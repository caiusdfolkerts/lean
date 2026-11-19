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
/- Source: ProjectionCertificates/R_m16e10q1_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 781, 341, 149, 677, 721, 558, 122, 346, 778, 738, 172, 396, 404, 440, 240, 21, 133, 261, 517, 81, 145, 321, 577, 641, 769, 90, 42, 266, 522, 98, 546, 322, 578, 770, 44, 140, 268, 524, 148, 276, 164, 548, 388, 56, 280, 168, 392, 776, 112, 176, 208, 336, 400, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_781, vertices_341, vertices_149, vertices_677, vertices_721, vertices_558, vertices_122, vertices_346, vertices_778, vertices_738, vertices_172, vertices_396, vertices_404, vertices_440, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_769, vertices_90, vertices_42, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_164, vertices_548, vertices_388, vertices_56, vertices_280, vertices_168, vertices_392, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_781), (false, vertices_341), (false, vertices_149), (false, vertices_677), (false, vertices_721), (true, vertices_90), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_44), (true, vertices_140), (true, vertices_388), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_112), (true, vertices_176), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_90) then 19 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 149 42 266 522 98 546 44 140 388 56 280 168 392 112 176 400 224 835 90 781 341 677 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_2 2 0 2 3 5 90
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 90 122 3
cert_coverFacet 2 346
cert_cover_5 2 2 0 2 3 7 90 346 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 98 738 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 56 440 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0009

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 57, 345, 617, 433, 206, 590, 422, 774, 466, 652, 692, 568, 216, 664, 25, 41, 73, 49, 273, 289, 545, 321, 577, 769, 78, 134, 262, 518, 194, 322, 578, 386, 770, 140, 524, 164, 292, 548, 644, 772, 56, 88, 152, 536, 552, 200, 584, 648, 176, 560, 208, 336, 400, 656, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_57, vertices_345, vertices_617, vertices_433, vertices_206, vertices_590, vertices_422, vertices_774, vertices_466, vertices_652, vertices_692, vertices_568, vertices_216, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_78, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_524, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_552, vertices_200, vertices_584, vertices_648, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_57), (false, vertices_345), (false, vertices_617), (false, vertices_433), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_524), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_560), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_78) then 19 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 57 134 262 518 194 386 140 524 164 644 152 536 200 648 560 208 656 835 78 805 345 617 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_4 2 0 1 4 6 7 422 134 2
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 422
cert_cover_5 2 2 0 1 4 6 134 422 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 194 466 1
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 164 692 1
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0010

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 789, 421, 709, 217, 537, 401, 782, 678, 294, 314, 106, 738, 120, 792, 496, 133, 261, 517, 25, 73, 521, 145, 273, 529, 193, 577, 385, 38, 262, 518, 42, 74, 266, 522, 98, 674, 290, 578, 164, 292, 644, 772, 56, 88, 280, 536, 104, 776, 112, 304, 208, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_789, vertices_421, vertices_709, vertices_217, vertices_537, vertices_401, vertices_782, vertices_678, vertices_294, vertices_314, vertices_106, vertices_738, vertices_120, vertices_792, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_38, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_674, vertices_290, vertices_578, vertices_164, vertices_292, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_789), (false, vertices_421), (false, vertices_709), (false, vertices_217), (false, vertices_537), (false, vertices_401), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_98), (true, vertices_674), (true, vertices_290), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
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
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 537 1 401 38 262 518 42 266 98 290 56 280 104 776 112 304 224 587 674 789 421 709 217
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 0 4 6 8 674
cert_row_4 2 0 2 3 4 7 314 42 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 38 678 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 314
cert_cover_5 3 2 0 2 3 4 42 314 2
cert_coverFacet 4 106
cert_cover_2 4 2 0 4 5 42 106 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 98 738 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0011

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 227, 643, 301, 617, 905, 417, 214, 794, 402, 898, 572, 284, 628, 404, 484, 67, 131, 515, 41, 265, 521, 97, 161, 289, 577, 385, 641, 82, 146, 274, 530, 194, 386, 642, 770, 28, 44, 268, 564, 84, 148, 276, 100, 292, 196, 388, 280, 536, 552, 776, 592, 400, 224, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_227, vertices_643, vertices_301, vertices_617, vertices_905, vertices_417, vertices_214, vertices_794, vertices_402, vertices_898, vertices_572, vertices_284, vertices_628, vertices_404, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_41, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_564, vertices_84, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_388, vertices_280, vertices_536, vertices_552, vertices_776, vertices_592, vertices_400, vertices_224, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_227), (false, vertices_643), (false, vertices_301), (false, vertices_617), (false, vertices_905), (false, vertices_417), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_564), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_196), (true, vertices_388), (true, vertices_280), (true, vertices_536), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_227) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_564) then 21 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_536) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_564), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 274 1
cert_row_2 1 1 3 4 8 564
cert_row_4 2 0 1 3 5 6 214 82 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 82 214 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 274 794 1
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 572
cert_cover_5 4 1 1 2 3 4 28 572 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 628
cert_cover_5 6 1 1 3 4 5 564 628 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 100 484 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0012

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 653, 453, 345, 585, 566, 602, 242, 930, 60, 540, 804, 900, 312, 496, 13, 133, 261, 73, 265, 521, 193, 321, 577, 641, 50, 82, 530, 162, 546, 194, 578, 642, 28, 44, 524, 52, 532, 292, 548, 388, 644, 772, 56, 88, 280, 536, 296, 584, 240, 304, 336, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_653, vertices_453, vertices_345, vertices_585, vertices_566, vertices_602, vertices_242, vertices_930, vertices_60, vertices_540, vertices_804, vertices_900, vertices_312, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_50, vertices_82, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_524, vertices_52, vertices_532, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_584, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_653), (false, vertices_453), (false, vertices_345), (false, vertices_585), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_28), (true, vertices_52), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_56), (true, vertices_536), (true, vertices_240), (true, vertices_304), (true, vertices_416), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_240) then 26 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_800) then 15 else
  if p.val = (true, vertices_896) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 0 2 3 5 8 602 82 1
cert_row_2 2 3 4 5 6 240
cert_row_4 3 0 4 6 7 8 930 162 3
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 82 602 1
cert_coverFacet 2 242
cert_cover_5 2 2 0 3 4 5 50 242 3
cert_coverFacet 3 930
cert_cover_5 3 3 0 4 6 7 162 930 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 496
cert_cover_5 9 2 3 4 5 7 240 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0013

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0014.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0014

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 613, 453, 241, 417, 286, 122, 618, 778, 434, 156, 652, 404, 708, 728, 69, 261, 517, 97, 161, 289, 545, 193, 385, 769, 26, 106, 266, 522, 50, 274, 290, 546, 770, 28, 140, 268, 524, 148, 276, 196, 580, 388, 644, 88, 152, 584, 648, 776, 112, 176, 208, 400, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_613, vertices_453, vertices_241, vertices_417, vertices_286, vertices_122, vertices_618, vertices_778, vertices_434, vertices_156, vertices_652, vertices_404, vertices_708, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_26, vertices_106, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_196, vertices_580, vertices_388, vertices_644, vertices_88, vertices_152, vertices_584, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_613), (false, vertices_453), (false, vertices_241), (false, vertices_417), (true, vertices_26), (true, vertices_106), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_28), (true, vertices_140), (true, vertices_148), (true, vertices_276), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_584), (true, vertices_648), (true, vertices_400), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_106) then 19 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 417 26 266 522 50 274 28 140 148 276 644 88 152 584 648 400 704 803 106 781 613 453 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 0 3 4 6 7 434 50 3
cert_row_2 2 0 2 4 5 106
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 26 122 3
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 8 106 618 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 434
cert_cover_5 4 1 0 3 4 6 50 434 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 708
cert_cover_2 8 5 1 6 8 196 708 3
cert_coverFacet 9 728
cert_cover_5 9 3 2 3 5 6 88 728 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0014

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 313, 217, 329, 625, 214, 598, 422, 774, 458, 684, 660, 568, 664, 424, 25, 73, 265, 49, 81, 289, 545, 321, 577, 769, 86, 134, 262, 518, 194, 322, 578, 386, 770, 148, 532, 164, 292, 548, 644, 772, 56, 152, 536, 168, 296, 552, 200, 328, 392, 648, 560, 208, 592, 656, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_313, vertices_217, vertices_329, vertices_625, vertices_214, vertices_598, vertices_422, vertices_774, vertices_458, vertices_684, vertices_660, vertices_568, vertices_664, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_49, vertices_81, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_648, vertices_560, vertices_208, vertices_592, vertices_656, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_313), (false, vertices_217), (false, vertices_329), (false, vertices_625), (true, vertices_86), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_194), (true, vertices_386), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_86) then 19 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 329 134 262 518 194 386 148 532 164 644 536 168 552 392 648 656 416 835 86 805 313 217 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 1 4 6 7 422 134 2
cert_row_4 3 1 2 4 6 8 684 164 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 422
cert_cover_5 2 2 0 1 4 6 134 422 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 458
cert_cover_5 4 1 0 2 5 6 194 458 1
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 164 684 1
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0015

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 307, 563, 707, 665, 465, 590, 806, 188, 540, 300, 332, 564, 488, 712, 432, 51, 67, 259, 515, 145, 273, 529, 193, 321, 641, 70, 262, 518, 290, 546, 578, 28, 44, 76, 268, 524, 52, 532, 292, 548, 324, 152, 536, 168, 296, 200, 328, 584, 648, 176, 304, 560, 400, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_307, vertices_563, vertices_707, vertices_665, vertices_465, vertices_590, vertices_806, vertices_188, vertices_540, vertices_300, vertices_332, vertices_564, vertices_488, vertices_712, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_67, vertices_259, vertices_515, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_70, vertices_262, vertices_518, vertices_290, vertices_546, vertices_578, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_532, vertices_292, vertices_548, vertices_324, vertices_152, vertices_536, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_560, vertices_400, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_307), (false, vertices_563), (false, vertices_707), (false, vertices_665), (false, vertices_465), (true, vertices_518), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 18 else
  if p.val = (false, vertices_307) then 20 else
  if p.val = (false, vertices_563) then 21 else
  if p.val = (false, vertices_707) then 22 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 6 188 28 3
cert_row_4 1 2 4 5 6 7 488 168 2
cert_row_4 2 0 1 2 5 8 590 70 2
cert_row_4 3 0 1 4 7 8 806 262 2
cert_rows
cert_pivot_2 3 6 2 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 70 590 2
cert_coverFacet 1 806
cert_cover_5 1 3 0 1 4 7 262 806 2
cert_coverFacet 2 188
cert_cover_5 2 0 1 2 3 4 28 188 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 488
cert_cover_5 7 1 2 4 5 6 168 488 2
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0016

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 787, 675, 195, 569, 433, 449, 206, 646, 774, 684, 588, 852, 376, 600, 488, 67, 131, 259, 515, 49, 273, 529, 161, 545, 193, 321, 385, 70, 134, 262, 518, 194, 642, 770, 76, 140, 524, 324, 580, 644, 772, 56, 88, 536, 360, 168, 552, 200, 584, 304, 336, 592, 784, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_787, vertices_675, vertices_195, vertices_569, vertices_433, vertices_449, vertices_206, vertices_646, vertices_774, vertices_684, vertices_588, vertices_852, vertices_376, vertices_600, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_70, vertices_134, vertices_262, vertices_518, vertices_194, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_360, vertices_168, vertices_552, vertices_200, vertices_584, vertices_304, vertices_336, vertices_592, vertices_784, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_787), (false, vertices_675), (false, vertices_195), (false, vertices_569), (false, vertices_433), (false, vertices_449), (true, vertices_134), (true, vertices_518), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_580), (true, vertices_644), (true, vertices_772), (true, vertices_88), (true, vertices_360), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 17 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_360) then 23 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 70 2
cert_row_4 1 1 2 4 6 8 684 140 2
cert_row_2 2 2 4 5 7 360
cert_row_4 3 1 3 5 7 8 852 324 1
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 70 206 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 140 684 2
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 852
cert_cover_5 5 3 1 3 5 7 324 852 1
cert_coverFacet 6 376
cert_cover_5 6 2 2 3 4 5 56 376 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 488
cert_cover_5 8 2 2 4 5 6 360 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0017

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 213, 405, 613, 481, 286, 186, 650, 778, 306, 738, 604, 216, 712, 432, 149, 69, 261, 517, 97, 289, 545, 193, 385, 769, 26, 138, 266, 522, 50, 274, 162, 290, 546, 642, 770, 28, 268, 524, 84, 276, 580, 88, 152, 200, 584, 648, 776, 176, 304, 208, 400, 224, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_213, vertices_405, vertices_613, vertices_481, vertices_286, vertices_186, vertices_650, vertices_778, vertices_306, vertices_738, vertices_604, vertices_216, vertices_712, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_580, vertices_88, vertices_152, vertices_200, vertices_584, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_213), (false, vertices_405), (false, vertices_613), (false, vertices_481), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_162), (true, vertices_642), (true, vertices_28), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_176), (true, vertices_304), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 19 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_213) then 22 else
  if p.val = (false, vertices_405) then 23 else
  if p.val = (false, vertices_613) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 1 2 3 5 8 604 28 3
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 0 4 5 6 8 738 162 2
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 186
cert_cover_5 1 2 0 2 3 4 26 186 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 738
cert_cover_5 5 3 0 4 5 6 162 738 2
cert_coverFacet 6 604
cert_cover_5 6 1 1 2 3 5 28 604 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0018

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 115, 563, 451, 557, 229, 389, 346, 786, 172, 652, 916, 632, 408, 664, 488, 51, 67, 259, 515, 37, 133, 261, 517, 97, 545, 193, 385, 82, 274, 530, 322, 770, 44, 140, 524, 164, 388, 644, 772, 88, 152, 280, 536, 104, 168, 552, 328, 392, 648, 112, 560, 400, 656, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_115, vertices_563, vertices_451, vertices_557, vertices_229, vertices_389, vertices_346, vertices_786, vertices_172, vertices_652, vertices_916, vertices_632, vertices_408, vertices_664, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_67, vertices_259, vertices_515, vertices_37, vertices_133, vertices_261, vertices_517, vertices_97, vertices_545, vertices_193, vertices_385, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_44, vertices_140, vertices_524, vertices_164, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_552, vertices_328, vertices_392, vertices_648, vertices_112, vertices_560, vertices_400, vertices_656, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_115), (false, vertices_563), (false, vertices_451), (false, vertices_557), (false, vertices_229), (false, vertices_389), (true, vertices_274), (true, vertices_140), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_400), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 16 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_115) then 21 else
  if p.val = (false, vertices_563) then 22 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 82 1
cert_row_4 1 1 3 6 7 8 916 388 1
cert_row_4 2 2 3 4 5 8 632 88 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 0 0 2 3 5 82 346 1
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 388 916 1
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 88 632 2
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0019

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 227, 643, 333, 617, 905, 449, 406, 794, 178, 898, 604, 284, 628, 180, 484, 35, 131, 515, 73, 265, 521, 97, 545, 193, 321, 385, 641, 50, 146, 274, 530, 162, 386, 642, 770, 28, 76, 268, 52, 596, 148, 276, 100, 164, 324, 388, 280, 536, 584, 776, 176, 560, 224, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_227, vertices_643, vertices_333, vertices_617, vertices_905, vertices_449, vertices_406, vertices_794, vertices_178, vertices_898, vertices_604, vertices_284, vertices_628, vertices_180, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_52, vertices_596, vertices_148, vertices_276, vertices_100, vertices_164, vertices_324, vertices_388, vertices_280, vertices_536, vertices_584, vertices_776, vertices_176, vertices_560, vertices_224, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_227), (false, vertices_643), (false, vertices_333), (false, vertices_617), (false, vertices_905), (false, vertices_449), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_52), (true, vertices_596), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_388), (true, vertices_280), (true, vertices_536), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_227) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_596) then 21 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_536) then 14 else
  if p.val = (true, vertices_176) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 274 1
cert_row_2 1 1 3 5 8 596
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 274 794 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 604
cert_cover_5 4 1 1 2 3 5 28 604 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 628
cert_cover_5 6 1 1 3 4 5 52 628 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 100 484 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0020

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0021.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0021

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 789, 357, 709, 217, 537, 337, 782, 614, 294, 186, 298, 738, 312, 792, 496, 69, 261, 517, 25, 137, 521, 81, 273, 529, 193, 321, 641, 38, 262, 518, 42, 138, 266, 522, 610, 162, 290, 642, 100, 292, 580, 772, 56, 152, 280, 536, 296, 776, 176, 304, 208, 336, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_789, vertices_357, vertices_709, vertices_217, vertices_537, vertices_337, vertices_782, vertices_614, vertices_294, vertices_186, vertices_298, vertices_738, vertices_312, vertices_792, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_38, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_610, vertices_162, vertices_290, vertices_642, vertices_100, vertices_292, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_789), (false, vertices_357), (false, vertices_709), (false, vertices_217), (false, vertices_537), (false, vertices_337), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_610), (true, vertices_162), (true, vertices_290), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_610) then 18 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 537 1 337 38 262 518 42 266 162 290 56 280 296 776 176 304 224 651 610 789 357 709 217
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 0 4 5 8 610
cert_row_4 2 0 2 3 4 6 186 42 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 5 38 614 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 186
cert_cover_5 3 2 0 2 3 4 42 186 2
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 610 738 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0021

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 541, 77, 117, 457, 777, 721, 310, 426, 626, 786, 738, 236, 300, 780, 788, 13, 21, 69, 73, 265, 521, 81, 529, 193, 385, 641, 769, 50, 274, 530, 610, 162, 290, 386, 642, 770, 44, 76, 268, 524, 52, 276, 532, 100, 292, 772, 168, 296, 200, 392, 776, 112, 592, 784, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_541, vertices_77, vertices_117, vertices_457, vertices_777, vertices_721, vertices_310, vertices_426, vertices_626, vertices_786, vertices_738, vertices_236, vertices_300, vertices_780, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_73, vertices_265, vertices_521, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_50, vertices_274, vertices_530, vertices_610, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_772, vertices_168, vertices_296, vertices_200, vertices_392, vertices_776, vertices_112, vertices_592, vertices_784, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_541), (false, vertices_77), (false, vertices_117), (false, vertices_457), (false, vertices_777), (false, vertices_721), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_610), (true, vertices_162), (true, vertices_290), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_296), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_610) then 18 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 77 0 777 50 274 530 162 290 44 268 276 292 772 168 296 784 224 899 610 541 117 457 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 8 610
cert_row_4 1 0 1 3 4 7 310 50 1
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 8 3 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 50 310 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 162 426 1
cert_coverFacet 2 626
cert_cover_5 2 0 0 3 4 5 50 626 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 738
cert_cover_5 4 0 0 4 5 6 610 738 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 44 236 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0022

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 405, 805, 709, 457, 777, 662, 58, 538, 362, 242, 706, 572, 308, 808, 496, 133, 261, 517, 73, 265, 521, 193, 577, 385, 769, 26, 42, 74, 522, 50, 146, 530, 98, 194, 578, 642, 52, 148, 276, 532, 292, 548, 644, 56, 536, 296, 552, 328, 776, 240, 304, 400, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_405, vertices_805, vertices_709, vertices_457, vertices_777, vertices_662, vertices_58, vertices_538, vertices_362, vertices_242, vertices_706, vertices_572, vertices_308, vertices_808, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_769, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_146, vertices_530, vertices_98, vertices_194, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_328, vertices_776, vertices_240, vertices_304, vertices_400, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_405), (false, vertices_805), (false, vertices_709), (false, vertices_457), (false, vertices_777), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_194), (true, vertices_642), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_296), (true, vertices_552), (true, vertices_240), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_240) then 26 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 2 3 4 8 572 52 1
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 42 362 3
cert_coverFacet 4 242
cert_cover_5 4 1 0 3 4 5 50 242 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 52 572 1
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coverFacet 9 496
cert_cover_5 9 1 3 4 5 7 240 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0023

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 557, 421, 197, 581, 313, 905, 214, 842, 434, 338, 898, 628, 180, 632, 344, 37, 69, 133, 517, 41, 265, 521, 289, 193, 577, 385, 641, 82, 146, 274, 194, 322, 578, 386, 642, 770, 52, 84, 148, 164, 548, 196, 580, 56, 88, 280, 552, 328, 584, 776, 624, 176, 304, 336, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_557, vertices_421, vertices_197, vertices_581, vertices_313, vertices_905, vertices_214, vertices_842, vertices_434, vertices_338, vertices_898, vertices_628, vertices_180, vertices_632, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_584, vertices_776, vertices_624, vertices_176, vertices_304, vertices_336, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_557), (false, vertices_421), (false, vertices_197), (false, vertices_581), (false, vertices_313), (false, vertices_905), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_88), (true, vertices_328), (true, vertices_584), (true, vertices_624), (true, vertices_176), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_624) then 25 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 82 1
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_2 2 3 4 5 8 624
cert_row_4 3 0 3 4 6 7 434 146 2
cert_rows
cert_pivot_2 1 2 5 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 82 214 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 434
cert_cover_5 2 3 0 3 4 6 146 434 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 52 628 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 632
cert_cover_5 7 2 2 3 4 5 56 632 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0024

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0025.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 275, 707, 771, 677, 241, 817, 590, 282, 810, 300, 556, 460, 436, 708, 472, 19, 67, 259, 515, 49, 81, 273, 161, 545, 193, 641, 769, 26, 74, 266, 522, 274, 578, 770, 44, 76, 268, 524, 164, 292, 548, 196, 580, 388, 644, 88, 280, 296, 552, 456, 176, 304, 208, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_275, vertices_707, vertices_771, vertices_677, vertices_241, vertices_817, vertices_590, vertices_282, vertices_810, vertices_300, vertices_556, vertices_460, vertices_436, vertices_708, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_49, vertices_81, vertices_273, vertices_161, vertices_545, vertices_193, vertices_641, vertices_769, vertices_26, vertices_74, vertices_266, vertices_522, vertices_274, vertices_578, vertices_770, vertices_44, vertices_76, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_296, vertices_552, vertices_456, vertices_176, vertices_304, vertices_208, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_275), (false, vertices_707), (false, vertices_771), (false, vertices_677), (false, vertices_241), (false, vertices_817), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_456), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_456) then 22 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 7 436 164 1
cert_row_2 1 2 5 6 7 456
cert_row_4 2 0 1 2 5 8 590 74 1
cert_row_4 3 0 2 4 7 8 810 266 2
cert_rows
cert_pivot_2 3 6 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 74 590 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 810
cert_cover_5 2 3 0 2 4 7 266 810 2
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 6 76 460 3
cert_coverFacet 6 436
cert_cover_5 6 0 1 3 4 6 164 436 1
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0025

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0026.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0026

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 613, 645, 905, 481, 286, 122, 618, 778, 434, 604, 396, 652, 404, 240, 69, 133, 517, 97, 289, 545, 193, 385, 641, 769, 26, 106, 266, 522, 50, 274, 290, 546, 770, 28, 140, 268, 524, 84, 148, 276, 580, 388, 644, 88, 584, 392, 648, 776, 112, 176, 208, 400, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_613, vertices_645, vertices_905, vertices_481, vertices_286, vertices_122, vertices_618, vertices_778, vertices_434, vertices_604, vertices_396, vertices_652, vertices_404, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_106, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_580, vertices_388, vertices_644, vertices_88, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_613), (false, vertices_645), (false, vertices_905), (false, vertices_481), (true, vertices_26), (true, vertices_106), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_388), (true, vertices_88), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_106) then 19 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 2 3 7 286 26 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 26 286 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 26 122 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 8 106 618 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 50 434 3
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 28 604 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0026

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0027.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0027

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 789, 421, 709, 89, 537, 465, 782, 678, 294, 122, 298, 738, 440, 792, 240, 133, 261, 517, 25, 73, 521, 81, 273, 529, 193, 577, 385, 38, 262, 518, 42, 74, 266, 522, 98, 674, 290, 578, 164, 292, 644, 772, 56, 88, 280, 536, 296, 776, 112, 176, 208, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_789, vertices_421, vertices_709, vertices_89, vertices_537, vertices_465, vertices_782, vertices_678, vertices_294, vertices_122, vertices_298, vertices_738, vertices_440, vertices_792, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_73, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_38, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_674, vertices_290, vertices_578, vertices_164, vertices_292, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_789), (false, vertices_421), (false, vertices_709), (false, vertices_89), (false, vertices_537), (false, vertices_465), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_98), (true, vertices_674), (true, vertices_290), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_112), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_674) then 18 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 89 1 537 38 262 518 42 266 98 290 56 280 296 776 112 176 224 587 674 789 421 709 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 0 4 6 8 674
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 38 678 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 42 122 2
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 98 738 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 56 440 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0027

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 397, 677, 793, 713, 566, 358, 122, 466, 786, 484, 568, 216, 408, 616, 736, 133, 261, 517, 137, 265, 521, 641, 769, 38, 262, 518, 50, 82, 274, 530, 98, 322, 770, 356, 164, 548, 388, 56, 88, 152, 280, 536, 104, 552, 200, 584, 392, 560, 208, 400, 784, 224, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_397, vertices_677, vertices_793, vertices_713, vertices_566, vertices_358, vertices_122, vertices_466, vertices_786, vertices_484, vertices_568, vertices_216, vertices_408, vertices_616, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_322, vertices_770, vertices_356, vertices_164, vertices_548, vertices_388, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_200, vertices_584, vertices_392, vertices_560, vertices_208, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_397), (false, vertices_677), (false, vertices_793), (false, vertices_713), (true, vertices_38), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_356), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_552), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 24 27 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 19 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_793) then 25 else
  if p.val = (false, vertices_713) then 26 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_356) then 23 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_608) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 27 => Sum.inl 3
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 38 2
cert_row_2 1 1 4 5 7 356
cert_row_4 2 0 2 3 4 5 122 50 1
cert_row_4 3 0 3 5 6 7 466 82 3
cert_rows
cert_pivot_2 8 1 2 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 38 566 2
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 38 358 3
cert_coverFacet 2 122
cert_cover_5 2 2 0 2 3 4 50 122 1
cert_coverFacet 3 466
cert_cover_5 3 3 0 3 5 6 82 466 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 356 484 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coverFacet 10 736
cert_cover_2 10 5 4 6 8 224 736 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0029

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 181, 805, 645, 313, 153, 457, 614, 714, 370, 802, 450, 604, 668, 116, 344, 37, 133, 517, 25, 137, 265, 49, 145, 289, 385, 641, 769, 98, 290, 546, 194, 322, 578, 386, 642, 770, 540, 52, 84, 148, 100, 548, 580, 644, 88, 152, 280, 200, 328, 584, 648, 112, 304, 336, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_181, vertices_805, vertices_645, vertices_313, vertices_153, vertices_457, vertices_614, vertices_714, vertices_370, vertices_802, vertices_450, vertices_604, vertices_668, vertices_116, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_25, vertices_137, vertices_265, vertices_49, vertices_145, vertices_289, vertices_385, vertices_641, vertices_769, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_540, vertices_52, vertices_84, vertices_148, vertices_100, vertices_548, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_648, vertices_112, vertices_304, vertices_336, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_181), (false, vertices_805), (false, vertices_645), (false, vertices_313), (false, vertices_153), (false, vertices_457), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_540), (true, vertices_84), (true, vertices_100), (true, vertices_580), (true, vertices_88), (true, vertices_584), (true, vertices_648), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_540) then 21 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_2 1 1 2 3 8 540
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 0 3 4 5 7 370 98 1
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 194 714 1
cert_coverFacet 2 370
cert_cover_5 2 3 0 3 4 5 98 370 1
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 604
cert_cover_5 5 1 1 2 3 5 540 604 3
cert_coverFacet 6 668
cert_cover_5 6 1 1 2 3 6 540 668 3
cert_coverFacet 7 116
cert_cover_2 7 3 1 4 5 52 116 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0030

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 595, 163, 643, 709, 425, 465, 678, 810, 786, 348, 796, 236, 556, 596, 456, 19, 35, 131, 515, 81, 273, 161, 289, 193, 577, 385, 641, 274, 530, 162, 290, 546, 642, 770, 284, 44, 76, 524, 84, 532, 164, 548, 196, 580, 644, 168, 296, 552, 200, 328, 392, 776, 336, 592, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_595, vertices_163, vertices_643, vertices_709, vertices_425, vertices_465, vertices_678, vertices_810, vertices_786, vertices_348, vertices_796, vertices_236, vertices_556, vertices_596, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_284, vertices_44, vertices_76, vertices_524, vertices_84, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_336, vertices_592, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_595), (false, vertices_163), (false, vertices_643), (false, vertices_709), (false, vertices_425), (false, vertices_465), (true, vertices_546), (true, vertices_770), (true, vertices_284), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_552), (true, vertices_200), (true, vertices_328), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_284) then 21 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 163 1 643 546 770 44 76 524 84 532 164 548 552 200 328 776 784 307 595 709 284 425 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 1 4 6 8 678 162 1
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 162 678 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 348
cert_cover_5 3 0 1 2 3 5 284 348 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 8 284 796 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 44 236 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0033

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 171, 291, 835, 357, 649, 737, 790, 282, 298, 412, 428, 244, 596, 836, 728, 11, 35, 259, 515, 137, 521, 97, 161, 289, 321, 577, 641, 26, 42, 266, 274, 530, 290, 770, 396, 84, 148, 276, 532, 100, 164, 292, 324, 580, 772, 152, 280, 536, 168, 296, 648, 208, 592, 224, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_171, vertices_291, vertices_835, vertices_357, vertices_649, vertices_737, vertices_790, vertices_282, vertices_298, vertices_412, vertices_428, vertices_244, vertices_596, vertices_836, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_26, vertices_42, vertices_266, vertices_274, vertices_530, vertices_290, vertices_770, vertices_396, vertices_84, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_648, vertices_208, vertices_592, vertices_224, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_171), (false, vertices_291), (false, vertices_835), (false, vertices_357), (false, vertices_649), (false, vertices_737), (true, vertices_266), (true, vertices_274), (true, vertices_396), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_580), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_171) then 18 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_396) then 22 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 1 2 6 7 396
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 412
cert_cover_5 3 1 1 2 3 6 396 412 2
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 396 428 2
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 84 244 2
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 152 728 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0034

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 557, 709, 601, 297, 457, 417, 150, 790, 806, 346, 210, 482, 660, 824, 720, 37, 133, 517, 41, 73, 265, 521, 161, 289, 193, 577, 385, 22, 38, 134, 774, 82, 146, 274, 162, 290, 194, 322, 148, 532, 548, 644, 88, 280, 536, 296, 552, 328, 208, 592, 656, 784, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_557, vertices_709, vertices_601, vertices_297, vertices_457, vertices_417, vertices_150, vertices_790, vertices_806, vertices_346, vertices_210, vertices_482, vertices_660, vertices_824, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_22, vertices_38, vertices_134, vertices_774, vertices_82, vertices_146, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_148, vertices_532, vertices_548, vertices_644, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_208, vertices_592, vertices_656, vertices_784, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_557), (false, vertices_709), (false, vertices_601), (false, vertices_297), (false, vertices_457), (false, vertices_417), (true, vertices_22), (true, vertices_774), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_148), (true, vertices_532), (true, vertices_280), (true, vertices_208), (true, vertices_656), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_774) then 18 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 297 1 417 22 82 146 274 290 194 322 148 532 280 208 656 784 800 167 774 557 709 601 457
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_4 2 0 2 3 5 7 346 82 1
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 38 806 3
cert_coverFacet 3 346
cert_cover_5 3 2 0 2 3 5 82 346 1
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 162 482 2
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 280 824 2
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0035

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 789, 421, 313, 561, 737, 334, 526, 454, 122, 538, 722, 780, 792, 488, 624, 133, 261, 517, 49, 273, 529, 161, 289, 545, 641, 14, 326, 134, 518, 26, 74, 522, 82, 530, 194, 642, 268, 524, 388, 772, 56, 280, 536, 104, 296, 328, 776, 112, 560, 592, 784, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_789, vertices_421, vertices_313, vertices_561, vertices_737, vertices_334, vertices_526, vertices_454, vertices_122, vertices_538, vertices_722, vertices_780, vertices_792, vertices_488, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_14, vertices_326, vertices_134, vertices_518, vertices_26, vertices_74, vertices_522, vertices_82, vertices_530, vertices_194, vertices_642, vertices_268, vertices_524, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_776, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_789), (false, vertices_421), (false, vertices_313), (false, vertices_561), (false, vertices_737), (true, vertices_14), (true, vertices_326), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_268), (true, vertices_524), (true, vertices_536), (true, vertices_104), (true, vertices_328), (true, vertices_776), (true, vertices_112), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_313) then 24 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_326) then 19 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 7 326
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 6 326 454 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 26 122 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 6 82 722 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coverFacet 9 624
cert_cover_2 9 4 3 5 8 112 624 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0036

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 213, 421, 581, 737, 94, 58, 298, 842, 690, 722, 284, 588, 404, 440, 69, 133, 261, 517, 161, 289, 545, 193, 577, 769, 26, 42, 74, 266, 50, 82, 658, 290, 546, 578, 770, 28, 76, 268, 524, 84, 148, 276, 580, 388, 56, 280, 296, 584, 776, 176, 208, 400, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_213, vertices_421, vertices_581, vertices_737, vertices_94, vertices_58, vertices_298, vertices_842, vertices_690, vertices_722, vertices_284, vertices_588, vertices_404, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_26, vertices_42, vertices_74, vertices_266, vertices_50, vertices_82, vertices_658, vertices_290, vertices_546, vertices_578, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_580, vertices_388, vertices_56, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_400, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_213), (false, vertices_421), (false, vertices_581), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_50), (true, vertices_82), (true, vertices_658), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_584), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_213) then 22 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_658) then 19 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 5 94 26 1
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_2 2 0 3 6 8 658
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 26 94 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 74 842 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 50 690 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 82 722 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coverFacet 9 440
cert_cover_5 9 3 2 3 4 6 56 440 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0037

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 563, 451, 771, 597, 241, 833, 398, 554, 778, 124, 284, 236, 788, 964, 824, 35, 131, 259, 515, 49, 81, 529, 161, 193, 321, 577, 769, 42, 138, 266, 522, 546, 386, 770, 28, 108, 140, 268, 84, 276, 532, 196, 580, 388, 772, 56, 280, 168, 552, 776, 112, 560, 784, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_563, vertices_451, vertices_771, vertices_597, vertices_241, vertices_833, vertices_398, vertices_554, vertices_778, vertices_124, vertices_284, vertices_236, vertices_788, vertices_964, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_161, vertices_193, vertices_321, vertices_577, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_546, vertices_386, vertices_770, vertices_28, vertices_108, vertices_140, vertices_268, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_280, vertices_168, vertices_552, vertices_776, vertices_112, vertices_560, vertices_784, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_563), (false, vertices_451), (false, vertices_771), (false, vertices_597), (false, vertices_241), (false, vertices_833), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_108), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_772), (true, vertices_56), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_108) then 22 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_2 2 1 2 4 5 108
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 28 124 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 236
cert_cover_5 5 2 1 2 4 6 108 236 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 964
cert_cover_5 7 1 1 5 6 7 196 964 3
cert_coverFacet 8 824
cert_cover_5 8 3 2 3 4 7 56 824 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0038

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 787, 355, 341, 593, 737, 398, 782, 170, 418, 220, 540, 788, 484, 696, 720, 35, 259, 515, 81, 273, 529, 97, 545, 321, 577, 270, 42, 138, 522, 162, 290, 386, 770, 28, 140, 524, 84, 276, 532, 196, 324, 388, 772, 152, 536, 168, 552, 208, 592, 656, 784, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_787, vertices_355, vertices_341, vertices_593, vertices_737, vertices_398, vertices_782, vertices_170, vertices_418, vertices_220, vertices_540, vertices_788, vertices_484, vertices_696, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_270, vertices_42, vertices_138, vertices_522, vertices_162, vertices_290, vertices_386, vertices_770, vertices_28, vertices_140, vertices_524, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_787), (false, vertices_355), (false, vertices_341), (false, vertices_593), (false, vertices_737), (true, vertices_270), (true, vertices_138), (true, vertices_162), (true, vertices_386), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_532), (true, vertices_196), (true, vertices_388), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_208), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 17 24 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 21 else
  if p.val = (false, vertices_787) then 22 else
  if p.val = (false, vertices_355) then 23 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_270) then 19 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 1 4 5 6 7 484 196 1
cert_row_4 2 1 2 3 5 6 220 28 3
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 270 398 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 8 270 782 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 220
cert_cover_5 4 2 1 2 3 5 28 220 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 484
cert_cover_5 7 1 1 4 5 6 196 484 1
cert_coverFacet 8 696
cert_cover_5 8 3 2 3 4 6 152 696 2
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0039

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 595, 227, 387, 301, 617, 417, 214, 658, 898, 572, 284, 628, 404, 484, 920, 67, 131, 259, 515, 41, 265, 521, 97, 161, 289, 577, 385, 82, 146, 530, 194, 386, 642, 770, 28, 44, 268, 564, 84, 148, 276, 100, 292, 196, 388, 280, 536, 552, 776, 592, 400, 656, 224, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_595, vertices_227, vertices_387, vertices_301, vertices_617, vertices_417, vertices_214, vertices_658, vertices_898, vertices_572, vertices_284, vertices_628, vertices_404, vertices_484, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_82, vertices_146, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_564, vertices_84, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_388, vertices_280, vertices_536, vertices_552, vertices_776, vertices_592, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_595), (false, vertices_227), (false, vertices_387), (false, vertices_301), (false, vertices_617), (false, vertices_417), (true, vertices_146), (true, vertices_642), (true, vertices_28), (true, vertices_564), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_196), (true, vertices_388), (true, vertices_280), (true, vertices_536), (true, vertices_400), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_301) then 21 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_564) then 22 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 387 417 146 642 28 84 148 276 100 196 388 280 536 400 656 896 779 595 227 301 564 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 82 1
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_2 2 1 3 4 8 564
cert_row_4 3 2 3 6 7 8 920 280 2
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 82 214 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 4 28 572 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 564 628 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 484
cert_cover_5 7 1 1 4 5 6 100 484 3
cert_coverFacet 8 920
cert_cover_5 8 3 2 3 6 7 280 920 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0040

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 557, 357, 453, 121, 713, 406, 774, 314, 538, 778, 722, 804, 600, 808, 496, 37, 325, 133, 517, 41, 73, 521, 97, 193, 641, 134, 262, 518, 26, 266, 522, 146, 274, 530, 642, 770, 292, 548, 388, 772, 56, 88, 536, 296, 552, 584, 776, 112, 304, 208, 592, 400, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_557, vertices_357, vertices_453, vertices_121, vertices_713, vertices_406, vertices_774, vertices_314, vertices_538, vertices_778, vertices_722, vertices_804, vertices_600, vertices_808, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_325, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_97, vertices_193, vertices_641, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_292, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_536, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_557), (false, vertices_357), (false, vertices_453), (false, vertices_121), (false, vertices_713), (true, vertices_262), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_772), (true, vertices_536), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_121) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_4 1 0 2 3 4 7 314 26 3
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 134 406 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 314
cert_cover_5 2 1 0 2 3 4 26 314 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 146 722 2
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0041

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3903 : Certifies 3903 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3904 : Certifies 3904 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3905 : Certifies 3905 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3906 : Certifies 3906 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3907 : Certifies 3907 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3908 : Certifies 3908 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0014.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3909 : Certifies 3909 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3910 : Certifies 3910 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3911 : Certifies 3911 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3912 : Certifies 3912 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3913 : Certifies 3913 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3914 : Certifies 3914 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3915 : Certifies 3915 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0021.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3916 : Certifies 3916 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3917 : Certifies 3917 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3918 : Certifies 3918 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3919 : Certifies 3919 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0025.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3920 : Certifies 3920 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0026.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3921 : Certifies 3921 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0027.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3922 : Certifies 3922 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3923 : Certifies 3923 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3924 : Certifies 3924 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3925 : Certifies 3925 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3926 : Certifies 3926 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3927 : Certifies 3927 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3928 : Certifies 3928 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3929 : Certifies 3929 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3930 : Certifies 3930 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3931 : Certifies 3931 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3932 : Certifies 3932 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B129 (j : Fin 30) :
    Certifies (3903 + j.val) := by
  fin_cases j
  · exact projection_3903
  · exact projection_3904
  · exact projection_3905
  · exact projection_3906
  · exact projection_3907
  · exact projection_3908
  · exact projection_3909
  · exact projection_3910
  · exact projection_3911
  · exact projection_3912
  · exact projection_3913
  · exact projection_3914
  · exact projection_3915
  · exact projection_3916
  · exact projection_3917
  · exact projection_3918
  · exact projection_3919
  · exact projection_3920
  · exact projection_3921
  · exact projection_3922
  · exact projection_3923
  · exact projection_3924
  · exact projection_3925
  · exact projection_3926
  · exact projection_3927
  · exact projection_3928
  · exact projection_3929
  · exact projection_3930
  · exact projection_3931
  · exact projection_3932

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
