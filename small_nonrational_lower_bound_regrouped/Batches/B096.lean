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
/- Source: ProjectionCertificates/R_m15e10q1_0303.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0303

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 789, 345, 625, 481, 897, 94, 142, 598, 902, 618, 170, 284, 428, 360, 81, 273, 529, 97, 161, 545, 321, 385, 641, 769, 14, 86, 134, 518, 42, 74, 138, 162, 546, 578, 642, 28, 140, 268, 276, 532, 388, 772, 88, 280, 104, 168, 296, 328, 592, 352, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_789, vertices_345, vertices_625, vertices_481, vertices_897, vertices_94, vertices_142, vertices_598, vertices_902, vertices_618, vertices_170, vertices_284, vertices_428, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_86, vertices_134, vertices_518, vertices_42, vertices_74, vertices_138, vertices_162, vertices_546, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_276, vertices_532, vertices_388, vertices_772, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_328, vertices_592, vertices_352, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_789), (false, vertices_345), (false, vertices_625), (false, vertices_481), (false, vertices_897), (true, vertices_14), (true, vertices_86), (true, vertices_134), (true, vertices_518), (true, vertices_42), (true, vertices_74), (true, vertices_138), (true, vertices_578), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_388), (true, vertices_104), (true, vertices_168), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 897 14 134 518 42 74 138 578 28 140 268 388 104 168 296 675 86 789 345 625 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 8 86 598 3
cert_coverFacet 3 902
cert_cover_5 3 2 0 1 6 7 134 902 3
cert_coverFacet 4 618
cert_cover_5 4 1 0 2 4 5 42 618 3
cert_coverFacet 5 170
cert_cover_2 5 2 0 4 6 42 170 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 428
cert_cover_5 7 3 1 2 4 6 140 428 2
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0303

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0304.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0304

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 307, 595, 357, 837, 241, 654, 394, 402, 658, 172, 812, 724, 228, 440, 19, 259, 515, 325, 49, 81, 97, 289, 577, 769, 138, 266, 522, 146, 274, 530, 386, 642, 44, 140, 524, 100, 164, 292, 196, 580, 644, 772, 168, 296, 392, 776, 176, 304, 208, 592, 400, 656, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_307, vertices_595, vertices_357, vertices_837, vertices_241, vertices_654, vertices_394, vertices_402, vertices_658, vertices_172, vertices_812, vertices_724, vertices_228, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_325, vertices_49, vertices_81, vertices_97, vertices_289, vertices_577, vertices_769, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_44, vertices_140, vertices_524, vertices_100, vertices_164, vertices_292, vertices_196, vertices_580, vertices_644, vertices_772, vertices_168, vertices_296, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_307), (false, vertices_595), (false, vertices_357), (false, vertices_837), (false, vertices_241), (true, vertices_138), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_164), (true, vertices_196), (true, vertices_644), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 1 3 5 6 8 724 196 1
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 6 7 440 168 1
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 812
cert_cover_5 5 2 1 2 4 7 44 812 3
cert_coverFacet 6 724
cert_cover_5 6 1 1 3 5 6 196 724 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 168 440 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0304

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0305.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0305

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 341, 805, 709, 457, 777, 118, 614, 58, 154, 810, 722, 316, 408, 464, 69, 261, 517, 137, 265, 521, 193, 321, 641, 769, 102, 26, 42, 138, 522, 50, 82, 146, 546, 578, 642, 52, 84, 276, 292, 548, 580, 56, 152, 280, 296, 392, 776, 208, 336, 400, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_341, vertices_805, vertices_709, vertices_457, vertices_777, vertices_118, vertices_614, vertices_58, vertices_154, vertices_810, vertices_722, vertices_316, vertices_408, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_102, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_546, vertices_578, vertices_642, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_580, vertices_56, vertices_152, vertices_280, vertices_296, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_341), (false, vertices_805), (false, vertices_709), (false, vertices_457), (false, vertices_777), (true, vertices_102), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_546), (true, vertices_578), (true, vertices_52), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 777 26 42 50 82 146 546 578 52 56 152 280 296 208 400 651 102 341 805 709 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 82 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 1 2 3 4 7 316 52 1
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 102 118 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 8 102 614 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 42 810 3
cert_coverFacet 5 722
cert_cover_5 5 0 0 3 5 6 82 722 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 52 316 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0305

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0306.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0306

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [147, 275, 803, 707, 229, 617, 433, 794, 658, 348, 108, 812, 468, 420, 728, 19, 131, 259, 515, 145, 273, 97, 161, 289, 545, 193, 577, 146, 274, 530, 642, 770, 44, 76, 268, 340, 100, 164, 292, 196, 388, 88, 280, 536, 104, 552, 584, 776, 208, 400, 656, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_147, vertices_275, vertices_803, vertices_707, vertices_229, vertices_617, vertices_433, vertices_794, vertices_658, vertices_348, vertices_108, vertices_812, vertices_468, vertices_420, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_340, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_88, vertices_280, vertices_536, vertices_104, vertices_552, vertices_584, vertices_776, vertices_208, vertices_400, vertices_656, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_147), (false, vertices_275), (false, vertices_803), (false, vertices_707), (false, vertices_229), (false, vertices_617), (false, vertices_433), (true, vertices_530), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_340), (true, vertices_292), (true, vertices_388), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_275) then 1 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_340) then 19 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 147 275 530 44 76 268 292 388 88 280 536 776 208 656 803 707 229 340 617 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 274 1
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_2 2 1 3 5 7 340
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 274 794 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 348
cert_cover_5 2 2 1 2 3 5 76 348 2
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 7 44 812 3
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 340 468 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0306

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0307.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0307

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 333, 713, 393, 689, 865, 286, 566, 838, 410, 178, 802, 92, 724, 216, 73, 137, 265, 161, 289, 545, 321, 577, 385, 641, 22, 262, 518, 282, 50, 146, 162, 290, 546, 386, 770, 28, 76, 268, 84, 532, 324, 580, 88, 152, 200, 392, 176, 560, 208, 656, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_333, vertices_713, vertices_393, vertices_689, vertices_865, vertices_286, vertices_566, vertices_838, vertices_410, vertices_178, vertices_802, vertices_92, vertices_724, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_22, vertices_262, vertices_518, vertices_282, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_268, vertices_84, vertices_532, vertices_324, vertices_580, vertices_88, vertices_152, vertices_200, vertices_392, vertices_176, vertices_560, vertices_208, vertices_656, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_333), (false, vertices_713), (false, vertices_393), (false, vertices_689), (false, vertices_865), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_282), (true, vertices_50), (true, vertices_146), (true, vertices_546), (true, vertices_770), (true, vertices_28), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_282) then 17 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 393 22 262 518 50 146 546 770 28 84 532 580 88 152 208 419 282 333 713 689 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 0 1 3 4 8 566 22 3
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 22 286 2
cert_coverFacet 1 566
cert_cover_5 1 1 0 1 3 4 22 566 3
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 262 838 2
cert_coverFacet 3 410
cert_cover_5 3 0 0 2 3 6 282 410 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 724
cert_cover_5 7 3 1 3 5 6 84 724 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0307

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0308.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0308

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 409, 361, 713, 833, 182, 534, 358, 838, 618, 674, 428, 404, 680, 73, 137, 265, 145, 273, 529, 321, 577, 641, 769, 22, 38, 326, 518, 146, 530, 98, 162, 546, 578, 642, 148, 276, 532, 164, 292, 388, 772, 104, 168, 296, 552, 584, 392, 648, 400, 352, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_409, vertices_361, vertices_713, vertices_833, vertices_182, vertices_534, vertices_358, vertices_838, vertices_618, vertices_674, vertices_428, vertices_404, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_38, vertices_326, vertices_518, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_388, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_584, vertices_392, vertices_648, vertices_400, vertices_352, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_409), (false, vertices_361), (false, vertices_713), (false, vertices_833), (true, vertices_22), (true, vertices_38), (true, vertices_326), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_148), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_168), (true, vertices_552), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_326) then 17 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 22 3
cert_row_4 1 0 2 4 5 8 618 98 1
cert_row_2 2 0 1 5 7 326
cert_row_4 3 1 2 4 6 7 428 164 1
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 22 182 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 358
cert_cover_5 2 2 0 1 4 5 38 358 3
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 8 326 838 3
cert_coverFacet 4 618
cert_cover_5 4 1 0 2 4 5 98 618 1
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 164 428 1
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0308

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0309.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0309

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 453, 617, 905, 369, 662, 626, 178, 418, 898, 604, 652, 436, 340, 197, 73, 137, 521, 97, 289, 545, 321, 385, 769, 50, 146, 530, 162, 290, 546, 386, 642, 770, 76, 140, 524, 84, 148, 276, 532, 324, 388, 644, 584, 648, 112, 176, 304, 336, 592, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_453, vertices_617, vertices_905, vertices_369, vertices_662, vertices_626, vertices_178, vertices_418, vertices_898, vertices_604, vertices_652, vertices_436, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_197, vertices_73, vertices_137, vertices_521, vertices_97, vertices_289, vertices_545, vertices_321, vertices_385, vertices_769, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_388, vertices_644, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_453), (false, vertices_617), (false, vertices_905), (false, vertices_369), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_176), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 50 1 146 2 530 162 386 642 524 84 148 276 532 644 176 592 416 803 205 453 617 905 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 76 2
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 626
cert_cover_5 1 1 0 3 4 5 50 626 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 604
cert_cover_5 5 0 1 2 3 5 76 604 2
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 148 436 2
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0309

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0310.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0310

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 205, 781, 453, 617, 817, 662, 714, 626, 178, 418, 450, 652, 436, 788, 13, 197, 261, 73, 521, 97, 289, 545, 321, 769, 50, 146, 530, 98, 162, 290, 194, 322, 578, 386, 642, 140, 524, 148, 276, 532, 388, 644, 772, 200, 584, 648, 176, 304, 560, 784, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_205, vertices_781, vertices_453, vertices_617, vertices_817, vertices_662, vertices_714, vertices_626, vertices_178, vertices_418, vertices_450, vertices_652, vertices_436, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_197, vertices_261, vertices_73, vertices_521, vertices_97, vertices_289, vertices_545, vertices_321, vertices_769, vertices_50, vertices_146, vertices_530, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_560, vertices_784, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_205), (false, vertices_781), (false, vertices_453), (false, vertices_617), (false, vertices_817), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_648), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 50 1 146 530 162 194 578 386 642 148 276 532 644 648 176 416 355 205 781 453 617 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 194 714 1
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 50 626 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 148 436 2
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0310

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0311.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0311

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 787, 611, 805, 361, 465, 662, 714, 620, 172, 652, 436, 788, 424, 456, 19, 67, 515, 209, 273, 97, 289, 545, 321, 769, 146, 530, 194, 578, 642, 44, 140, 524, 148, 276, 532, 164, 292, 548, 644, 772, 104, 168, 296, 200, 328, 584, 392, 648, 400, 784, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_787, vertices_611, vertices_805, vertices_361, vertices_465, vertices_662, vertices_714, vertices_620, vertices_172, vertices_652, vertices_436, vertices_788, vertices_424, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_515, vertices_209, vertices_273, vertices_97, vertices_289, vertices_545, vertices_321, vertices_769, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_400, vertices_784, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_787), (false, vertices_611), (false, vertices_805), (false, vertices_361), (false, vertices_465), (true, vertices_642), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 23 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 7 436 148 2
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 194 714 1
cert_coverFacet 2 620
cert_cover_5 2 3 1 2 4 5 44 620 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 436
cert_cover_5 5 0 1 3 4 6 148 436 2
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0311

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0312.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0312

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 589, 565, 357, 841, 433, 654, 154, 282, 778, 690, 236, 676, 472, 480, 37, 69, 517, 585, 49, 273, 529, 289, 321, 769, 26, 138, 266, 522, 146, 274, 530, 642, 770, 76, 140, 524, 100, 164, 548, 644, 152, 280, 200, 328, 776, 176, 560, 400, 224, 352, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_589, vertices_565, vertices_357, vertices_841, vertices_433, vertices_654, vertices_154, vertices_282, vertices_778, vertices_690, vertices_236, vertices_676, vertices_472, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_585, vertices_49, vertices_273, vertices_529, vertices_289, vertices_321, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_644, vertices_152, vertices_280, vertices_200, vertices_328, vertices_776, vertices_176, vertices_560, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_589), (false, vertices_565), (false, vertices_357), (false, vertices_841), (false, vertices_433), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_224), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 266 522 146 642 140 164 644 152 280 200 224 672 448 787 565 357 589 841 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 6 7 472 152 2
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 2 4 5 6 236 76 2
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 146 690 2
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 76 236 2
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 472
cert_cover_5 7 0 2 3 5 6 152 472 2
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0312

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0313.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0313

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 109, 357, 569, 841, 433, 714, 690, 210, 338, 834, 684, 204, 468, 420, 101, 41, 73, 521, 49, 273, 529, 289, 321, 769, 82, 146, 274, 530, 194, 322, 578, 642, 770, 44, 76, 140, 164, 292, 196, 324, 388, 552, 200, 584, 648, 176, 560, 208, 336, 400, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_109, vertices_357, vertices_569, vertices_841, vertices_433, vertices_714, vertices_690, vertices_210, vertices_338, vertices_834, vertices_684, vertices_204, vertices_468, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_101, vertices_41, vertices_73, vertices_521, vertices_49, vertices_273, vertices_529, vertices_289, vertices_321, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_552, vertices_200, vertices_584, vertices_648, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_109), (false, vertices_357), (false, vertices_569), (false, vertices_841), (false, vertices_433), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_196), (true, vertices_388), (true, vertices_200), (true, vertices_648), (true, vertices_208), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 82 1 146 2 194 322 578 642 140 164 196 388 200 648 208 336 672 787 109 357 569 841 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 7 468 196 1
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 1 0 2 5 6 194 714 1
cert_coverFacet 1 690
cert_cover_5 1 2 0 3 4 6 146 690 2
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 44 684 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 468
cert_cover_5 7 0 1 3 5 6 196 468 1
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0313

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0314.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0314

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 333, 773, 713, 913, 122, 346, 434, 738, 60, 284, 692, 788, 616, 13, 261, 517, 73, 521, 193, 321, 385, 641, 769, 90, 50, 274, 98, 162, 194, 322, 386, 28, 44, 268, 52, 276, 532, 548, 772, 56, 280, 104, 552, 328, 584, 176, 400, 656, 784, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_333, vertices_773, vertices_713, vertices_913, vertices_122, vertices_346, vertices_434, vertices_738, vertices_60, vertices_284, vertices_692, vertices_788, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_90, vertices_50, vertices_274, vertices_98, vertices_162, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_56, vertices_280, vertices_104, vertices_552, vertices_328, vertices_584, vertices_176, vertices_400, vertices_656, vertices_784, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_333), (false, vertices_773), (false, vertices_713), (false, vertices_913), (true, vertices_90), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_162), (true, vertices_28), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_176), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_913) then 24 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 773 50 274 98 162 28 52 276 532 56 280 104 176 608 672 451 90 557 333 713 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 3 4 6 7 434 50 3
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 122
cert_cover_5 0 0 0 2 3 4 90 122 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 7 90 346 3
cert_coverFacet 2 434
cert_cover_5 2 1 0 3 4 6 50 434 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 98 738 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0314

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0315.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0315

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 93, 301, 453, 617, 673, 705, 790, 806, 690, 466, 540, 556, 340, 728, 13, 69, 261, 41, 73, 161, 289, 545, 193, 577, 385, 641, 774, 146, 274, 530, 162, 290, 546, 386, 28, 44, 524, 84, 276, 532, 292, 548, 324, 88, 536, 552, 584, 208, 336, 656, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_93, vertices_301, vertices_453, vertices_617, vertices_673, vertices_705, vertices_790, vertices_806, vertices_690, vertices_466, vertices_540, vertices_556, vertices_340, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_41, vertices_73, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_774, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_44, vertices_524, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_88, vertices_536, vertices_552, vertices_584, vertices_208, vertices_336, vertices_656, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_93), (false, vertices_301), (false, vertices_453), (false, vertices_617), (false, vertices_673), (false, vertices_705), (true, vertices_774), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_536), (true, vertices_208), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 673 1 705 146 274 530 546 524 276 532 548 536 208 336 656 419 774 93 301 453 617
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 774 790 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 774 806 2
cert_coverFacet 2 690
cert_cover_5 2 1 0 3 4 6 146 690 2
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 146 466 2
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0315

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0316.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0316

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 805, 453, 713, 625, 353, 398, 310, 566, 602, 282, 650, 216, 408, 496, 133, 261, 517, 97, 289, 545, 193, 321, 577, 641, 54, 134, 262, 518, 26, 138, 266, 522, 274, 530, 642, 292, 548, 388, 88, 152, 280, 200, 584, 392, 648, 112, 304, 560, 208, 592, 400, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_805, vertices_453, vertices_713, vertices_625, vertices_353, vertices_398, vertices_310, vertices_566, vertices_602, vertices_282, vertices_650, vertices_216, vertices_408, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_54, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_642, vertices_292, vertices_548, vertices_388, vertices_88, vertices_152, vertices_280, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_805), (false, vertices_453), (false, vertices_713), (false, vertices_625), (false, vertices_353), (true, vertices_54), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_304), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_625) then 24 else
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
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 353 262 26 138 266 522 274 530 88 152 280 392 304 208 400 647 54 805 453 713 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 0 1 2 6 7 398 134 2
cert_row_2 2 0 1 3 4 54
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 2 0 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 310
cert_cover_5 1 2 0 1 3 7 54 310 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 8 54 566 3
cert_coverFacet 3 602
cert_cover_5 3 0 0 2 3 5 26 602 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 650
cert_cover_2 5 2 0 6 8 138 650 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0316

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0317.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0317

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 421, 197, 837, 681, 817, 94, 206, 570, 650, 850, 284, 396, 340, 440, 69, 133, 261, 161, 289, 545, 193, 577, 641, 769, 78, 26, 138, 522, 82, 530, 194, 578, 642, 28, 140, 268, 84, 276, 196, 324, 388, 56, 280, 168, 552, 392, 648, 304, 560, 336, 784, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_421, vertices_197, vertices_837, vertices_681, vertices_817, vertices_94, vertices_206, vertices_570, vertices_650, vertices_850, vertices_284, vertices_396, vertices_340, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_78, vertices_26, vertices_138, vertices_522, vertices_82, vertices_530, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_84, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_168, vertices_552, vertices_392, vertices_648, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_421), (false, vertices_197), (false, vertices_837), (false, vertices_681), (false, vertices_817), (true, vertices_78), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_392), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 197 26 138 522 82 530 28 140 268 84 276 56 280 392 336 707 78 421 837 681 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 206
cert_cover_5 1 0 0 1 2 6 78 206 3
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 82 850 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 56 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0317

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0318.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0318

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 565, 357, 581, 793, 433, 206, 590, 410, 778, 482, 684, 228, 664, 688, 37, 69, 517, 49, 273, 529, 289, 321, 577, 769, 78, 138, 266, 522, 194, 322, 578, 386, 770, 140, 524, 100, 164, 548, 196, 580, 152, 280, 536, 648, 776, 176, 560, 400, 656, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_565, vertices_357, vertices_581, vertices_793, vertices_433, vertices_206, vertices_590, vertices_410, vertices_778, vertices_482, vertices_684, vertices_228, vertices_664, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_49, vertices_273, vertices_529, vertices_289, vertices_321, vertices_577, vertices_769, vertices_78, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_152, vertices_280, vertices_536, vertices_648, vertices_776, vertices_176, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_565), (false, vertices_357), (false, vertices_581), (false, vertices_793), (false, vertices_433), (true, vertices_78), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_524), (true, vertices_164), (true, vertices_196), (true, vertices_152), (true, vertices_648), (true, vertices_656), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 581 138 266 522 194 386 140 524 164 196 152 648 656 224 672 835 78 565 357 793 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_2 2 0 1 2 5 78
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 2 0 1 2 8 78 590 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 6 138 410 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 194 482 1
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 140 684 2
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0318

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0319.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0319

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 613, 773, 905, 721, 481, 30, 270, 566, 122, 362, 668, 780, 472, 624, 37, 261, 517, 97, 289, 193, 577, 385, 641, 769, 14, 22, 38, 262, 26, 106, 266, 50, 290, 28, 268, 524, 532, 548, 772, 88, 152, 328, 392, 648, 776, 112, 560, 208, 592, 656, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_613, vertices_773, vertices_905, vertices_721, vertices_481, vertices_30, vertices_270, vertices_566, vertices_122, vertices_362, vertices_668, vertices_780, vertices_472, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_262, vertices_26, vertices_106, vertices_266, vertices_50, vertices_290, vertices_28, vertices_268, vertices_524, vertices_532, vertices_548, vertices_772, vertices_88, vertices_152, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_613), (false, vertices_773), (false, vertices_905), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_26), (true, vertices_106), (true, vertices_266), (true, vertices_50), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_88), (true, vertices_152), (true, vertices_328), (true, vertices_112), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 773 14 22 26 266 50 28 268 524 532 88 152 328 112 560 295 106 613 905 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 6 7 472 88 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 2 3 6 8 668 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 4 22 566 3
cert_coverFacet 3 122
cert_cover_5 3 1 0 2 3 4 26 122 3
cert_coverFacet 4 362
cert_cover_5 4 1 0 2 4 7 106 362 3
cert_coverFacet 5 668
cert_cover_5 5 3 1 2 3 6 28 668 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 472
cert_cover_5 7 0 2 3 5 6 88 472 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0319

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0320.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0320

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 301, 525, 565, 601, 409, 417, 218, 562, 594, 930, 962, 460, 588, 868, 13, 37, 517, 25, 265, 521, 49, 145, 529, 161, 289, 385, 50, 82, 146, 530, 162, 546, 194, 578, 898, 76, 268, 524, 292, 548, 324, 580, 88, 152, 200, 584, 392, 560, 592, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_301, vertices_525, vertices_565, vertices_601, vertices_409, vertices_417, vertices_218, vertices_562, vertices_594, vertices_930, vertices_962, vertices_460, vertices_588, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_25, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_385, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_898, vertices_76, vertices_268, vertices_524, vertices_292, vertices_548, vertices_324, vertices_580, vertices_88, vertices_152, vertices_200, vertices_584, vertices_392, vertices_560, vertices_592, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_301), (false, vertices_525), (false, vertices_565), (false, vertices_601), (false, vertices_409), (false, vertices_417), (true, vertices_82), (true, vertices_530), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_898), (true, vertices_76), (true, vertices_324), (true, vertices_580), (true, vertices_200), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_898) then 16 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 525 1 417 82 530 546 194 578 76 324 580 200 800 448 832 179 898 301 565 601 409
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 6 218 82 1
cert_row_2 1 0 6 7 8 898
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 0 0 2 3 5 82 218 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 930
cert_cover_5 3 1 0 4 6 7 162 930 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 76 460 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 292 868 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0320

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0321.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0321

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 397, 661, 837, 433, 801, 710, 122, 218, 658, 866, 364, 204, 312, 408, 133, 261, 517, 49, 145, 529, 289, 545, 385, 769, 90, 50, 146, 530, 98, 546, 194, 578, 642, 76, 140, 268, 196, 324, 580, 644, 56, 152, 280, 104, 296, 200, 392, 304, 400, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_397, vertices_661, vertices_837, vertices_433, vertices_801, vertices_710, vertices_122, vertices_218, vertices_658, vertices_866, vertices_364, vertices_204, vertices_312, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_90, vertices_50, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_76, vertices_140, vertices_268, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_392, vertices_304, vertices_400, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_397), (false, vertices_661), (false, vertices_837), (false, vertices_433), (false, vertices_801), (true, vertices_90), (true, vertices_146), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_76), (true, vertices_196), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 801 1 146 98 194 578 642 76 196 56 152 280 104 296 200 352 563 90 397 661 837 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 2 4 5 7 364 76 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 218
cert_cover_5 2 0 0 2 3 6 90 218 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 98 866 3
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 76 364 2
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0321

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0322.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0322

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 781, 309, 613, 241, 337, 654, 218, 346, 778, 738, 396, 420, 676, 440, 37, 261, 517, 49, 81, 273, 97, 321, 577, 769, 90, 138, 266, 522, 194, 322, 578, 642, 770, 140, 268, 524, 164, 292, 548, 388, 644, 152, 280, 392, 776, 176, 304, 208, 336, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_781, vertices_309, vertices_613, vertices_241, vertices_337, vertices_654, vertices_218, vertices_346, vertices_778, vertices_738, vertices_396, vertices_420, vertices_676, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_97, vertices_321, vertices_577, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_152, vertices_280, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_781), (false, vertices_309), (false, vertices_613), (false, vertices_241), (false, vertices_337), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 337 1 138 266 522 194 642 140 164 388 644 152 280 392 416 672 835 90 781 309 613 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_2 2 0 2 3 5 90
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 2 0 2 3 7 90 346 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 152 440 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0322

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0323.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0323

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 805, 709, 325, 457, 433, 542, 590, 186, 202, 818, 706, 348, 788, 408, 69, 261, 517, 161, 289, 545, 193, 321, 385, 641, 526, 26, 74, 138, 50, 530, 162, 546, 194, 578, 642, 28, 76, 276, 532, 324, 580, 772, 152, 280, 200, 328, 392, 176, 304, 400, 784, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_805, vertices_709, vertices_325, vertices_457, vertices_433, vertices_542, vertices_590, vertices_186, vertices_202, vertices_818, vertices_706, vertices_348, vertices_788, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_526, vertices_26, vertices_74, vertices_138, vertices_50, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_76, vertices_276, vertices_532, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_200, vertices_328, vertices_392, vertices_176, vertices_304, vertices_400, vertices_784, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_805), (false, vertices_709), (false, vertices_325), (false, vertices_457), (false, vertices_433), (true, vertices_526), (true, vertices_26), (true, vertices_74), (true, vertices_138), (true, vertices_50), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_276), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_526) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 325 26 74 138 50 530 194 578 28 76 276 532 152 280 784 675 526 805 709 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 26 3
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_2 2 0 1 2 8 526
cert_row_4 3 1 2 3 5 7 348 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 526 542 3
cert_coverFacet 1 590
cert_cover_5 1 2 0 1 2 5 526 590 3
cert_coverFacet 2 186
cert_cover_5 2 0 0 2 3 4 26 186 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 818
cert_cover_5 4 1 0 3 4 7 50 818 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 28 348 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0323

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0324.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0324

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 837, 169, 809, 457, 721, 30, 302, 598, 806, 186, 658, 284, 468, 408, 41, 137, 265, 161, 545, 193, 321, 577, 641, 769, 14, 22, 294, 518, 26, 42, 146, 530, 162, 546, 642, 28, 268, 84, 276, 324, 580, 772, 152, 280, 168, 296, 392, 208, 592, 400, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_837, vertices_169, vertices_809, vertices_457, vertices_721, vertices_30, vertices_302, vertices_598, vertices_806, vertices_186, vertices_658, vertices_284, vertices_468, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_294, vertices_518, vertices_26, vertices_42, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_268, vertices_84, vertices_276, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_208, vertices_592, vertices_400, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_837), (false, vertices_169), (false, vertices_809), (false, vertices_457), (false, vertices_721), (true, vertices_14), (true, vertices_22), (true, vertices_294), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 169 14 22 518 26 42 146 530 28 268 84 276 152 280 400 675 294 837 809 457 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_4 1 0 2 3 4 6 186 26 3
cert_row_2 2 0 1 4 7 294
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 302
cert_cover_5 1 2 0 1 2 4 14 302 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 22 598 3
cert_coverFacet 3 806
cert_cover_5 3 2 0 1 4 8 294 806 3
cert_coverFacet 4 186
cert_cover_5 4 1 0 2 3 4 26 186 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 84 468 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0324

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0325.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0325

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 213, 405, 313, 617, 457, 561, 310, 86, 710, 774, 810, 562, 908, 712, 149, 41, 73, 265, 49, 81, 273, 529, 545, 193, 577, 385, 22, 70, 262, 518, 50, 82, 530, 290, 546, 578, 770, 84, 276, 196, 388, 644, 772, 296, 552, 200, 584, 392, 648, 776, 304, 560, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_213, vertices_405, vertices_313, vertices_617, vertices_457, vertices_561, vertices_310, vertices_86, vertices_710, vertices_774, vertices_810, vertices_562, vertices_908, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_41, vertices_73, vertices_265, vertices_49, vertices_81, vertices_273, vertices_529, vertices_545, vertices_193, vertices_577, vertices_385, vertices_22, vertices_70, vertices_262, vertices_518, vertices_50, vertices_82, vertices_530, vertices_290, vertices_546, vertices_578, vertices_770, vertices_84, vertices_276, vertices_196, vertices_388, vertices_644, vertices_772, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_213), (false, vertices_405), (false, vertices_313), (false, vertices_617), (false, vertices_457), (false, vertices_561), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_644), (true, vertices_772), (true, vertices_648), (true, vertices_776), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 561 2 22 1 70 262 518 50 290 546 770 644 772 648 776 704 595 213 405 313 617 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 6 7 8 908 388 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 70 710 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 290 810 1
cert_coverFacet 5 562
cert_cover_2 5 3 0 4 8 50 562 3
cert_coverFacet 6 908
cert_cover_5 6 3 1 2 6 7 388 908 1
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0325

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0326.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0326

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 535, 613, 421, 233, 721, 398, 806, 154, 282, 850, 376, 216, 424, 864, 23, 37, 133, 517, 145, 529, 97, 161, 193, 577, 134, 262, 518, 26, 138, 266, 146, 274, 530, 770, 292, 548, 388, 88, 152, 280, 104, 168, 296, 200, 392, 208, 336, 592, 352, 608, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_535, vertices_613, vertices_421, vertices_233, vertices_721, vertices_398, vertices_806, vertices_154, vertices_282, vertices_850, vertices_376, vertices_216, vertices_424, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_133, vertices_517, vertices_145, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_770, vertices_292, vertices_548, vertices_388, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_208, vertices_336, vertices_592, vertices_352, vertices_608, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_535), (false, vertices_613), (false, vertices_421), (false, vertices_233), (false, vertices_721), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_770), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_336), (true, vertices_352), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 262 26 138 266 274 770 88 152 280 296 392 336 352 800 832 151 535 613 421 233 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 262 806 2
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 274 850 2
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 88 376 2
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0326

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0327.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0327

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 309, 613, 453, 185, 401, 673, 838, 218, 346, 682, 778, 812, 312, 464, 37, 69, 261, 49, 145, 273, 161, 545, 193, 577, 385, 641, 90, 138, 266, 522, 194, 322, 578, 642, 770, 292, 548, 324, 580, 772, 56, 152, 280, 168, 296, 552, 776, 304, 208, 336, 400, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_309, vertices_613, vertices_453, vertices_185, vertices_401, vertices_673, vertices_838, vertices_218, vertices_346, vertices_682, vertices_778, vertices_812, vertices_312, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_776, vertices_304, vertices_208, vertices_336, vertices_400, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_309), (false, vertices_613), (false, vertices_453), (false, vertices_185), (false, vertices_401), (false, vertices_673), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_770), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_185) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 401 1 673 138 266 522 322 770 772 280 296 552 776 208 336 707 90 309 613 453 185
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 2 4 7 8 812 292 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 138 682 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 292 812 1
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0327

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0328.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0328

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 181, 645, 361, 713, 417, 214, 598, 842, 434, 786, 820, 708, 808, 37, 133, 517, 41, 73, 521, 161, 289, 193, 321, 385, 641, 86, 146, 274, 530, 194, 322, 578, 386, 770, 52, 148, 532, 548, 196, 580, 644, 296, 552, 328, 584, 776, 176, 304, 784, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_181, vertices_645, vertices_361, vertices_713, vertices_417, vertices_214, vertices_598, vertices_842, vertices_434, vertices_786, vertices_820, vertices_708, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_86, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_148, vertices_532, vertices_548, vertices_196, vertices_580, vertices_644, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_784, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_181), (false, vertices_645), (false, vertices_361), (false, vertices_713), (false, vertices_417), (true, vertices_86), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_776), (true, vertices_304), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_86) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 645 1 417 146 274 530 578 770 532 196 580 776 304 784 800 451 86 557 181 361 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_2 1 0 1 3 5 86
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 8 86 598 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 322 842 1
cert_coverFacet 3 434
cert_cover_5 3 2 0 3 4 6 146 434 2
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 820
cert_cover_5 5 3 1 3 4 7 52 820 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0328

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0329.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0329

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 779, 707, 117, 805, 737, 682, 394, 466, 60, 412, 556, 780, 340, 248, 67, 259, 515, 37, 69, 261, 97, 545, 705, 769, 138, 266, 522, 194, 322, 386, 642, 28, 44, 268, 524, 52, 84, 276, 548, 324, 772, 56, 152, 168, 552, 392, 776, 112, 208, 336, 400, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_779, vertices_707, vertices_117, vertices_805, vertices_737, vertices_682, vertices_394, vertices_466, vertices_60, vertices_412, vertices_556, vertices_780, vertices_340, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_261, vertices_97, vertices_545, vertices_705, vertices_769, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_168, vertices_552, vertices_392, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_779), (false, vertices_707), (false, vertices_117), (false, vertices_805), (false, vertices_737), (true, vertices_138), (true, vertices_386), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_208), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 23 24 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_707) then 25 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 138 2
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_4 2 1 2 3 6 7 412 28 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 138 682 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 466
cert_cover_5 2 1 0 3 5 6 194 466 1
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 412
cert_cover_5 4 2 1 2 3 6 28 412 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0329

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0330.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0330

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 275, 803, 557, 425, 649, 465, 590, 342, 774, 594, 236, 484, 804, 728, 19, 259, 515, 41, 137, 521, 145, 273, 289, 545, 385, 641, 70, 262, 518, 82, 274, 530, 578, 770, 44, 76, 524, 228, 292, 548, 324, 772, 168, 200, 584, 648, 208, 336, 592, 656, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_275, vertices_803, vertices_557, vertices_425, vertices_649, vertices_465, vertices_590, vertices_342, vertices_774, vertices_594, vertices_236, vertices_484, vertices_804, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_41, vertices_137, vertices_521, vertices_145, vertices_273, vertices_289, vertices_545, vertices_385, vertices_641, vertices_70, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_44, vertices_76, vertices_524, vertices_228, vertices_292, vertices_548, vertices_324, vertices_772, vertices_168, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_275), (false, vertices_803), (false, vertices_557), (false, vertices_425), (false, vertices_649), (false, vertices_465), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_578), (true, vertices_76), (true, vertices_228), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_200), (true, vertices_584), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_228) then 19 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 275 649 70 262 518 82 578 76 292 324 772 200 584 592 659 803 557 228 425 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 1 3 5 7 342 70 2
cert_row_4 2 0 1 2 5 8 590 70 2
cert_row_4 3 2 3 5 6 8 728 200 1
cert_rows
cert_pivot_2 4 7 0 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 70 590 2
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 70 342 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 5 44 236 3
cert_coverFacet 5 484
cert_cover_5 5 0 1 4 5 7 228 484 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 200 728 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0330

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0331.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0331

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 341, 409, 777, 721, 865, 182, 598, 614, 170, 810, 658, 428, 404, 356, 137, 265, 521, 81, 145, 273, 321, 577, 641, 769, 22, 38, 582, 42, 138, 522, 146, 530, 162, 546, 642, 84, 148, 276, 100, 164, 292, 324, 388, 168, 296, 392, 776, 592, 400, 656, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_341, vertices_409, vertices_777, vertices_721, vertices_865, vertices_182, vertices_598, vertices_614, vertices_170, vertices_810, vertices_658, vertices_428, vertices_404, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_38, vertices_582, vertices_42, vertices_138, vertices_522, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_324, vertices_388, vertices_168, vertices_296, vertices_392, vertices_776, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_341), (false, vertices_409), (false, vertices_777), (false, vertices_721), (false, vertices_865), (true, vertices_22), (true, vertices_38), (true, vertices_582), (true, vertices_42), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_148), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_168), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_582) then 17 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 777 22 38 42 146 530 162 546 148 100 164 292 388 168 296 651 582 341 409 721 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 0 1 3 4 6 182 22 3
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 1 2 4 6 7 428 164 1
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 22 182 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 5 22 598 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 38 614 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 42 810 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 164 428 1
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0331

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0332.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0332

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 61, 345, 681, 201, 625, 206, 334, 390, 850, 930, 284, 172, 436, 816, 25, 41, 73, 137, 49, 81, 545, 193, 577, 641, 78, 134, 262, 194, 322, 578, 386, 642, 770, 28, 44, 140, 268, 52, 276, 164, 388, 280, 168, 200, 328, 304, 560, 336, 592, 784, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_61, vertices_345, vertices_681, vertices_201, vertices_625, vertices_206, vertices_334, vertices_390, vertices_850, vertices_930, vertices_284, vertices_172, vertices_436, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_137, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_78, vertices_134, vertices_262, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_276, vertices_164, vertices_388, vertices_280, vertices_168, vertices_200, vertices_328, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_61), (false, vertices_345), (false, vertices_681), (false, vertices_201), (false, vertices_625), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_164), (true, vertices_388), (true, vertices_304), (true, vertices_784), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_61) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 201 134 262 322 386 770 140 268 276 164 388 304 784 416 800 707 78 61 345 681 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_4 2 0 4 6 7 8 930 386 1
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 322 850 1
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 386 930 1
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 52 436 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0332

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2913 : Certifies 2913 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0303.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2914 : Certifies 2914 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0304.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2915 : Certifies 2915 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0305.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2916 : Certifies 2916 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0306.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2917 : Certifies 2917 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0307.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2918 : Certifies 2918 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0308.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2919 : Certifies 2919 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0309.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2920 : Certifies 2920 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0310.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2921 : Certifies 2921 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0311.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2922 : Certifies 2922 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0312.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2923 : Certifies 2923 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0313.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2924 : Certifies 2924 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0314.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2925 : Certifies 2925 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0315.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2926 : Certifies 2926 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0316.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2927 : Certifies 2927 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0317.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2928 : Certifies 2928 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0318.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2929 : Certifies 2929 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0319.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2930 : Certifies 2930 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0320.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2931 : Certifies 2931 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0321.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2932 : Certifies 2932 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0322.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2933 : Certifies 2933 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0323.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2934 : Certifies 2934 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0324.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2935 : Certifies 2935 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0325.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2936 : Certifies 2936 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0326.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2937 : Certifies 2937 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0327.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2938 : Certifies 2938 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0328.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2939 : Certifies 2939 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0329.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2940 : Certifies 2940 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0330.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2941 : Certifies 2941 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0331.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2942 : Certifies 2942 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0332.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B096 (j : Fin 30) :
    Certifies (2913 + j.val) := by
  fin_cases j
  · exact projection_2913
  · exact projection_2914
  · exact projection_2915
  · exact projection_2916
  · exact projection_2917
  · exact projection_2918
  · exact projection_2919
  · exact projection_2920
  · exact projection_2921
  · exact projection_2922
  · exact projection_2923
  · exact projection_2924
  · exact projection_2925
  · exact projection_2926
  · exact projection_2927
  · exact projection_2928
  · exact projection_2929
  · exact projection_2930
  · exact projection_2931
  · exact projection_2932
  · exact projection_2933
  · exact projection_2934
  · exact projection_2935
  · exact projection_2936
  · exact projection_2937
  · exact projection_2938
  · exact projection_2939
  · exact projection_2940
  · exact projection_2941
  · exact projection_2942

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
