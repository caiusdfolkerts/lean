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
/- Source: ProjectionCertificates/R_m14e10q1_0090.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 141, 269, 661, 837, 217, 361, 678, 122, 186, 658, 866, 172, 812, 13, 133, 261, 517, 73, 137, 265, 81, 145, 529, 321, 577, 58, 82, 146, 530, 98, 162, 546, 578, 642, 44, 140, 268, 164, 548, 644, 772, 88, 152, 104, 168, 296, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_141, vertices_269, vertices_661, vertices_837, vertices_217, vertices_361, vertices_678, vertices_122, vertices_186, vertices_658, vertices_866, vertices_172, vertices_812] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_81, vertices_145, vertices_529, vertices_321, vertices_577, vertices_58, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_44, vertices_140, vertices_268, vertices_164, vertices_548, vertices_644, vertices_772, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_141), (false, vertices_269), (false, vertices_661), (false, vertices_837), (false, vertices_217), (false, vertices_361), (true, vertices_58), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_164), (true, vertices_548), (true, vertices_168), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 141 1 269 146 98 162 546 642 44 164 548 168 800 595 58 661 837 217 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 2 4 7 8 812 44 3
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
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 44 812 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0090

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0094.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0094

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 267, 451, 709, 665, 281, 433, 806, 838, 570, 298, 692, 484, 312, 11, 67, 259, 25, 265, 521, 145, 273, 193, 577, 385, 641, 774, 42, 266, 522, 290, 546, 322, 578, 164, 292, 548, 196, 324, 580, 644, 56, 280, 536, 296, 176, 304, 560, 656, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_267, vertices_451, vertices_709, vertices_665, vertices_281, vertices_433, vertices_806, vertices_838, vertices_570, vertices_298, vertices_692, vertices_484, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_25, vertices_265, vertices_521, vertices_145, vertices_273, vertices_193, vertices_577, vertices_385, vertices_641, vertices_774, vertices_42, vertices_266, vertices_522, vertices_290, vertices_546, vertices_322, vertices_578, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_176, vertices_304, vertices_560, vertices_656, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_267), (false, vertices_451), (false, vertices_709), (false, vertices_665), (false, vertices_281), (false, vertices_433), (true, vertices_774), (true, vertices_42), (true, vertices_290), (true, vertices_546), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_56), (true, vertices_296), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_560) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 42 2
cert_row_2 1 0 1 7 8 774
cert_row_4 2 1 3 4 6 8 692 164 1
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 774 806 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 774 838 2
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 42 570 2
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 164 692 1
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 164 484 2
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0094

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0095.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0095

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 275, 707, 387, 453, 617, 369, 406, 658, 796, 364, 716, 660, 824, 19, 131, 259, 515, 49, 273, 97, 545, 193, 321, 577, 385, 146, 274, 530, 386, 642, 76, 268, 524, 148, 276, 532, 196, 324, 388, 644, 792, 104, 296, 552, 584, 304, 560, 656, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_275, vertices_707, vertices_387, vertices_453, vertices_617, vertices_369, vertices_406, vertices_658, vertices_796, vertices_364, vertices_716, vertices_660, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_792, vertices_104, vertices_296, vertices_552, vertices_584, vertices_304, vertices_560, vertices_656, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_275), (false, vertices_707), (false, vertices_387), (false, vertices_453), (false, vertices_617), (false, vertices_369), (true, vertices_146), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_792), (true, vertices_296), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 13 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_792) then 19 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_2 1 2 3 7 8 792
cert_row_4 2 1 2 4 5 7 364 76 2
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 0 3 4 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 268 796 2
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 76 364 2
cert_coverFacet 4 716
cert_cover_5 4 3 1 2 5 6 76 716 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 824
cert_cover_5 6 1 2 3 4 7 792 824 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0095

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0099.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0099

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 587, 451, 709, 681, 433, 790, 838, 282, 538, 692, 468, 312, 568, 11, 67, 259, 41, 521, 161, 289, 193, 577, 385, 641, 774, 26, 266, 522, 274, 530, 322, 578, 148, 276, 532, 196, 324, 580, 644, 56, 280, 536, 296, 552, 176, 304, 560, 400, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_587, vertices_451, vertices_709, vertices_681, vertices_433, vertices_790, vertices_838, vertices_282, vertices_538, vertices_692, vertices_468, vertices_312, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_41, vertices_521, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_774, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_322, vertices_578, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_176, vertices_304, vertices_560, vertices_400, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_587), (false, vertices_451), (false, vertices_709), (false, vertices_681), (false, vertices_433), (true, vertices_774), (true, vertices_26), (true, vertices_274), (true, vertices_530), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_709) then 12 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_774) then 13 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_560) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 3 4 6 8 692 148 2
cert_row_4 2 1 3 5 6 7 468 148 2
cert_rows_3
cert_pivot_3 4 0 1
cert_heightProof 3
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 774 790 2
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 774 838 2
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 148 692 2
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 148 468 2
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0099

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0100.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0100

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 267, 899, 709, 233, 297, 433, 314, 538, 786, 572, 620, 244, 916, 11, 259, 515, 41, 73, 265, 161, 289, 193, 577, 385, 641, 26, 266, 522, 274, 530, 770, 556, 52, 148, 532, 100, 196, 580, 644, 56, 536, 104, 296, 584, 176, 304, 400, 784, 224, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_267, vertices_899, vertices_709, vertices_233, vertices_297, vertices_433, vertices_314, vertices_538, vertices_786, vertices_572, vertices_620, vertices_244, vertices_916] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_41, vertices_73, vertices_265, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_556, vertices_52, vertices_148, vertices_532, vertices_100, vertices_196, vertices_580, vertices_644, vertices_56, vertices_536, vertices_104, vertices_296, vertices_584, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_267), (false, vertices_899), (false, vertices_709), (false, vertices_233), (false, vertices_297), (false, vertices_433), (true, vertices_26), (true, vertices_274), (true, vertices_530), (true, vertices_556), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_56), (true, vertices_536), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_556) then 17 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_556), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_2 1 1 2 4 8 556
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 0 2 4 1
cert_heightProof 4
cert_coverFacet 0 314
cert_cover_5 0 0 0 2 3 4 26 314 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 556 572 2
cert_coverFacet 4 620
cert_cover_5 4 1 1 2 4 5 556 620 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 52 244 3
cert_coverFacet 6 916
cert_cover_5 6 3 1 3 6 7 148 916 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0100

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0102.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0102

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 395, 179, 421, 361, 625, 590, 654, 594, 658, 332, 396, 692, 868, 11, 19, 131, 73, 265, 49, 81, 97, 161, 289, 385, 526, 74, 138, 82, 146, 530, 578, 642, 76, 140, 268, 164, 292, 548, 324, 580, 388, 644, 328, 392, 176, 560, 592, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_395, vertices_179, vertices_421, vertices_361, vertices_625, vertices_590, vertices_654, vertices_594, vertices_658, vertices_332, vertices_396, vertices_692, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_131, vertices_73, vertices_265, vertices_49, vertices_81, vertices_97, vertices_161, vertices_289, vertices_385, vertices_526, vertices_74, vertices_138, vertices_82, vertices_146, vertices_530, vertices_578, vertices_642, vertices_76, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_328, vertices_392, vertices_176, vertices_560, vertices_592, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_395), (false, vertices_179), (false, vertices_421), (false, vertices_361), (false, vertices_625), (true, vertices_526), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_421) then 12 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_526) then 13 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_656) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_526), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 8 526
cert_row_4 1 1 3 4 6 8 692 164 1
cert_row_4 2 1 4 5 7 8 868 292 2
cert_rows_3
cert_pivot_3 3 0 1
cert_heightProof 3
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 526 590 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 6 526 654 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 692
cert_cover_5 6 1 1 3 4 6 164 692 1
cert_coverFacet 7 868
cert_cover_5 7 2 1 4 5 7 292 868 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0102

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0105.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0105

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 331, 787, 99, 109, 525, 905, 242, 562, 466, 460, 652, 740, 944, 35, 67, 259, 515, 13, 37, 517, 73, 265, 521, 97, 769, 50, 210, 274, 530, 98, 546, 322, 76, 140, 524, 100, 548, 196, 644, 328, 392, 648, 176, 560, 400, 784, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_331, vertices_787, vertices_99, vertices_109, vertices_525, vertices_905, vertices_242, vertices_562, vertices_466, vertices_460, vertices_652, vertices_740, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_13, vertices_37, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_769, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_76, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_644, vertices_328, vertices_392, vertices_648, vertices_176, vertices_560, vertices_400, vertices_784, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_331), (false, vertices_787), (false, vertices_99), (false, vertices_109), (false, vertices_525), (false, vertices_905), (true, vertices_50), (true, vertices_210), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_176), (true, vertices_560), (true, vertices_400), (true, vertices_224), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_109) then 14 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_210) then 18 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 1 2 5 6 7 460 76 3
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 0 0 3 4 5 50 242 3
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 7 210 466 3
cert_coverFacet 3 460
cert_cover_5 3 1 1 2 5 6 76 460 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 100 740 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0105

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0106.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0106

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 43, 419, 901, 569, 785, 737, 342, 602, 618, 354, 724, 788, 484, 11, 35, 259, 25, 41, 273, 529, 161, 545, 385, 641, 769, 26, 42, 586, 82, 274, 98, 290, 322, 84, 276, 532, 196, 324, 388, 644, 772, 536, 552, 592, 784, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_43, vertices_419, vertices_901, vertices_569, vertices_785, vertices_737, vertices_342, vertices_602, vertices_618, vertices_354, vertices_724, vertices_788, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_25, vertices_41, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_586, vertices_82, vertices_274, vertices_98, vertices_290, vertices_322, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_536, vertices_552, vertices_592, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_43), (false, vertices_419), (false, vertices_901), (false, vertices_569), (false, vertices_785), (false, vertices_737), (true, vertices_586), (true, vertices_82), (true, vertices_98), (true, vertices_322), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 13 else
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_586) then 15 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_586), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 8 586
cert_row_4 1 0 1 3 5 7 342 82 1
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 82 342 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 5 42 618 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 196 484 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0106

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0108.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0108

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 91, 523, 403, 589, 117, 181, 282, 778, 930, 740, 632, 440, 808, 11, 19, 131, 515, 53, 69, 133, 517, 73, 521, 81, 145, 26, 266, 522, 274, 386, 642, 770, 100, 164, 580, 644, 56, 88, 280, 296, 552, 584, 776, 112, 176, 400, 608, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_91, vertices_523, vertices_403, vertices_589, vertices_117, vertices_181, vertices_282, vertices_778, vertices_930, vertices_740, vertices_632, vertices_440, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_131, vertices_515, vertices_53, vertices_69, vertices_133, vertices_517, vertices_73, vertices_521, vertices_81, vertices_145, vertices_26, vertices_266, vertices_522, vertices_274, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_176, vertices_400, vertices_608, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_91), (false, vertices_523), (false, vertices_403), (false, vertices_589), (false, vertices_117), (false, vertices_181), (true, vertices_266), (true, vertices_770), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 8 930 386 1
cert_row_4 1 1 4 5 6 8 740 100 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 1 5 2
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 930
cert_cover_5 2 0 0 4 6 7 386 930 1
cert_coverFacet 3 740
cert_cover_5 3 1 1 4 5 6 100 740 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 56 440 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0108

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0110.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0110

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 117, 293, 837, 905, 737, 310, 122, 410, 234, 92, 284, 716, 780, 37, 69, 261, 97, 161, 289, 577, 385, 641, 769, 26, 106, 138, 50, 274, 162, 290, 386, 28, 76, 268, 524, 52, 84, 276, 292, 580, 772, 88, 280, 200, 392, 648, 776, 112, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_117, vertices_293, vertices_837, vertices_905, vertices_737, vertices_310, vertices_122, vertices_410, vertices_234, vertices_92, vertices_284, vertices_716, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_106, vertices_138, vertices_50, vertices_274, vertices_162, vertices_290, vertices_386, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_580, vertices_772, vertices_88, vertices_280, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_117), (false, vertices_293), (false, vertices_837), (false, vertices_905), (false, vertices_737), (true, vertices_26), (true, vertices_106), (true, vertices_138), (true, vertices_50), (true, vertices_274), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_200) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 8 716 76 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 3 4 7 310 50 1
cert_row_4 3 0 2 3 6 7 410 26 3
cert_rows
cert_pivot_2 8 5 1 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 2 0 1 3 4 50 310 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 26 122 3
cert_coverFacet 2 410
cert_cover_5 2 3 0 2 3 6 26 410 3
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 6 106 234 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 716
cert_cover_5 6 0 1 2 5 6 76 716 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0110

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0115.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0115

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 173, 557, 405, 837, 793, 454, 538, 618, 202, 850, 402, 740, 232, 45, 133, 261, 517, 25, 137, 521, 145, 273, 769, 26, 74, 138, 522, 146, 274, 530, 194, 322, 578, 386, 164, 548, 196, 324, 580, 388, 536, 104, 168, 552, 200, 400, 784, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_173, vertices_557, vertices_405, vertices_837, vertices_793, vertices_454, vertices_538, vertices_618, vertices_202, vertices_850, vertices_402, vertices_740, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_145, vertices_273, vertices_769, vertices_26, vertices_74, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_400, vertices_784, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_173), (false, vertices_557), (false, vertices_405), (false, vertices_837), (false, vertices_793), (true, vertices_74), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_196), (true, vertices_104), (true, vertices_200), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 74 2 522 1 274 530 194 322 578 386 196 104 200 224 608 155 173 557 793 405 837
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 74 2
cert_row_4 1 0 3 5 7 8 850 274 2
cert_row_4 2 0 1 5 6 7 454 194 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 2 0 1 5 6 194 454 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 5 74 618 2
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 274 850 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0115

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0121.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0121

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 307, 227, 707, 789, 625, 654, 426, 396, 780, 116, 308, 724, 484, 35, 195, 259, 515, 49, 273, 529, 97, 577, 769, 138, 266, 522, 162, 290, 642, 140, 268, 524, 52, 84, 276, 532, 100, 292, 196, 388, 644, 772, 392, 776, 112, 304, 592, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_307, vertices_227, vertices_707, vertices_789, vertices_625, vertices_654, vertices_426, vertices_396, vertices_780, vertices_116, vertices_308, vertices_724, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_195, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_97, vertices_577, vertices_769, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_642, vertices_140, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_196, vertices_388, vertices_644, vertices_772, vertices_392, vertices_776, vertices_112, vertices_304, vertices_592, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_307), (false, vertices_227), (false, vertices_707), (false, vertices_789), (false, vertices_625), (true, vertices_138), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_100), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 15 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
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
cert_row_4 0 1 3 5 6 8 724 84 3
cert_row_4 1 0 1 2 6 8 654 138 1
cert_row_4 2 0 2 4 6 7 426 138 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 138 654 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 138 426 2
cert_coverFacet 2 396
cert_cover_2 2 2 1 6 7 140 396 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 724
cert_cover_5 6 0 1 3 5 6 84 724 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0121

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0123.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0123

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 653, 809, 457, 369, 225, 782, 310, 150, 646, 242, 802, 220, 348, 137, 265, 521, 97, 161, 289, 545, 193, 321, 641, 22, 134, 262, 518, 50, 146, 162, 290, 546, 642, 770, 92, 140, 268, 524, 148, 276, 644, 200, 328, 776, 112, 304, 208, 336, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_653, vertices_809, vertices_457, vertices_369, vertices_225, vertices_782, vertices_310, vertices_150, vertices_646, vertices_242, vertices_802, vertices_220, vertices_348] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_22, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_92, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_644, vertices_200, vertices_328, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_653), (false, vertices_809), (false, vertices_457), (false, vertices_369), (false, vertices_225), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_290), (true, vertices_770), (true, vertices_92), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_92) then 17 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 225 1 22 2 134 3 262 518 50 146 290 770 268 148 276 208 675 653 92 809 457 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 1 3 4 7 310 22 3
cert_row_4 3 0 3 4 5 6 242 50 3
cert_rows
cert_pivot_2 8 2 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 310
cert_cover_5 1 2 0 1 3 4 22 310 3
cert_coverFacet 2 150
cert_cover_2 2 1 0 3 6 22 150 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 242
cert_cover_5 4 3 0 3 4 5 50 242 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 6 92 220 3
cert_coverFacet 7 348
cert_cover_5 7 1 1 2 3 7 92 348 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0123

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0125.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0125

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 357, 677, 841, 625, 662, 390, 602, 282, 434, 420, 376, 688, 15, 37, 261, 517, 265, 521, 97, 545, 321, 577, 134, 262, 518, 26, 266, 522, 146, 274, 530, 386, 164, 292, 388, 644, 88, 280, 328, 584, 112, 176, 304, 560, 592, 656, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_357, vertices_677, vertices_841, vertices_625, vertices_662, vertices_390, vertices_602, vertices_282, vertices_434, vertices_420, vertices_376, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_37, vertices_261, vertices_517, vertices_265, vertices_521, vertices_97, vertices_545, vertices_321, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_164, vertices_292, vertices_388, vertices_644, vertices_88, vertices_280, vertices_328, vertices_584, vertices_112, vertices_176, vertices_304, vertices_560, vertices_592, vertices_656, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_357), (false, vertices_677), (false, vertices_841), (false, vertices_625), (true, vertices_134), (true, vertices_26), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_388), (true, vertices_88), (true, vertices_280), (true, vertices_176), (true, vertices_304), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 14 else
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 5 26 602 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 146 434 2
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 88 376 2
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0125

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0126.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0126

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 781, 709, 601, 457, 214, 598, 806, 570, 434, 312, 216, 408, 808, 133, 261, 517, 73, 265, 521, 193, 577, 385, 86, 134, 262, 518, 50, 146, 530, 290, 546, 386, 196, 580, 772, 56, 88, 152, 280, 536, 296, 552, 200, 392, 776, 304, 208, 592, 400, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_781, vertices_709, vertices_601, vertices_457, vertices_214, vertices_598, vertices_806, vertices_570, vertices_434, vertices_312, vertices_216, vertices_408, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_86, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_530, vertices_290, vertices_546, vertices_386, vertices_196, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_296, vertices_552, vertices_200, vertices_392, vertices_776, vertices_304, vertices_208, vertices_592, vertices_400, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_781), (false, vertices_709), (false, vertices_601), (false, vertices_457), (true, vertices_86), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 2 3 4 8 570 50 1
cert_row_4 3 0 3 4 6 7 434 50 3
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 806
cert_cover_5 2 1 0 1 4 7 262 806 2
cert_coverFacet 3 570
cert_cover_5 3 2 0 2 3 4 50 570 1
cert_coverFacet 4 434
cert_cover_5 4 3 0 3 4 6 50 434 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0126

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0127.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0127

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 557, 205, 421, 793, 457, 710, 346, 594, 786, 482, 674, 604, 676, 13, 37, 133, 201, 265, 521, 289, 545, 385, 769, 82, 274, 530, 162, 290, 546, 194, 322, 578, 642, 770, 76, 524, 164, 548, 196, 580, 644, 88, 280, 536, 328, 592, 784, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_557, vertices_205, vertices_421, vertices_793, vertices_457, vertices_710, vertices_346, vertices_594, vertices_786, vertices_482, vertices_674, vertices_604, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_201, vertices_265, vertices_521, vertices_289, vertices_545, vertices_385, vertices_769, vertices_82, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_76, vertices_524, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_536, vertices_328, vertices_592, vertices_784, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_557), (false, vertices_205), (false, vertices_421), (false, vertices_793), (false, vertices_457), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_580), (true, vertices_644), (true, vertices_88), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 162 2
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 2 3 5 7 346 82 1
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 82 346 1
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 482
cert_cover_5 4 0 0 4 5 6 162 482 2
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0127

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0128.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0128

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 535, 779, 419, 689, 961, 590, 270, 294, 364, 116, 724, 840, 496, 23, 35, 259, 515, 49, 529, 161, 385, 641, 769, 14, 38, 262, 518, 266, 522, 290, 76, 268, 52, 84, 532, 100, 292, 580, 328, 584, 776, 112, 176, 208, 656, 352, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_535, vertices_779, vertices_419, vertices_689, vertices_961, vertices_590, vertices_270, vertices_294, vertices_364, vertices_116, vertices_724, vertices_840, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_35, vertices_259, vertices_515, vertices_49, vertices_529, vertices_161, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_290, vertices_76, vertices_268, vertices_52, vertices_84, vertices_532, vertices_100, vertices_292, vertices_580, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_535), (false, vertices_779), (false, vertices_419), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_262), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_100), (true, vertices_292), (true, vertices_580), (true, vertices_328), (true, vertices_584), (true, vertices_112), (true, vertices_208), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 5 7 364 76 2
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 76 364 2
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 84 724 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0128

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0132.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0132

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 837, 313, 625, 481, 654, 454, 570, 282, 394, 740, 424, 680, 23, 261, 517, 49, 273, 529, 97, 289, 321, 577, 134, 262, 518, 26, 138, 266, 522, 274, 530, 386, 196, 324, 580, 644, 56, 280, 168, 296, 552, 392, 648, 560, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_837, vertices_313, vertices_625, vertices_481, vertices_654, vertices_454, vertices_570, vertices_282, vertices_394, vertices_740, vertices_424, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_560, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_837), (false, vertices_313), (false, vertices_625), (false, vertices_481), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_196), (true, vertices_644), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 7 454 134 2
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 1 2 6 8 654 134 2
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 134 454 2
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 196 740 1
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0132

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0136.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0136

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 551, 899, 213, 837, 457, 570, 170, 842, 394, 188, 628, 216, 600, 39, 131, 515, 69, 133, 517, 193, 321, 385, 769, 42, 138, 266, 522, 162, 546, 386, 770, 52, 84, 148, 164, 548, 580, 56, 88, 152, 536, 168, 200, 328, 584, 392, 560, 208, 592, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_551, vertices_899, vertices_213, vertices_837, vertices_457, vertices_570, vertices_170, vertices_842, vertices_394, vertices_188, vertices_628, vertices_216, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_131, vertices_515, vertices_69, vertices_133, vertices_517, vertices_193, vertices_321, vertices_385, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_546, vertices_386, vertices_770, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_580, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_200, vertices_328, vertices_584, vertices_392, vertices_560, vertices_208, vertices_592, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_551), (false, vertices_899), (false, vertices_213), (false, vertices_837), (false, vertices_457), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_52), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_584), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 14 else
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 266 2
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 1 2 3 4 6 188 52 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 1 0 2 3 4 42 570 2
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 266 842 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 188
cert_cover_5 4 2 1 2 3 4 52 188 1
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0136

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0149.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0149

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 781, 565, 165, 389, 617, 481, 790, 122, 570, 778, 466, 244, 404, 37, 133, 261, 517, 73, 265, 521, 97, 161, 545, 321, 385, 58, 74, 266, 522, 82, 274, 530, 322, 770, 52, 148, 276, 532, 164, 388, 772, 104, 552, 776, 112, 560, 208, 400, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_781, vertices_565, vertices_165, vertices_389, vertices_617, vertices_481, vertices_790, vertices_122, vertices_570, vertices_778, vertices_466, vertices_244, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_58, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_388, vertices_772, vertices_104, vertices_552, vertices_776, vertices_112, vertices_560, vertices_208, vertices_400, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_781), (false, vertices_565), (false, vertices_165), (false, vertices_389), (false, vertices_617), (false, vertices_481), (true, vertices_58), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_148), (true, vertices_276), (true, vertices_112), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 8 58 570 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 82 466 3
cert_coverFacet 5 244
cert_cover_5 5 3 1 3 4 5 52 244 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0149

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0150.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0150

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 653, 805, 453, 433, 657, 838, 602, 242, 482, 802, 220, 588, 664, 133, 261, 517, 49, 145, 529, 289, 545, 385, 641, 50, 82, 530, 226, 290, 546, 322, 578, 770, 76, 140, 524, 196, 324, 580, 772, 88, 152, 536, 584, 648, 176, 208, 656, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_653, vertices_805, vertices_453, vertices_433, vertices_657, vertices_838, vertices_602, vertices_242, vertices_482, vertices_802, vertices_220, vertices_588, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_641, vertices_50, vertices_82, vertices_530, vertices_226, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_196, vertices_324, vertices_580, vertices_772, vertices_88, vertices_152, vertices_536, vertices_584, vertices_648, vertices_176, vertices_208, vertices_656, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_653), (false, vertices_805), (false, vertices_453), (false, vertices_433), (false, vertices_657), (true, vertices_82), (true, vertices_226), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_584), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_226) then 15 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_226), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 6 226
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 1 2 3 5 6 220 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 82 602 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 5 50 242 3
cert_coverFacet 3 482
cert_cover_5 3 0 0 4 5 7 226 482 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 220
cert_cover_5 5 3 1 2 3 5 76 220 2
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0150

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0151.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0151

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 141, 525, 901, 569, 233, 433, 838, 242, 562, 466, 610, 620, 460, 13, 133, 517, 41, 137, 521, 49, 273, 529, 161, 385, 769, 50, 210, 274, 530, 98, 546, 322, 578, 770, 76, 140, 524, 324, 580, 388, 772, 104, 552, 200, 176, 560, 400, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_141, vertices_525, vertices_901, vertices_569, vertices_233, vertices_433, vertices_838, vertices_242, vertices_562, vertices_466, vertices_610, vertices_620, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_41, vertices_137, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_385, vertices_769, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_324, vertices_580, vertices_388, vertices_772, vertices_104, vertices_552, vertices_200, vertices_176, vertices_560, vertices_400, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_141), (false, vertices_525), (false, vertices_901), (false, vertices_569), (false, vertices_233), (false, vertices_433), (true, vertices_50), (true, vertices_210), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_324), (true, vertices_580), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_569) then 18 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 242
cert_cover_5 1 0 0 3 4 5 50 242 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 466
cert_cover_5 3 0 0 3 5 7 210 466 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 620
cert_cover_5 5 2 1 2 4 5 76 620 2
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0151

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0152.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0152

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 901, 313, 777, 689, 481, 590, 346, 370, 562, 610, 460, 780, 740, 25, 265, 521, 49, 529, 161, 289, 385, 641, 769, 26, 74, 522, 50, 338, 530, 98, 546, 578, 76, 268, 524, 196, 580, 388, 644, 772, 280, 328, 776, 304, 560, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_901, vertices_313, vertices_777, vertices_689, vertices_481, vertices_590, vertices_346, vertices_370, vertices_562, vertices_610, vertices_460, vertices_780, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_265, vertices_521, vertices_49, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_769, vertices_26, vertices_74, vertices_522, vertices_50, vertices_338, vertices_530, vertices_98, vertices_546, vertices_578, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_280, vertices_328, vertices_776, vertices_304, vertices_560, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_901), (false, vertices_313), (false, vertices_777), (false, vertices_689), (false, vertices_481), (true, vertices_74), (true, vertices_50), (true, vertices_338), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_328), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_338) then 15 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 777 74 50 98 546 578 76 268 524 196 580 328 608 539 338 901 313 689 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 5 50 370 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 76 460 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 196 740 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0152

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0153.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0153

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 659, 653, 601, 457, 369, 678, 626, 306, 418, 428, 332, 588, 868, 147, 73, 137, 521, 81, 273, 529, 321, 385, 641, 50, 274, 530, 162, 290, 546, 386, 642, 76, 140, 268, 524, 164, 292, 548, 324, 580, 644, 328, 584, 392, 112, 304, 592, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_659, vertices_653, vertices_601, vertices_457, vertices_369, vertices_678, vertices_626, vertices_306, vertices_418, vertices_428, vertices_332, vertices_588, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_73, vertices_137, vertices_521, vertices_81, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_328, vertices_584, vertices_392, vertices_112, vertices_304, vertices_592, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_659), (false, vertices_653), (false, vertices_601), (false, vertices_457), (false, vertices_369), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_76), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 1 2 4 6 7 428 140 2
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 626
cert_cover_5 1 0 0 3 4 5 50 626 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 428
cert_cover_5 4 2 1 2 4 6 140 428 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 292 868 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0153

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0154.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0154

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 901, 313, 681, 457, 785, 598, 362, 618, 306, 338, 716, 468, 788, 41, 137, 265, 49, 273, 529, 545, 385, 641, 769, 106, 50, 82, 274, 530, 290, 546, 322, 578, 84, 276, 532, 196, 580, 388, 644, 772, 296, 552, 200, 328, 584, 648, 304, 336, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_901, vertices_313, vertices_681, vertices_457, vertices_785, vertices_598, vertices_362, vertices_618, vertices_306, vertices_338, vertices_716, vertices_468, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_49, vertices_273, vertices_529, vertices_545, vertices_385, vertices_641, vertices_769, vertices_106, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_336, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_901), (false, vertices_313), (false, vertices_681), (false, vertices_457), (false, vertices_785), (true, vertices_106), (true, vertices_82), (true, vertices_274), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_584), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 3 5 8 598 82 1
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 82 598 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 7 106 362 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 196 716 1
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0154

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0155.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0155

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 541, 77, 117, 713, 465, 785, 566, 682, 370, 786, 482, 236, 556, 13, 21, 69, 73, 521, 81, 273, 529, 193, 385, 641, 769, 50, 274, 530, 354, 162, 546, 386, 642, 770, 44, 76, 524, 52, 532, 100, 548, 168, 552, 200, 648, 112, 336, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_541, vertices_77, vertices_117, vertices_713, vertices_465, vertices_785, vertices_566, vertices_682, vertices_370, vertices_786, vertices_482, vertices_236, vertices_556] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_73, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_50, vertices_274, vertices_530, vertices_354, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_524, vertices_52, vertices_532, vertices_100, vertices_548, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_336, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_541), (false, vertices_77), (false, vertices_117), (false, vertices_713), (false, vertices_465), (false, vertices_785), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_354), (true, vertices_162), (true, vertices_546), (true, vertices_44), (true, vertices_548), (true, vertices_168), (true, vertices_552), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_354) then 14 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 77 1 785 50 274 530 162 546 44 548 168 552 224 899 354 541 117 713 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 1 3 4 8 566 50 1
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 50 566 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 162 682 1
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 5 50 370 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 482
cert_cover_5 4 0 0 4 5 6 354 482 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 44 236 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0155

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0156.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0156

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 331, 787, 547, 77, 781, 677, 242, 562, 466, 236, 652, 968, 944, 35, 67, 259, 515, 13, 37, 69, 517, 73, 265, 545, 769, 50, 210, 274, 530, 98, 546, 322, 76, 140, 524, 100, 164, 644, 200, 328, 648, 776, 176, 560, 400, 784, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_331, vertices_787, vertices_547, vertices_77, vertices_781, vertices_677, vertices_242, vertices_562, vertices_466, vertices_236, vertices_652, vertices_968, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_13, vertices_37, vertices_69, vertices_517, vertices_73, vertices_265, vertices_545, vertices_769, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_644, vertices_200, vertices_328, vertices_648, vertices_776, vertices_176, vertices_560, vertices_400, vertices_784, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_331), (false, vertices_787), (false, vertices_547), (false, vertices_77), (false, vertices_781), (false, vertices_677), (true, vertices_50), (true, vertices_210), (true, vertices_140), (true, vertices_200), (true, vertices_648), (true, vertices_176), (true, vertices_560), (true, vertices_400), (true, vertices_224), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 13 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_77) then 1 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_210) then 19 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 1 2 4 5 6 236 76 2
cert_row_4 2 2 5 6 7 8 968 200 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 0 0 3 4 5 50 242 3
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 7 210 466 3
cert_coverFacet 3 236
cert_cover_5 3 1 1 2 4 5 76 236 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 968
cert_cover_5 5 2 2 5 6 7 200 968 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0156

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0157.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0157

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 141, 525, 709, 569, 409, 929, 346, 562, 594, 482, 738, 604, 460, 13, 133, 517, 25, 137, 521, 49, 273, 289, 545, 385, 641, 50, 82, 274, 530, 226, 290, 546, 322, 578, 76, 140, 524, 196, 580, 88, 280, 536, 328, 392, 560, 592, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_141, vertices_525, vertices_709, vertices_569, vertices_409, vertices_929, vertices_346, vertices_562, vertices_594, vertices_482, vertices_738, vertices_604, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_137, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_385, vertices_641, vertices_50, vertices_82, vertices_274, vertices_530, vertices_226, vertices_290, vertices_546, vertices_322, vertices_578, vertices_76, vertices_140, vertices_524, vertices_196, vertices_580, vertices_88, vertices_280, vertices_536, vertices_328, vertices_392, vertices_560, vertices_592, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_141), (false, vertices_525), (false, vertices_709), (false, vertices_569), (false, vertices_409), (false, vertices_929), (true, vertices_82), (true, vertices_530), (true, vertices_226), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_88), (true, vertices_328), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_569) then 18 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_226) then 14 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_226), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 6 226
cert_row_4 1 0 2 3 5 7 346 82 1
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 4 0 3 1
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 1 0 2 3 5 82 346 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 482
cert_cover_5 3 0 0 4 5 7 226 482 3
cert_coverFacet 4 738
cert_cover_5 4 0 0 4 5 8 226 738 3
cert_coverFacet 5 604
cert_cover_5 5 2 1 2 3 5 76 604 2
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0157

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0158.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0158

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 781, 661, 389, 425, 585, 737, 790, 298, 842, 242, 306, 722, 436, 133, 261, 517, 41, 73, 265, 521, 97, 161, 577, 385, 641, 42, 74, 266, 50, 210, 274, 530, 98, 290, 578, 770, 148, 276, 532, 388, 772, 296, 584, 776, 176, 304, 656, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_781, vertices_661, vertices_389, vertices_425, vertices_585, vertices_737, vertices_790, vertices_298, vertices_842, vertices_242, vertices_306, vertices_722, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_577, vertices_385, vertices_641, vertices_42, vertices_74, vertices_266, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_290, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_781), (false, vertices_661), (false, vertices_389), (false, vertices_425), (false, vertices_585), (false, vertices_737), (true, vertices_266), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_578), (true, vertices_770), (true, vertices_276), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 50 242 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 8 210 722 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 148 436 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0158

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0178.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0178

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 357, 165, 709, 809, 689, 406, 454, 570, 282, 778, 722, 316, 180, 37, 69, 133, 161, 289, 545, 321, 577, 641, 769, 390, 26, 266, 522, 146, 274, 530, 194, 322, 578, 770, 52, 148, 276, 164, 292, 196, 324, 56, 280, 296, 552, 776, 176, 560, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_357, vertices_165, vertices_709, vertices_809, vertices_689, vertices_406, vertices_454, vertices_570, vertices_282, vertices_778, vertices_722, vertices_316, vertices_180] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_390, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_770, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_56, vertices_280, vertices_296, vertices_552, vertices_776, vertices_176, vertices_560, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_357), (false, vertices_165), (false, vertices_709), (false, vertices_809), (false, vertices_689), (true, vertices_390), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_56), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_390) then 15 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_280) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 165 26 266 522 146 274 530 194 52 148 276 56 280 835 390 357 709 809 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_2 1 0 1 6 7 390
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 1 2 3 4 7 316 52 1
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 390 406 2
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 390 454 2
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 722
cert_cover_5 5 0 0 3 5 6 146 722 2
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 52 316 1
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0178

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2283 : Certifies 2283 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0090.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2284 : Certifies 2284 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0094.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2285 : Certifies 2285 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0095.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2286 : Certifies 2286 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0099.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2287 : Certifies 2287 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0100.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2288 : Certifies 2288 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0102.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2289 : Certifies 2289 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0105.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2290 : Certifies 2290 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0106.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2291 : Certifies 2291 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0108.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2292 : Certifies 2292 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0110.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2293 : Certifies 2293 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0115.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2294 : Certifies 2294 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0121.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2295 : Certifies 2295 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0123.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2296 : Certifies 2296 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0125.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2297 : Certifies 2297 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0126.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2298 : Certifies 2298 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0127.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2299 : Certifies 2299 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0128.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2300 : Certifies 2300 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0132.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2301 : Certifies 2301 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0136.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2302 : Certifies 2302 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0149.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2303 : Certifies 2303 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0150.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2304 : Certifies 2304 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0151.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2305 : Certifies 2305 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0152.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2306 : Certifies 2306 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0153.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2307 : Certifies 2307 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0154.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2308 : Certifies 2308 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0155.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2309 : Certifies 2309 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0156.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2310 : Certifies 2310 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0157.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2311 : Certifies 2311 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0158.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2312 : Certifies 2312 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0178.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B075 (j : Fin 30) :
    Certifies (2283 + j.val) := by
  fin_cases j
  · exact projection_2283
  · exact projection_2284
  · exact projection_2285
  · exact projection_2286
  · exact projection_2287
  · exact projection_2288
  · exact projection_2289
  · exact projection_2290
  · exact projection_2291
  · exact projection_2292
  · exact projection_2293
  · exact projection_2294
  · exact projection_2295
  · exact projection_2296
  · exact projection_2297
  · exact projection_2298
  · exact projection_2299
  · exact projection_2300
  · exact projection_2301
  · exact projection_2302
  · exact projection_2303
  · exact projection_2304
  · exact projection_2305
  · exact projection_2306
  · exact projection_2307
  · exact projection_2308
  · exact projection_2309
  · exact projection_2310
  · exact projection_2311
  · exact projection_2312

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
