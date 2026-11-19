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
/- Source: ProjectionCertificates/R_m15e10q1_0942.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0942

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 835, 643, 709, 313, 241, 337, 654, 794, 394, 124, 540, 236, 852, 424, 131, 259, 515, 49, 81, 273, 161, 289, 193, 321, 577, 641, 138, 266, 522, 386, 642, 770, 28, 108, 140, 524, 84, 532, 196, 580, 644, 56, 280, 536, 168, 296, 392, 112, 336, 784, 224, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_835, vertices_643, vertices_709, vertices_313, vertices_241, vertices_337, vertices_654, vertices_794, vertices_394, vertices_124, vertices_540, vertices_236, vertices_852, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_108, vertices_140, vertices_524, vertices_84, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_112, vertices_336, vertices_784, vertices_224, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_835), (false, vertices_643), (false, vertices_709), (false, vertices_313), (false, vertices_241), (false, vertices_337), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_108), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 643 337 138 266 522 28 140 524 84 532 536 168 392 784 419 835 709 108 313 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 2 6 8 654 138 1
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 138 654 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 266 794 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 4 28 124 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 236
cert_cover_5 5 0 1 2 4 6 108 236 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 84 852 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0942

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0943.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0943

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 781, 677, 569, 361, 417, 710, 774, 842, 370, 434, 210, 120, 728, 688, 133, 261, 517, 41, 265, 521, 161, 289, 545, 385, 134, 262, 518, 306, 82, 146, 194, 322, 578, 386, 770, 644, 772, 56, 88, 536, 104, 328, 584, 776, 112, 176, 560, 208, 656, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_781, vertices_677, vertices_569, vertices_361, vertices_417, vertices_710, vertices_774, vertices_842, vertices_370, vertices_434, vertices_210, vertices_120, vertices_728, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_385, vertices_134, vertices_262, vertices_518, vertices_306, vertices_82, vertices_146, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_781), (false, vertices_677), (false, vertices_569), (false, vertices_361), (false, vertices_417), (true, vertices_518), (true, vertices_306), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_88), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_306) then 17 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_306), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_2 0 0 3 4 7 306
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 134 710 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 842
cert_cover_5 2 2 0 2 5 7 322 842 1
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 5 306 370 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 306 434 3
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0943

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0944.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0944

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 403, 611, 643, 597, 277, 665, 682, 226, 450, 796, 812, 484, 612, 440, 67, 131, 259, 515, 21, 69, 261, 145, 273, 529, 577, 641, 98, 162, 546, 194, 322, 386, 642, 780, 276, 532, 100, 292, 548, 324, 580, 152, 280, 536, 168, 296, 552, 648, 400, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_403, vertices_611, vertices_643, vertices_597, vertices_277, vertices_665, vertices_682, vertices_226, vertices_450, vertices_796, vertices_812, vertices_484, vertices_612, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_261, vertices_145, vertices_273, vertices_529, vertices_577, vertices_641, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_780, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_400, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_403), (false, vertices_611), (false, vertices_643), (false, vertices_597), (false, vertices_277), (false, vertices_665), (true, vertices_162), (true, vertices_194), (true, vertices_780), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_780) then 20 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 162 682 1
cert_coverFacet 1 226
cert_cover_2 1 4 0 5 6 98 226 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 780 796 2
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 7 780 812 2
cert_coverFacet 5 484
cert_cover_5 5 2 1 4 5 6 100 484 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 152 440 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0944

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0945.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0945

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 405, 217, 617, 169, 369, 662, 358, 614, 390, 682, 788, 836, 856, 664, 41, 73, 137, 81, 145, 273, 97, 161, 289, 385, 102, 134, 262, 518, 162, 290, 546, 386, 642, 148, 276, 532, 324, 580, 388, 772, 88, 152, 536, 168, 552, 584, 648, 336, 656, 784, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_405, vertices_217, vertices_617, vertices_169, vertices_369, vertices_662, vertices_358, vertices_614, vertices_390, vertices_682, vertices_788, vertices_836, vertices_856, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_385, vertices_102, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_168, vertices_552, vertices_584, vertices_648, vertices_336, vertices_656, vertices_784, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_405), (false, vertices_217), (false, vertices_617), (false, vertices_169), (false, vertices_369), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_546), (true, vertices_642), (true, vertices_532), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_536), (true, vertices_648), (true, vertices_656), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 169 134 262 518 546 642 532 324 580 772 536 648 656 784 832 419 102 405 217 617 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 7 8 856 88 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 1 3 6 8 662 134 2
cert_row_4 3 0 2 4 6 8 682 162 1
cert_rows
cert_pivot_2 7 5 1 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 134 662 2
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 7 102 358 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 8 102 614 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 682
cert_cover_5 4 3 0 2 4 6 162 682 1
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 856
cert_cover_5 7 0 2 3 5 7 88 856 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0945

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0946.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0946

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [47, 519, 659, 227, 781, 105, 713, 406, 534, 422, 300, 852, 872, 496, 720, 7, 35, 131, 515, 13, 517, 41, 73, 521, 97, 193, 641, 22, 38, 390, 518, 146, 530, 162, 44, 268, 276, 532, 292, 772, 104, 296, 584, 776, 208, 336, 592, 400, 656, 224, 352, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_47, vertices_519, vertices_659, vertices_227, vertices_781, vertices_105, vertices_713, vertices_406, vertices_534, vertices_422, vertices_300, vertices_852, vertices_872, vertices_496, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_131, vertices_515, vertices_13, vertices_517, vertices_41, vertices_73, vertices_521, vertices_97, vertices_193, vertices_641, vertices_22, vertices_38, vertices_390, vertices_518, vertices_146, vertices_530, vertices_162, vertices_44, vertices_268, vertices_276, vertices_532, vertices_292, vertices_772, vertices_104, vertices_296, vertices_584, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_47), (false, vertices_519), (false, vertices_659), (false, vertices_227), (false, vertices_781), (false, vertices_105), (false, vertices_713), (true, vertices_22), (true, vertices_390), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_296), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_352), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_47) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_227) then 20 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_390) then 17 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_47), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 3 5 7 8 852 276 2
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 22 406 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 276 852 2
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 208 496 1
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0946

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0947.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0947

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 557, 405, 293, 185, 537, 481, 214, 454, 774, 602, 866, 804, 216, 744, 21, 37, 261, 517, 25, 41, 521, 145, 529, 161, 289, 385, 22, 198, 262, 518, 82, 530, 322, 578, 770, 148, 292, 548, 388, 772, 88, 152, 536, 168, 552, 200, 584, 208, 224, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_557, vertices_405, vertices_293, vertices_185, vertices_537, vertices_481, vertices_214, vertices_454, vertices_774, vertices_602, vertices_866, vertices_804, vertices_216, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_517, vertices_25, vertices_41, vertices_521, vertices_145, vertices_529, vertices_161, vertices_289, vertices_385, vertices_22, vertices_198, vertices_262, vertices_518, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_148, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_208, vertices_224, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_557), (false, vertices_405), (false, vertices_293), (false, vertices_185), (false, vertices_537), (false, vertices_481), (true, vertices_198), (true, vertices_262), (true, vertices_82), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_772), (true, vertices_88), (true, vertices_200), (true, vertices_584), (true, vertices_208), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 293 1 537 262 82 322 578 770 772 88 200 584 208 608 800 535 198 557 405 185 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 2 3 5 8 602 82 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 7 198 454 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 602
cert_cover_5 3 1 0 2 3 5 82 602 1
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 168 744 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0947

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0948.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0948

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 789, 613, 453, 233, 897, 286, 58, 170, 458, 818, 898, 604, 332, 632, 69, 261, 517, 97, 161, 545, 193, 385, 641, 769, 26, 42, 138, 266, 50, 274, 162, 546, 386, 642, 770, 28, 76, 268, 276, 532, 324, 580, 56, 600, 104, 168, 200, 328, 560, 784, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_789, vertices_613, vertices_453, vertices_233, vertices_897, vertices_286, vertices_58, vertices_170, vertices_458, vertices_818, vertices_898, vertices_604, vertices_332, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_50, vertices_274, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_276, vertices_532, vertices_324, vertices_580, vertices_56, vertices_600, vertices_104, vertices_168, vertices_200, vertices_328, vertices_560, vertices_784, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_789), (false, vertices_613), (false, vertices_453), (false, vertices_233), (false, vertices_897), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_56), (true, vertices_600), (true, vertices_328), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_600) then 23 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 0 2 5 6 7 458 138 2
cert_row_2 2 2 3 5 8 600
cert_row_4 3 0 3 4 7 8 818 50 3
cert_rows
cert_pivot_2 1 6 2 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 6 138 458 2
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 50 818 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 604
cert_cover_5 6 2 1 2 3 5 28 604 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 632
cert_cover_5 8 2 2 3 4 5 56 632 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0948

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0949.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0949

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 675, 835, 45, 269, 805, 185, 598, 466, 658, 60, 92, 844, 692, 472, 131, 259, 515, 13, 37, 261, 41, 137, 265, 161, 545, 769, 82, 146, 530, 322, 578, 386, 642, 28, 44, 76, 268, 52, 84, 532, 548, 580, 772, 56, 88, 152, 328, 392, 176, 464, 656, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_675, vertices_835, vertices_45, vertices_269, vertices_805, vertices_185, vertices_598, vertices_466, vertices_658, vertices_60, vertices_92, vertices_844, vertices_692, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_261, vertices_41, vertices_137, vertices_265, vertices_161, vertices_545, vertices_769, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_52, vertices_84, vertices_532, vertices_548, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_328, vertices_392, vertices_176, vertices_464, vertices_656, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_675), (false, vertices_835), (false, vertices_45), (false, vertices_269), (false, vertices_805), (false, vertices_185), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_88), (true, vertices_328), (true, vertices_464), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_464) then 23 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
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
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_2 2 3 5 6 7 464
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 0 2 5 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 466
cert_cover_5 1 2 0 3 5 6 82 466 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 844
cert_cover_5 5 1 1 2 5 7 76 844 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 472
cert_cover_5 7 2 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0949

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0950.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0950

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 611, 163, 323, 661, 837, 681, 346, 242, 402, 796, 404, 248, 664, 872, 35, 67, 131, 259, 133, 261, 517, 161, 545, 321, 577, 641, 82, 146, 274, 98, 162, 322, 386, 148, 276, 532, 388, 772, 88, 152, 280, 536, 104, 168, 552, 328, 648, 776, 240, 400, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_611, vertices_163, vertices_323, vertices_661, vertices_837, vertices_681, vertices_346, vertices_242, vertices_402, vertices_796, vertices_404, vertices_248, vertices_664, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_259, vertices_133, vertices_261, vertices_517, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_322, vertices_386, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_552, vertices_328, vertices_648, vertices_776, vertices_240, vertices_400, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_611), (false, vertices_163), (false, vertices_323), (false, vertices_661), (false, vertices_837), (false, vertices_681), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_276), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_328), (true, vertices_776), (true, vertices_240), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_240) then 23 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 2 3 5 7 346 82 1
cert_row_4 2 1 2 3 7 8 796 276 1
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 1 0 2 3 5 82 346 1
cert_coverFacet 1 242
cert_cover_5 1 0 0 3 4 5 82 242 2
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 276 796 1
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 248
cert_cover_5 5 0 2 3 4 5 88 248 2
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0950

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0951.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0951

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 419, 547, 451, 309, 569, 345, 710, 690, 844, 180, 660, 788, 484, 792, 35, 67, 387, 515, 25, 73, 521, 49, 273, 289, 545, 321, 162, 546, 194, 578, 642, 52, 148, 276, 532, 164, 292, 196, 324, 580, 644, 772, 280, 536, 328, 584, 776, 176, 560, 656, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_419, vertices_547, vertices_451, vertices_309, vertices_569, vertices_345, vertices_710, vertices_690, vertices_844, vertices_180, vertices_660, vertices_788, vertices_484, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_387, vertices_515, vertices_25, vertices_73, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_280, vertices_536, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_656, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_419), (false, vertices_547), (false, vertices_451), (false, vertices_309), (false, vertices_569), (false, vertices_345), (true, vertices_642), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_772), (true, vertices_776), (true, vertices_176), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 162 1
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 1 2 5 7 8 844 324 1
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 690
cert_cover_5 1 0 0 3 4 6 162 690 1
cert_coverFacet 2 844
cert_cover_5 2 2 1 2 5 7 324 844 1
cert_coverFacet 3 180
cert_cover_2 3 3 1 4 6 52 180 3
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 164 484 2
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0951

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0952.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0952

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 397, 229, 549, 773, 217, 361, 790, 346, 722, 738, 354, 156, 284, 692, 37, 133, 261, 517, 73, 137, 265, 97, 289, 545, 193, 769, 82, 274, 530, 98, 290, 546, 706, 322, 770, 28, 140, 268, 148, 276, 532, 164, 548, 772, 88, 152, 280, 328, 208, 656, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_397, vertices_229, vertices_549, vertices_773, vertices_217, vertices_361, vertices_790, vertices_346, vertices_722, vertices_738, vertices_354, vertices_156, vertices_284, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_97, vertices_289, vertices_545, vertices_193, vertices_769, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_706, vertices_322, vertices_770, vertices_28, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_328, vertices_208, vertices_656, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_397), (false, vertices_229), (false, vertices_549), (false, vertices_773), (false, vertices_217), (false, vertices_361), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_706), (true, vertices_322), (true, vertices_28), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_280), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_706) then 16 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 549 1 773 82 274 530 98 322 28 148 276 532 280 656 672 803 706 397 229 217 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 82 1
cert_row_2 1 0 5 6 8 706
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 82 346 1
cert_coverFacet 2 722
cert_cover_5 2 1 0 3 5 6 82 722 3
cert_coverFacet 3 738
cert_cover_5 3 1 0 4 5 6 98 738 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 148 692 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0952

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0953.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0953

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 709, 313, 681, 585, 481, 590, 566, 214, 282, 538, 466, 436, 676, 568, 41, 73, 265, 521, 161, 289, 193, 321, 577, 641, 22, 70, 518, 26, 74, 266, 522, 210, 274, 530, 322, 52, 148, 164, 548, 196, 580, 644, 56, 280, 536, 552, 584, 304, 560, 400, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_709, vertices_313, vertices_681, vertices_585, vertices_481, vertices_590, vertices_566, vertices_214, vertices_282, vertices_538, vertices_466, vertices_436, vertices_676, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_266, vertices_522, vertices_210, vertices_274, vertices_530, vertices_322, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_552, vertices_584, vertices_304, vertices_560, vertices_400, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_709), (false, vertices_313), (false, vertices_681), (false, vertices_585), (false, vertices_481), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_164), (true, vertices_548), (true, vertices_536), (true, vertices_560), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_210) then 17 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 585 22 70 518 26 522 274 530 52 148 164 548 536 560 400 331 210 709 313 681 481
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
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 466
cert_cover_5 5 1 0 3 5 7 210 466 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0953

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0954.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0954

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 789, 601, 433, 209, 865, 110, 270, 806, 218, 394, 418, 412, 540, 620, 81, 145, 273, 529, 97, 161, 289, 193, 577, 769, 14, 38, 262, 74, 138, 266, 98, 162, 290, 194, 386, 28, 108, 268, 524, 276, 532, 548, 772, 88, 152, 536, 584, 392, 208, 400, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_789, vertices_601, vertices_433, vertices_209, vertices_865, vertices_110, vertices_270, vertices_806, vertices_218, vertices_394, vertices_418, vertices_412, vertices_540, vertices_620] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_769, vertices_14, vertices_38, vertices_262, vertices_74, vertices_138, vertices_266, vertices_98, vertices_162, vertices_290, vertices_194, vertices_386, vertices_28, vertices_108, vertices_268, vertices_524, vertices_276, vertices_532, vertices_548, vertices_772, vertices_88, vertices_152, vertices_536, vertices_584, vertices_392, vertices_208, vertices_400, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_789), (false, vertices_601), (false, vertices_433), (false, vertices_209), (false, vertices_865), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_108), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_152), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 209 1 14 38 262 74 138 266 290 386 28 268 524 548 152 392 227 789 108 601 433 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 38 3
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 2 3 5 6 218 74 2
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 38 806 3
cert_coverFacet 3 218
cert_cover_5 3 2 0 2 3 5 74 218 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 620
cert_cover_5 8 1 1 2 4 8 108 620 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0954

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0955.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0955

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 541, 301, 837, 553, 737, 790, 410, 426, 242, 594, 834, 284, 728, 680, 13, 261, 517, 41, 521, 97, 289, 545, 321, 577, 394, 82, 146, 274, 530, 98, 162, 290, 322, 578, 770, 28, 268, 276, 532, 772, 152, 280, 536, 168, 296, 552, 648, 208, 592, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_541, vertices_301, vertices_837, vertices_553, vertices_737, vertices_790, vertices_410, vertices_426, vertices_242, vertices_594, vertices_834, vertices_284, vertices_728, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_41, vertices_521, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_394, vertices_82, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_268, vertices_276, vertices_532, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_208, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_541), (false, vertices_301), (false, vertices_837), (false, vertices_553), (false, vertices_737), (true, vertices_394), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_578), (true, vertices_770), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_648), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_394) then 17 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 394 410 2
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 6 394 426 2
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 82 242 2
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 152 728 2
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0955

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0956.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0956

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 589, 661, 229, 281, 457, 401, 678, 314, 842, 178, 658, 866, 612, 496, 69, 133, 517, 25, 73, 265, 521, 145, 273, 529, 193, 385, 26, 266, 522, 50, 146, 530, 162, 290, 546, 834, 642, 100, 164, 548, 580, 644, 280, 328, 584, 176, 304, 400, 656, 224, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_589, vertices_661, vertices_229, vertices_281, vertices_457, vertices_401, vertices_678, vertices_314, vertices_842, vertices_178, vertices_658, vertices_866, vertices_612, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_25, vertices_73, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_385, vertices_26, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_834, vertices_642, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_280, vertices_328, vertices_584, vertices_176, vertices_304, vertices_400, vertices_656, vertices_224, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_589), (false, vertices_661), (false, vertices_229), (false, vertices_281), (false, vertices_457), (false, vertices_401), (true, vertices_266), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_834), (true, vertices_642), (true, vertices_548), (true, vertices_176), (true, vertices_304), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_834) then 16 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 281 1 401 266 50 146 162 290 546 642 548 176 304 352 608 539 834 589 661 229 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_2 1 0 5 7 8 834
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 266 842 2
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 290 866 2
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0956

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0957.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0957

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 181, 357, 709, 425, 897, 662, 602, 154, 362, 394, 898, 572, 620, 184, 37, 69, 133, 161, 289, 321, 577, 385, 641, 769, 26, 74, 138, 266, 146, 530, 322, 578, 386, 642, 770, 556, 52, 148, 532, 100, 580, 644, 56, 152, 536, 104, 168, 296, 584, 392, 176, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_181, vertices_357, vertices_709, vertices_425, vertices_897, vertices_662, vertices_602, vertices_154, vertices_362, vertices_394, vertices_898, vertices_572, vertices_620, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_74, vertices_138, vertices_266, vertices_146, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_556, vertices_52, vertices_148, vertices_532, vertices_100, vertices_580, vertices_644, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_584, vertices_392, vertices_176, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_181), (false, vertices_357), (false, vertices_709), (false, vertices_425), (false, vertices_897), (true, vertices_26), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_556), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_556) then 19 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 897 1 26 2 74 138 266 146 530 386 642 532 56 152 536 104 584 835 425 556 181 357 709
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 1 2 4 8 556
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 0 2 4 5 7 362 74 2
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 362
cert_cover_5 3 3 0 2 4 5 74 362 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 572
cert_cover_5 6 1 1 2 3 4 556 572 2
cert_coverFacet 7 620
cert_cover_5 7 1 1 2 4 5 556 620 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0957

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0958.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0958

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 421, 841, 369, 737, 174, 526, 310, 534, 114, 722, 226, 780, 852, 389, 137, 265, 521, 97, 161, 289, 321, 577, 641, 14, 22, 38, 518, 138, 522, 50, 82, 530, 98, 162, 194, 642, 140, 268, 524, 276, 532, 164, 292, 772, 776, 112, 304, 336, 592, 224, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_421, vertices_841, vertices_369, vertices_737, vertices_174, vertices_526, vertices_310, vertices_534, vertices_114, vertices_722, vertices_226, vertices_780, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_389, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_14, vertices_22, vertices_38, vertices_518, vertices_138, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_162, vertices_194, vertices_642, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_164, vertices_292, vertices_772, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_224, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_421), (false, vertices_841), (false, vertices_369), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_162) then 8 else
  if p.val = (true, vertices_194) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 6 174 14 3
cert_row_4 1 0 1 3 4 7 310 22 3
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 1 3 5 7 8 852 276 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 14 174 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 310
cert_cover_5 2 1 0 1 3 4 22 310 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 82 722 3
cert_coverFacet 6 226
cert_cover_2 6 4 0 5 6 98 226 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 852
cert_cover_5 8 3 1 3 5 7 276 852 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0958

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0959.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0959

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 205, 341, 677, 773, 361, 801, 790, 602, 282, 298, 714, 930, 724, 344, 69, 133, 261, 517, 41, 73, 137, 161, 289, 545, 321, 769, 26, 42, 586, 138, 266, 274, 530, 162, 290, 642, 770, 84, 276, 532, 196, 644, 772, 88, 280, 296, 200, 328, 336, 592, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_205, vertices_341, vertices_677, vertices_773, vertices_361, vertices_801, vertices_790, vertices_602, vertices_282, vertices_298, vertices_714, vertices_930, vertices_724, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_161, vertices_289, vertices_545, vertices_321, vertices_769, vertices_26, vertices_42, vertices_586, vertices_138, vertices_266, vertices_274, vertices_530, vertices_162, vertices_290, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_88, vertices_280, vertices_296, vertices_200, vertices_328, vertices_336, vertices_592, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_205), (false, vertices_341), (false, vertices_677), (false, vertices_773), (false, vertices_361), (false, vertices_801), (true, vertices_26), (true, vertices_586), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_88), (true, vertices_280), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 15 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_586) then 16 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 773 1 801 26 266 274 530 290 642 770 532 88 280 592 704 171 586 205 341 677 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 8 586
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 714
cert_cover_5 4 0 0 2 5 6 586 714 3
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 162 930 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 84 724 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0959

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0960.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0960

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 181, 901, 681, 305, 865, 206, 526, 214, 774, 618, 850, 652, 248, 368, 21, 133, 261, 49, 273, 161, 289, 545, 641, 769, 14, 22, 198, 262, 518, 74, 522, 82, 274, 578, 770, 140, 524, 148, 644, 772, 104, 168, 552, 200, 648, 112, 176, 304, 208, 336, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_181, vertices_901, vertices_681, vertices_305, vertices_865, vertices_206, vertices_526, vertices_214, vertices_774, vertices_618, vertices_850, vertices_652, vertices_248, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_49, vertices_273, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_14, vertices_22, vertices_198, vertices_262, vertices_518, vertices_74, vertices_522, vertices_82, vertices_274, vertices_578, vertices_770, vertices_140, vertices_524, vertices_148, vertices_644, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_181), (false, vertices_901), (false, vertices_681), (false, vertices_305), (false, vertices_865), (true, vertices_14), (true, vertices_198), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_578), (true, vertices_770), (true, vertices_140), (true, vertices_524), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 305 14 518 74 522 82 578 770 140 524 104 200 112 208 336 279 198 181 901 681 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 214
cert_cover_5 2 0 0 1 3 5 22 214 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 618
cert_cover_5 4 2 0 2 4 5 74 618 2
cert_coverFacet 5 850
cert_cover_5 5 1 0 3 5 7 82 850 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 104 248 1
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0960

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0961.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0961

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 677, 453, 233, 625, 833, 398, 654, 122, 282, 554, 818, 472, 680, 848, 133, 261, 517, 97, 161, 545, 193, 321, 577, 769, 142, 262, 518, 26, 42, 266, 522, 50, 274, 546, 770, 388, 644, 88, 280, 104, 168, 552, 200, 392, 648, 112, 560, 336, 592, 784, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_677, vertices_453, vertices_233, vertices_625, vertices_833, vertices_398, vertices_654, vertices_122, vertices_282, vertices_554, vertices_818, vertices_472, vertices_680, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_142, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_546, vertices_770, vertices_388, vertices_644, vertices_88, vertices_280, vertices_104, vertices_168, vertices_552, vertices_200, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_677), (false, vertices_453), (false, vertices_233), (false, vertices_625), (false, vertices_833), (true, vertices_142), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_546), (true, vertices_88), (true, vertices_280), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 833 26 42 266 522 50 274 546 88 280 552 392 648 336 784 775 142 677 453 233 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 7 142 398 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 122
cert_cover_5 2 2 0 2 3 4 26 122 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 818
cert_cover_5 5 1 0 3 4 7 50 818 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0961

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0962.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0962

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 613, 121, 169, 721, 929, 342, 598, 806, 282, 906, 658, 364, 344, 424, 25, 41, 137, 81, 145, 97, 161, 545, 577, 641, 86, 262, 518, 26, 138, 266, 146, 274, 530, 642, 770, 100, 292, 548, 324, 580, 88, 280, 104, 168, 296, 328, 392, 336, 592, 656, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_613, vertices_121, vertices_169, vertices_721, vertices_929, vertices_342, vertices_598, vertices_806, vertices_282, vertices_906, vertices_658, vertices_364, vertices_344, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_577, vertices_641, vertices_86, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_336, vertices_592, vertices_656, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_613), (false, vertices_121), (false, vertices_169), (false, vertices_721), (false, vertices_929), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 169 262 518 266 274 530 642 770 292 324 280 296 328 392 336 155 86 613 121 721 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 1 2 4 5 7 364 100 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 7 86 342 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 262 806 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 906
cert_cover_5 4 1 0 2 6 7 138 906 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 100 364 1
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0962

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0963.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0963

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 93, 653, 457, 625, 737, 278, 774, 906, 690, 306, 482, 332, 780, 372, 13, 21, 517, 73, 137, 81, 529, 609, 193, 641, 22, 262, 518, 50, 274, 530, 162, 290, 386, 642, 770, 76, 268, 524, 84, 276, 324, 772, 328, 392, 648, 776, 112, 304, 560, 224, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_93, vertices_653, vertices_457, vertices_625, vertices_737, vertices_278, vertices_774, vertices_906, vertices_690, vertices_306, vertices_482, vertices_332, vertices_780, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_73, vertices_137, vertices_81, vertices_529, vertices_609, vertices_193, vertices_641, vertices_22, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_324, vertices_772, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_224, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_93), (false, vertices_653), (false, vertices_457), (false, vertices_625), (false, vertices_737), (true, vertices_262), (true, vertices_50), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_776), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 16 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 386 1
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 386 906 1
cert_coverFacet 3 690
cert_cover_5 3 1 0 3 4 6 50 690 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 482
cert_cover_5 5 2 0 4 5 6 162 482 2
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 372
cert_cover_5 8 3 1 3 4 5 84 372 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0963

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0964.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0964

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 395, 835, 345, 617, 649, 182, 790, 402, 124, 852, 740, 184, 408, 680, 131, 259, 515, 73, 137, 265, 521, 321, 577, 641, 22, 134, 518, 146, 274, 386, 770, 52, 84, 788, 100, 164, 580, 644, 56, 88, 152, 280, 104, 168, 552, 392, 648, 176, 336, 400, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_395, vertices_835, vertices_345, vertices_617, vertices_649, vertices_182, vertices_790, vertices_402, vertices_124, vertices_852, vertices_740, vertices_184, vertices_408, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_22, vertices_134, vertices_518, vertices_146, vertices_274, vertices_386, vertices_770, vertices_52, vertices_84, vertices_788, vertices_100, vertices_164, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_552, vertices_392, vertices_648, vertices_176, vertices_336, vertices_400, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_395), (false, vertices_835), (false, vertices_345), (false, vertices_617), (false, vertices_649), (true, vertices_22), (true, vertices_146), (true, vertices_274), (true, vertices_52), (true, vertices_84), (true, vertices_788), (true, vertices_100), (true, vertices_164), (true, vertices_580), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_788) then 20 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_2 0 1 3 7 8 788
cert_row_4 1 0 1 3 4 6 182 22 3
cert_row_4 2 1 2 3 4 5 124 52 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 22 182 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 52 124 1
cert_coverFacet 4 852
cert_cover_5 4 0 1 3 5 7 84 852 3
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 100 740 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0964

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0965.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0965

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 805, 793, 457, 689, 481, 30, 78, 662, 358, 550, 234, 674, 348, 788, 25, 137, 265, 145, 529, 161, 289, 545, 449, 769, 14, 22, 38, 70, 518, 26, 74, 138, 146, 98, 162, 546, 642, 28, 76, 276, 532, 292, 548, 324, 772, 280, 200, 328, 656, 784, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_805, vertices_793, vertices_457, vertices_689, vertices_481, vertices_30, vertices_78, vertices_662, vertices_358, vertices_550, vertices_234, vertices_674, vertices_348, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_449, vertices_769, vertices_14, vertices_22, vertices_38, vertices_70, vertices_518, vertices_26, vertices_74, vertices_138, vertices_146, vertices_98, vertices_162, vertices_546, vertices_642, vertices_28, vertices_76, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_772, vertices_280, vertices_200, vertices_328, vertices_656, vertices_784, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_805), (false, vertices_793), (false, vertices_457), (false, vertices_689), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_74), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_28), (true, vertices_76), (true, vertices_276), (true, vertices_532), (true, vertices_324)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 21 23 24 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_28) then 10 else
  if p.val = (true, vertices_76) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_532) then 13 else
  if p.val = (true, vertices_324) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 22 3
cert_row_4 1 0 2 4 5 6 234 74 2
cert_row_4 2 0 1 4 5 7 358 38 3
cert_row_4 3 1 2 3 5 7 348 28 3
cert_rows
cert_pivot_2 8 6 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 78
cert_cover_2 1 1 0 2 5 14 78 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 6 22 662 3
cert_coverFacet 3 358
cert_cover_5 3 2 0 1 4 5 38 358 3
cert_coverFacet 4 550
cert_cover_2 4 1 0 4 8 38 550 3
cert_coverFacet 5 234
cert_cover_5 5 1 0 2 4 5 74 234 2
cert_coverFacet 6 674
cert_cover_2 6 4 0 6 8 162 674 3
cert_coverFacet 7 348
cert_cover_5 7 3 1 2 3 5 28 348 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0965

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0966.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0966

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 333, 653, 597, 361, 737, 790, 314, 650, 778, 178, 722, 780, 372, 240, 13, 69, 517, 41, 329, 137, 97, 161, 577, 641, 42, 138, 266, 522, 50, 146, 274, 530, 162, 642, 770, 268, 524, 84, 276, 532, 324, 772, 296, 648, 776, 112, 176, 304, 208, 592, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_333, vertices_653, vertices_597, vertices_361, vertices_737, vertices_790, vertices_314, vertices_650, vertices_778, vertices_178, vertices_722, vertices_780, vertices_372, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_41, vertices_329, vertices_137, vertices_97, vertices_161, vertices_577, vertices_641, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_642, vertices_770, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_296, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_333), (false, vertices_653), (false, vertices_597), (false, vertices_361), (false, vertices_737), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_276), (true, vertices_772), (true, vertices_776), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 16 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 42 314 2
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 6 146 722 2
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 5 84 372 2
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0966

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0967.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0967

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 181, 805, 121, 721, 865, 838, 390, 602, 362, 394, 650, 428, 184, 664, 37, 133, 517, 49, 81, 145, 97, 801, 577, 641, 134, 262, 518, 74, 138, 266, 522, 322, 578, 386, 642, 164, 292, 388, 772, 56, 88, 152, 536, 104, 168, 296, 392, 648, 176, 592, 656, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_181, vertices_805, vertices_121, vertices_721, vertices_865, vertices_838, vertices_390, vertices_602, vertices_362, vertices_394, vertices_650, vertices_428, vertices_184, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_49, vertices_81, vertices_145, vertices_97, vertices_801, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_74, vertices_138, vertices_266, vertices_522, vertices_322, vertices_578, vertices_386, vertices_642, vertices_164, vertices_292, vertices_388, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_392, vertices_648, vertices_176, vertices_592, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_181), (false, vertices_805), (false, vertices_121), (false, vertices_721), (false, vertices_865), (true, vertices_262), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 21 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_805) then 24 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_4 2 0 2 4 5 7 362 74 2
cert_row_4 3 1 2 4 6 7 428 164 1
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 262 838 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 74 602 2
cert_coverFacet 3 362
cert_cover_5 3 2 0 2 4 5 74 362 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 650
cert_cover_2 5 2 0 6 8 138 650 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 164 428 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0967

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0968.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0968

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 357, 773, 457, 913, 737, 62, 662, 410, 618, 714, 284, 300, 788, 360, 37, 261, 517, 97, 545, 193, 321, 385, 641, 769, 22, 38, 518, 26, 42, 586, 138, 146, 546, 642, 28, 44, 268, 276, 532, 292, 772, 280, 104, 296, 200, 328, 392, 400, 656, 784, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_357, vertices_773, vertices_457, vertices_913, vertices_737, vertices_62, vertices_662, vertices_410, vertices_618, vertices_714, vertices_284, vertices_300, vertices_788, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_26, vertices_42, vertices_586, vertices_138, vertices_146, vertices_546, vertices_642, vertices_28, vertices_44, vertices_268, vertices_276, vertices_532, vertices_292, vertices_772, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_357), (false, vertices_773), (false, vertices_457), (false, vertices_913), (false, vertices_737), (true, vertices_22), (true, vertices_26), (true, vertices_42), (true, vertices_586), (true, vertices_138), (true, vertices_146), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_532), (true, vertices_280), (true, vertices_104), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_586) then 17 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 773 22 26 42 138 146 642 28 44 268 276 532 280 104 296 551 586 357 457 913 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 8 586
cert_row_4 1 0 1 2 3 4 62 22 2
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 0 2 3 6 7 410 26 3
cert_rows
cert_pivot_2 5 4 1 0
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 3 22 62 2
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 410
cert_cover_5 2 3 0 2 3 6 26 410 3
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 5 42 618 3
cert_coverFacet 4 714
cert_cover_5 4 0 0 2 5 6 586 714 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0968

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0969.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0969

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 403, 771, 309, 689, 865, 454, 618, 202, 834, 572, 668, 364, 204, 404, 131, 259, 515, 49, 145, 273, 289, 545, 641, 769, 74, 138, 522, 194, 322, 578, 386, 770, 540, 44, 76, 140, 52, 148, 276, 292, 196, 324, 388, 104, 552, 200, 648, 560, 400, 656, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_403, vertices_771, vertices_309, vertices_689, vertices_865, vertices_454, vertices_618, vertices_202, vertices_834, vertices_572, vertices_668, vertices_364, vertices_204, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_289, vertices_545, vertices_641, vertices_769, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_540, vertices_44, vertices_76, vertices_140, vertices_52, vertices_148, vertices_276, vertices_292, vertices_196, vertices_324, vertices_388, vertices_104, vertices_552, vertices_200, vertices_648, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_403), (false, vertices_771), (false, vertices_309), (false, vertices_689), (false, vertices_865), (true, vertices_74), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_540), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_540) then 20 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_200) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 8 540
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 74 618 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 572
cert_cover_5 4 0 1 2 3 4 540 572 3
cert_coverFacet 5 668
cert_cover_5 5 0 1 2 3 6 540 668 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0969

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0970.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0970

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 589, 357, 677, 369, 721, 806, 314, 154, 714, 778, 674, 348, 780, 216, 37, 69, 517, 49, 81, 145, 353, 161, 577, 641, 26, 138, 266, 522, 50, 146, 162, 290, 546, 642, 770, 76, 268, 524, 292, 548, 324, 772, 88, 152, 280, 200, 584, 776, 304, 208, 336, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_589, vertices_357, vertices_677, vertices_369, vertices_721, vertices_806, vertices_314, vertices_154, vertices_714, vertices_778, vertices_674, vertices_348, vertices_780, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_49, vertices_81, vertices_145, vertices_353, vertices_161, vertices_577, vertices_641, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_292, vertices_548, vertices_324, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_584, vertices_776, vertices_304, vertices_208, vertices_336, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_589), (false, vertices_357), (false, vertices_677), (false, vertices_369), (false, vertices_721), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_772), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 21 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_357) then 24 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_776) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 1 2 3 5 7 348 76 2
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 714
cert_cover_5 3 0 0 2 5 6 138 714 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 76 348 2
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0970

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0971.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0971

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 285, 309, 613, 841, 481, 158, 54, 102, 582, 650, 242, 962, 440, 904, 13, 277, 37, 517, 265, 521, 97, 289, 321, 577, 14, 22, 38, 70, 518, 138, 522, 50, 146, 98, 194, 578, 642, 28, 52, 100, 580, 152, 280, 392, 648, 776, 176, 304, 224, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_285, vertices_309, vertices_613, vertices_841, vertices_481, vertices_158, vertices_54, vertices_102, vertices_582, vertices_650, vertices_242, vertices_962, vertices_440, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_277, vertices_37, vertices_517, vertices_265, vertices_521, vertices_97, vertices_289, vertices_321, vertices_577, vertices_14, vertices_22, vertices_38, vertices_70, vertices_518, vertices_138, vertices_522, vertices_50, vertices_146, vertices_98, vertices_194, vertices_578, vertices_642, vertices_28, vertices_52, vertices_100, vertices_580, vertices_152, vertices_280, vertices_392, vertices_648, vertices_776, vertices_176, vertices_304, vertices_224, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_285), (false, vertices_309), (false, vertices_613), (false, vertices_841), (false, vertices_481), (true, vertices_22), (true, vertices_38), (true, vertices_70), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_152), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 6 158 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 54
cert_cover_2 1 1 0 3 4 22 54 3
cert_coverFacet 2 102
cert_cover_2 2 1 0 4 5 38 102 3
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 242
cert_cover_5 5 2 0 3 4 5 50 242 3
cert_coverFacet 6 962
cert_cover_5 6 1 0 5 6 7 194 962 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 152 440 2
cert_coverFacet 8 904
cert_cover_2 8 6 2 7 8 392 904 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0971

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3513 : Certifies 3513 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0942.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3514 : Certifies 3514 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0943.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3515 : Certifies 3515 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0944.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3516 : Certifies 3516 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0945.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3517 : Certifies 3517 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0946.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3518 : Certifies 3518 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0947.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3519 : Certifies 3519 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0948.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3520 : Certifies 3520 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0949.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3521 : Certifies 3521 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0950.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3522 : Certifies 3522 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0951.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3523 : Certifies 3523 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0952.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3524 : Certifies 3524 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0953.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3525 : Certifies 3525 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0954.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3526 : Certifies 3526 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0955.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3527 : Certifies 3527 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0956.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3528 : Certifies 3528 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0957.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3529 : Certifies 3529 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0958.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3530 : Certifies 3530 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0959.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3531 : Certifies 3531 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0960.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3532 : Certifies 3532 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0961.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3533 : Certifies 3533 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0962.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3534 : Certifies 3534 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0963.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3535 : Certifies 3535 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0964.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3536 : Certifies 3536 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0965.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3537 : Certifies 3537 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0966.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3538 : Certifies 3538 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0967.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3539 : Certifies 3539 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0968.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3540 : Certifies 3540 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0969.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3541 : Certifies 3541 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0970.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3542 : Certifies 3542 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0971.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B116 (j : Fin 30) :
    Certifies (3513 + j.val) := by
  fin_cases j
  · exact projection_3513
  · exact projection_3514
  · exact projection_3515
  · exact projection_3516
  · exact projection_3517
  · exact projection_3518
  · exact projection_3519
  · exact projection_3520
  · exact projection_3521
  · exact projection_3522
  · exact projection_3523
  · exact projection_3524
  · exact projection_3525
  · exact projection_3526
  · exact projection_3527
  · exact projection_3528
  · exact projection_3529
  · exact projection_3530
  · exact projection_3531
  · exact projection_3532
  · exact projection_3533
  · exact projection_3534
  · exact projection_3535
  · exact projection_3536
  · exact projection_3537
  · exact projection_3538
  · exact projection_3539
  · exact projection_3540
  · exact projection_3541
  · exact projection_3542

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
