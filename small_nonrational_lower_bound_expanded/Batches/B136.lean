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
/- Source: ProjectionCertificates/R_m16e10q1_0223.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0223

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 149, 789, 709, 409, 481, 62, 566, 346, 106, 786, 738, 156, 684, 360, 424, 21, 133, 517, 145, 273, 193, 321, 577, 385, 769, 54, 26, 42, 74, 274, 530, 98, 546, 322, 578, 770, 28, 44, 140, 148, 532, 548, 644, 152, 280, 104, 168, 296, 328, 392, 784, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_149, vertices_789, vertices_709, vertices_409, vertices_481, vertices_62, vertices_566, vertices_346, vertices_106, vertices_786, vertices_738, vertices_156, vertices_684, vertices_360, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_54, vertices_26, vertices_42, vertices_74, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_148, vertices_532, vertices_548, vertices_644, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_149), (false, vertices_789), (false, vertices_709), (false, vertices_409), (false, vertices_481), (true, vertices_54), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_548), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_54) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_328) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_2 1 0 1 3 4 54
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 3 54 62 2
cert_coverFacet 1 566
cert_cover_5 1 1 0 1 3 8 54 566 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 26 346 3
cert_coverFacet 3 106
cert_cover_2 3 2 0 4 5 42 106 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 684
cert_cover_5 7 3 1 2 4 6 44 684 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0223

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0225.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0225

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 57, 601, 369, 961, 158, 270, 710, 774, 186, 930, 540, 244, 596, 480, 25, 41, 265, 521, 49, 81, 289, 321, 577, 769, 14, 134, 262, 518, 154, 42, 266, 162, 290, 642, 770, 28, 268, 524, 84, 148, 532, 196, 580, 772, 56, 536, 112, 176, 592, 224, 352, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_57, vertices_601, vertices_369, vertices_961, vertices_158, vertices_270, vertices_710, vertices_774, vertices_186, vertices_930, vertices_540, vertices_244, vertices_596, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_134, vertices_262, vertices_518, vertices_154, vertices_42, vertices_266, vertices_162, vertices_290, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_580, vertices_772, vertices_56, vertices_536, vertices_112, vertices_176, vertices_592, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_57), (false, vertices_601), (false, vertices_369), (false, vertices_961), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_154), (true, vertices_162), (true, vertices_642), (true, vertices_770), (true, vertices_28), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_176), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 27 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_961) then 28 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_154) then 19 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_196) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 186
cert_cover_5 4 0 0 2 3 4 154 186 3
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 162 930 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 84 244 2
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0225

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0226.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0226

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 835, 643, 341, 613, 293, 681, 406, 154, 794, 650, 220, 236, 420, 632, 848, 131, 259, 515, 37, 69, 261, 161, 289, 545, 321, 577, 641, 26, 138, 522, 146, 274, 386, 642, 770, 204, 84, 148, 276, 100, 164, 292, 388, 88, 152, 536, 104, 168, 552, 648, 336, 592, 784, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_835, vertices_643, vertices_341, vertices_613, vertices_293, vertices_681, vertices_406, vertices_154, vertices_794, vertices_650, vertices_220, vertices_236, vertices_420, vertices_632, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_69, vertices_261, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_204, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_388, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_648, vertices_336, vertices_592, vertices_784, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_835), (false, vertices_643), (false, vertices_341), (false, vertices_613), (false, vertices_293), (false, vertices_681), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_204), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 22 19 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_341) then 23 else
  if p.val = (false, vertices_613) then 24 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_204) then 21 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 8 632 88 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 0 2 3 7 8 794 26 3
cert_rows
cert_pivot_2 4 5 1 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 794
cert_cover_5 2 3 0 2 3 7 26 794 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 220
cert_cover_5 4 1 1 2 3 5 204 220 2
cert_coverFacet 5 236
cert_cover_5 5 1 1 2 4 5 204 236 2
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 632
cert_cover_5 7 0 2 3 4 5 88 632 2
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0226

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0227.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0227

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 53, 789, 421, 681, 625, 334, 618, 394, 650, 850, 220, 396, 180, 340, 248, 21, 37, 261, 49, 529, 161, 545, 385, 641, 769, 74, 138, 266, 522, 322, 578, 386, 642, 770, 76, 140, 268, 52, 84, 148, 276, 164, 324, 388, 216, 104, 168, 552, 392, 648, 112, 176, 336, 592, 784, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_53, vertices_789, vertices_421, vertices_681, vertices_625, vertices_334, vertices_618, vertices_394, vertices_650, vertices_850, vertices_220, vertices_396, vertices_180, vertices_340, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_49, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_52, vertices_84, vertices_148, vertices_276, vertices_164, vertices_324, vertices_388, vertices_216, vertices_104, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_336, vertices_592, vertices_784, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_53), (false, vertices_789), (false, vertices_421), (false, vertices_681), (false, vertices_625), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_324), (true, vertices_216), (true, vertices_104), (true, vertices_392), (true, vertices_176), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_216) then 24 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 2 5 7 334 74 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 0 3 5 7 8 850 322 1
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 74 334 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 74 618 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 850
cert_cover_5 4 3 0 3 5 7 322 850 1
cert_coverFacet 5 220
cert_cover_5 5 0 1 2 3 5 76 220 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 248
cert_cover_5 9 0 2 3 4 5 216 248 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0227

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0228.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0228

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 647, 557, 341, 293, 313, 601, 705, 358, 550, 682, 466, 418, 920, 424, 720, 135, 37, 69, 261, 517, 25, 41, 521, 81, 273, 289, 193, 577, 641, 38, 70, 518, 162, 290, 546, 194, 322, 386, 642, 292, 548, 324, 280, 536, 168, 296, 552, 392, 648, 208, 336, 592, 400, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_647, vertices_557, vertices_341, vertices_293, vertices_313, vertices_601, vertices_705, vertices_358, vertices_550, vertices_682, vertices_466, vertices_418, vertices_920, vertices_424, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_135, vertices_37, vertices_69, vertices_261, vertices_517, vertices_25, vertices_41, vertices_521, vertices_81, vertices_273, vertices_289, vertices_193, vertices_577, vertices_641, vertices_38, vertices_70, vertices_518, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_292, vertices_548, vertices_324, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_647), (false, vertices_557), (false, vertices_341), (false, vertices_293), (false, vertices_313), (false, vertices_601), (false, vertices_705), (true, vertices_38), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_386), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 7 358 38 3
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 3 5 6 7 466 194 1
cert_row_4 3 2 3 6 7 8 920 280 2
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 38 358 3
cert_coverFacet 1 550
cert_cover_2 1 1 0 4 8 38 550 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 162 682 1
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 194 466 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 920
cert_cover_5 5 3 2 3 6 7 280 920 2
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0228

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0229.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0229

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 569, 177, 721, 481, 558, 142, 454, 774, 602, 202, 316, 412, 216, 432, 49, 145, 529, 161, 289, 545, 193, 321, 577, 769, 14, 134, 262, 518, 74, 138, 522, 194, 322, 578, 770, 284, 44, 140, 292, 548, 388, 772, 56, 88, 152, 536, 552, 200, 176, 304, 208, 592, 400, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_569, vertices_177, vertices_721, vertices_481, vertices_558, vertices_142, vertices_454, vertices_774, vertices_602, vertices_202, vertices_316, vertices_412, vertices_216, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_134, vertices_262, vertices_518, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_770, vertices_284, vertices_44, vertices_140, vertices_292, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_552, vertices_200, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_569), (false, vertices_177), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_284), (true, vertices_44), (true, vertices_140), (true, vertices_388), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_284) then 21 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_4 1 0 1 5 6 7 454 134 2
cert_row_2 2 1 2 3 7 284
cert_row_4 3 0 2 3 5 8 602 74 2
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 14 558 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 6 134 454 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 602
cert_cover_5 4 3 0 2 3 5 74 602 2
cert_coverFacet 5 202
cert_cover_2 5 2 0 5 6 74 202 3
cert_coverFacet 6 316
cert_cover_5 6 2 1 2 3 4 284 316 3
cert_coverFacet 7 412
cert_cover_5 7 2 1 2 3 6 284 412 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0229

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0230.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0230

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 611, 387, 771, 805, 409, 369, 902, 714, 60, 604, 428, 652, 628, 312, 216, 67, 131, 259, 515, 81, 145, 273, 97, 289, 545, 385, 769, 194, 578, 386, 642, 770, 28, 44, 140, 524, 52, 596, 292, 548, 388, 644, 772, 56, 88, 152, 280, 296, 200, 584, 392, 648, 112, 304, 208, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_611, vertices_387, vertices_771, vertices_805, vertices_409, vertices_369, vertices_902, vertices_714, vertices_60, vertices_604, vertices_428, vertices_652, vertices_628, vertices_312, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_385, vertices_769, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_52, vertices_596, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_208, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_611), (false, vertices_387), (false, vertices_771), (false, vertices_805), (false, vertices_409), (false, vertices_369), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_596), (true, vertices_388), (true, vertices_644), (true, vertices_56), (true, vertices_88), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_596) then 21 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_648) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 387 1 771 642 28 44 140 524 52 388 644 56 88 296 200 584 648 211 611 805 596 409 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 194 714 1
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 28 604 3
cert_coverFacet 4 428
cert_cover_5 4 3 1 2 4 6 44 428 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 628
cert_cover_5 6 0 1 3 4 5 52 628 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0230

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0231.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0231

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 285, 541, 357, 709, 457, 614, 186, 538, 818, 226, 706, 788, 804, 408, 496, 29, 69, 261, 517, 137, 265, 521, 193, 321, 641, 26, 138, 522, 50, 530, 98, 162, 546, 194, 578, 642, 276, 532, 100, 292, 548, 580, 772, 152, 280, 536, 392, 176, 304, 400, 784, 224, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_285, vertices_541, vertices_357, vertices_709, vertices_457, vertices_614, vertices_186, vertices_538, vertices_818, vertices_226, vertices_706, vertices_788, vertices_804, vertices_408, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_26, vertices_138, vertices_522, vertices_50, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_285), (false, vertices_541), (false, vertices_357), (false, vertices_709), (false, vertices_457), (true, vertices_26), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_548), (true, vertices_772), (true, vertices_152), (true, vertices_176), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 23 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_357) then 24 else
  if p.val = (false, vertices_709) then 25 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
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
cert_row_4 0 0 1 4 5 8 614 98 1
cert_row_4 1 0 2 3 4 6 186 26 3
cert_row_4 2 0 3 4 7 8 818 50 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 98 614 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 26 186 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 818
cert_cover_5 3 2 0 3 4 7 50 818 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 176 496 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0231

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0232.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0232

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 563, 163, 835, 333, 713, 673, 182, 402, 786, 412, 620, 684, 116, 340, 880, 35, 131, 259, 515, 73, 137, 265, 161, 545, 321, 577, 641, 50, 146, 274, 530, 162, 386, 770, 556, 76, 140, 268, 52, 84, 148, 276, 100, 164, 324, 584, 392, 648, 112, 560, 336, 400, 784, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_563, vertices_163, vertices_835, vertices_333, vertices_713, vertices_673, vertices_182, vertices_402, vertices_786, vertices_412, vertices_620, vertices_684, vertices_116, vertices_340, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_386, vertices_770, vertices_556, vertices_76, vertices_140, vertices_268, vertices_52, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_324, vertices_584, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_400, vertices_784, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_563), (false, vertices_163), (false, vertices_835), (false, vertices_333), (false, vertices_713), (false, vertices_673), (true, vertices_146), (true, vertices_274), (true, vertices_556), (true, vertices_140), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_556) then 22 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 163 673 146 274 140 52 84 148 276 100 164 112 336 400 784 608 395 563 835 333 556 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 50 1
cert_row_4 1 1 2 3 6 7 412 140 2
cert_row_2 2 1 2 4 8 556
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 50 182 1
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 412
cert_cover_5 3 1 1 2 3 6 140 412 2
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 556 620 3
cert_coverFacet 5 684
cert_cover_5 5 2 1 2 4 6 556 684 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0232

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0233.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0233

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 805, 569, 217, 425, 465, 342, 230, 646, 774, 602, 706, 684, 356, 712, 480, 25, 41, 137, 209, 273, 529, 289, 545, 385, 769, 70, 134, 262, 518, 82, 274, 530, 194, 578, 642, 770, 100, 164, 292, 548, 324, 644, 772, 88, 536, 168, 552, 200, 584, 648, 336, 224, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_805, vertices_569, vertices_217, vertices_425, vertices_465, vertices_342, vertices_230, vertices_646, vertices_774, vertices_602, vertices_706, vertices_684, vertices_356, vertices_712, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_209, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_194, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_644, vertices_772, vertices_88, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_336, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_805), (false, vertices_569), (false, vertices_217), (false, vertices_425), (false, vertices_465), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_100), (true, vertices_164), (true, vertices_324), (true, vertices_644), (true, vertices_584), (true, vertices_648), (true, vertices_224), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 21 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_217) then 25 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 70 2
cert_row_4 1 0 2 3 5 8 602 82 1
cert_row_4 2 0 1 4 5 6 230 70 2
cert_row_4 3 1 2 4 6 8 684 164 1
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 70 342 2
cert_coverFacet 1 230
cert_cover_5 1 2 0 1 4 5 70 230 2
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 602
cert_cover_5 4 1 0 2 3 5 82 602 1
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 164 684 1
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0233

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0234.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0234

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 451, 101, 165, 837, 241, 570, 282, 402, 658, 364, 812, 692, 120, 472, 131, 259, 515, 37, 69, 133, 517, 97, 161, 193, 321, 769, 26, 266, 522, 146, 274, 530, 386, 642, 300, 100, 164, 548, 324, 644, 772, 56, 88, 280, 104, 552, 328, 776, 112, 176, 560, 208, 400, 656, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_451, vertices_101, vertices_165, vertices_837, vertices_241, vertices_570, vertices_282, vertices_402, vertices_658, vertices_364, vertices_812, vertices_692, vertices_120, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_69, vertices_133, vertices_517, vertices_97, vertices_161, vertices_193, vertices_321, vertices_769, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_300, vertices_100, vertices_164, vertices_548, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_400, vertices_656, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_451), (false, vertices_101), (false, vertices_165), (false, vertices_837), (false, vertices_241), (true, vertices_26), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_300), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_560), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_300) then 22 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 1 3 4 6 8 692 164 1
cert_row_2 2 1 2 4 7 300
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 0 0 2 3 4 26 570 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 364
cert_cover_5 4 2 1 2 4 5 300 364 3
cert_coverFacet 5 812
cert_cover_5 5 2 1 2 4 8 300 812 3
cert_coverFacet 6 692
cert_cover_5 6 1 1 3 4 6 164 692 1
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0234

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0235.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0235

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 675, 771, 837, 713, 481, 790, 58, 602, 554, 188, 92, 460, 436, 596, 680, 35, 259, 515, 161, 289, 193, 321, 577, 641, 769, 26, 42, 522, 50, 274, 530, 546, 770, 28, 76, 140, 180, 84, 276, 532, 324, 580, 388, 772, 56, 88, 168, 552, 200, 584, 648, 304, 592, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_675, vertices_771, vertices_837, vertices_713, vertices_481, vertices_790, vertices_58, vertices_602, vertices_554, vertices_188, vertices_92, vertices_460, vertices_436, vertices_596, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_26, vertices_42, vertices_522, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_28, vertices_76, vertices_140, vertices_180, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_304, vertices_592, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_675), (false, vertices_771), (false, vertices_837), (false, vertices_713), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_180), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_56), (true, vertices_88), (true, vertices_168), (true, vertices_552), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_180) then 22 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_552) then 15 else
  if p.val = (true, vertices_592) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_2 0 1 3 4 6 180
cert_row_4 1 1 2 5 6 7 460 76 3
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 602
cert_cover_5 2 3 0 2 3 5 26 602 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 188
cert_cover_5 4 0 1 2 3 4 28 188 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 460
cert_cover_5 6 1 1 2 5 6 76 460 3
cert_coverFacet 7 436
cert_cover_5 7 0 1 3 4 7 180 436 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coverFacet 9 680
cert_cover_2 9 4 2 6 8 168 680 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0235

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0236.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0236

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 781, 405, 709, 105, 553, 457, 310, 534, 774, 810, 114, 722, 660, 248, 440, 133, 261, 517, 41, 73, 265, 521, 97, 545, 193, 577, 385, 22, 262, 518, 50, 82, 530, 98, 290, 546, 578, 770, 148, 276, 532, 644, 772, 184, 104, 296, 552, 200, 392, 776, 112, 304, 208, 400, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_781, vertices_405, vertices_709, vertices_105, vertices_553, vertices_457, vertices_310, vertices_534, vertices_774, vertices_810, vertices_114, vertices_722, vertices_660, vertices_248, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_22, vertices_262, vertices_518, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_184, vertices_104, vertices_296, vertices_552, vertices_200, vertices_392, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_781), (false, vertices_405), (false, vertices_709), (false, vertices_105), (false, vertices_553), (false, vertices_457), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_532), (true, vertices_184), (true, vertices_296), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_184) then 24 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_184), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_2 2 2 3 4 6 184
cert_row_4 3 0 3 5 6 8 722 82 3
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 290 810 1
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 722
cert_cover_5 5 3 0 3 5 6 82 722 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 5 184 248 3
cert_coverFacet 8 440
cert_cover_5 8 2 2 3 4 7 184 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0236

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0237.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0237

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 565, 405, 837, 457, 657, 302, 806, 106, 842, 690, 226, 60, 284, 248, 408, 21, 261, 517, 145, 529, 193, 321, 577, 385, 641, 294, 42, 74, 266, 98, 162, 546, 194, 578, 642, 770, 28, 44, 268, 52, 276, 548, 772, 56, 152, 280, 104, 200, 328, 392, 176, 560, 400, 656, 224, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_565, vertices_405, vertices_837, vertices_457, vertices_657, vertices_302, vertices_806, vertices_106, vertices_842, vertices_690, vertices_226, vertices_60, vertices_284, vertices_248, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_294, vertices_42, vertices_74, vertices_266, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_52, vertices_276, vertices_548, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_400, vertices_656, vertices_224, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_565), (false, vertices_405), (false, vertices_837), (false, vertices_457), (false, vertices_657), (true, vertices_294), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_405) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_294) then 19 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_104) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 657 42 74 266 98 162 546 770 28 44 268 56 152 280 104 176 224 707 294 565 405 837 457
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 7 294
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 0 3 4 6 8 690 162 1
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 294 302 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 8 294 806 3
cert_coverFacet 2 106
cert_cover_2 2 2 0 4 5 42 106 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 74 842 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 162 690 1
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 60
cert_cover_2 6 2 1 3 4 28 60 3
cert_coverFacet 7 284
cert_cover_2 7 2 1 3 7 28 284 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0237

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0238.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0238

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 181, 805, 709, 457, 417, 542, 566, 90, 714, 370, 802, 156, 652, 440, 344, 37, 133, 517, 161, 289, 193, 321, 577, 385, 769, 534, 26, 74, 522, 50, 82, 290, 546, 322, 578, 770, 28, 140, 524, 52, 148, 548, 644, 88, 152, 280, 200, 328, 392, 648, 176, 304, 336, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_181, vertices_805, vertices_709, vertices_457, vertices_417, vertices_542, vertices_566, vertices_90, vertices_714, vertices_370, vertices_802, vertices_156, vertices_652, vertices_440, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_534, vertices_26, vertices_74, vertices_522, vertices_50, vertices_82, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_148, vertices_548, vertices_644, vertices_88, vertices_152, vertices_280, vertices_200, vertices_328, vertices_392, vertices_648, vertices_176, vertices_304, vertices_336, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_181), (false, vertices_805), (false, vertices_709), (false, vertices_457), (false, vertices_417), (true, vertices_534), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_290), (true, vertices_546), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_648), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_534) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 417 26 74 522 50 82 290 546 28 140 524 88 152 280 648 304 336 835 534 181 805 709 457
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 8 534
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 534 542 2
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 4 534 566 3
cert_coverFacet 2 90
cert_cover_2 2 2 0 3 5 26 90 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 74 714 3
cert_coverFacet 4 370
cert_cover_5 4 2 0 3 4 5 50 370 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 152 440 2
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0238

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0239.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0239

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 357, 709, 793, 833, 614, 678, 122, 538, 170, 850, 436, 184, 408, 368, 69, 133, 261, 137, 265, 521, 321, 577, 641, 769, 550, 26, 42, 138, 522, 82, 530, 98, 162, 578, 642, 100, 164, 292, 580, 388, 644, 56, 152, 280, 536, 168, 392, 112, 176, 304, 336, 400, 784, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_357, vertices_709, vertices_793, vertices_833, vertices_614, vertices_678, vertices_122, vertices_538, vertices_170, vertices_850, vertices_436, vertices_184, vertices_408, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_769, vertices_550, vertices_26, vertices_42, vertices_138, vertices_522, vertices_82, vertices_530, vertices_98, vertices_162, vertices_578, vertices_642, vertices_100, vertices_164, vertices_292, vertices_580, vertices_388, vertices_644, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_784, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_357), (false, vertices_709), (false, vertices_793), (false, vertices_833), (true, vertices_550), (true, vertices_26), (true, vertices_42), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_578), (true, vertices_164), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_793) then 25 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_550) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 833 26 42 82 530 98 162 578 164 56 152 168 112 176 304 336 400 651 550 397 357 709 793
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 5 122 26 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_2 2 0 1 4 8 550
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 550 614 3
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 550 678 3
cert_coverFacet 2 122
cert_cover_5 2 0 0 2 3 4 26 122 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 850
cert_cover_5 5 1 0 3 5 7 82 850 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0239

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0240.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0240

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 307, 563, 707, 457, 929, 286, 598, 188, 556, 332, 588, 564, 408, 744, 432, 51, 67, 259, 515, 289, 545, 193, 321, 385, 641, 22, 70, 262, 274, 530, 578, 28, 44, 76, 268, 524, 52, 532, 548, 324, 580, 152, 280, 168, 552, 200, 328, 584, 392, 176, 304, 560, 400, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_307, vertices_563, vertices_707, vertices_457, vertices_929, vertices_286, vertices_598, vertices_188, vertices_556, vertices_332, vertices_588, vertices_564, vertices_408, vertices_744, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_67, vertices_259, vertices_515, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_22, vertices_70, vertices_262, vertices_274, vertices_530, vertices_578, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_532, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_304, vertices_560, vertices_400, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_307), (false, vertices_563), (false, vertices_707), (false, vertices_457), (false, vertices_929), (true, vertices_22), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_552), (true, vertices_584), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 18 else
  if p.val = (false, vertices_307) then 20 else
  if p.val = (false, vertices_563) then 21 else
  if p.val = (false, vertices_707) then 22 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 7 286 22 2
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 1 2 3 4 6 188 28 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 22 286 2
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 188
cert_cover_5 2 2 1 2 3 4 28 188 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 168 744 2
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0240

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0241.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0241

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 213, 405, 805, 457, 310, 186, 282, 650, 738, 802, 628, 408, 712, 240, 149, 69, 261, 517, 73, 265, 521, 193, 385, 769, 26, 138, 266, 522, 50, 274, 162, 290, 546, 642, 770, 52, 84, 276, 292, 548, 580, 152, 280, 200, 584, 392, 648, 112, 176, 208, 400, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_213, vertices_405, vertices_805, vertices_457, vertices_310, vertices_186, vertices_282, vertices_650, vertices_738, vertices_802, vertices_628, vertices_408, vertices_712, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_580, vertices_152, vertices_280, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_208, vertices_400, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_213), (false, vertices_405), (false, vertices_805), (false, vertices_457), (true, vertices_26), (true, vertices_138), (true, vertices_50), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_152), (true, vertices_280), (true, vertices_648), (true, vertices_112), (true, vertices_176), (true, vertices_224), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_213) then 23 else
  if p.val = (false, vertices_405) then 24 else
  if p.val = (false, vertices_805) then 25 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_4 1 0 2 3 4 6 186 26 3
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 26 186 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0241

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0242.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0242

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 419, 643, 589, 457, 721, 310, 242, 658, 786, 796, 236, 428, 564, 612, 624, 131, 259, 515, 73, 265, 521, 193, 577, 385, 641, 50, 146, 274, 530, 162, 290, 642, 770, 172, 76, 268, 524, 52, 276, 532, 100, 292, 548, 580, 200, 392, 776, 112, 560, 208, 592, 656, 784, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_419, vertices_643, vertices_589, vertices_457, vertices_721, vertices_310, vertices_242, vertices_658, vertices_786, vertices_796, vertices_236, vertices_428, vertices_564, vertices_612, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_642, vertices_770, vertices_172, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_200, vertices_392, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_419), (false, vertices_643), (false, vertices_589), (false, vertices_457), (false, vertices_721), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_172), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_112), (true, vertices_560), (true, vertices_784), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_419) then 19 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_172) then 22 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_2 1 1 2 4 6 172
cert_row_4 2 0 1 3 4 7 310 50 1
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 2 0 1 3 4 50 310 1
cert_coverFacet 1 242
cert_cover_5 1 0 0 3 4 5 50 242 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 796
cert_cover_5 4 3 1 2 3 7 268 796 2
cert_coverFacet 5 236
cert_cover_5 5 1 1 2 4 5 172 236 3
cert_coverFacet 6 428
cert_cover_5 6 1 1 2 4 7 172 428 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coverFacet 9 624
cert_cover_2 9 4 3 5 8 112 624 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0242

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0243.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0243

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 789, 709, 337, 481, 206, 590, 570, 426, 178, 210, 812, 240, 368, 816, 133, 261, 517, 81, 273, 529, 193, 321, 577, 385, 78, 42, 138, 522, 50, 82, 146, 530, 162, 194, 578, 140, 268, 524, 196, 580, 772, 296, 552, 392, 112, 176, 304, 560, 208, 336, 784, 224, 352, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_789, vertices_709, vertices_337, vertices_481, vertices_206, vertices_590, vertices_570, vertices_426, vertices_178, vertices_210, vertices_812, vertices_240, vertices_368, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_78, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_772, vertices_296, vertices_552, vertices_392, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_789), (false, vertices_709), (false, vertices_337), (false, vertices_481), (true, vertices_78), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_194), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_78) then 19 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 24 => Sum.inl 2
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
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 42 426 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 268 812 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coverFacet 9 816
cert_cover_2 9 4 3 7 8 304 816 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0243

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0244.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0244

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 301, 781, 181, 709, 233, 662, 794, 362, 402, 450, 706, 820, 240, 368, 464, 269, 37, 133, 517, 41, 73, 521, 161, 193, 577, 74, 266, 522, 146, 274, 530, 194, 322, 578, 386, 642, 52, 148, 532, 292, 644, 772, 104, 296, 776, 112, 176, 304, 208, 336, 400, 784, 224, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_301, vertices_781, vertices_181, vertices_709, vertices_233, vertices_662, vertices_794, vertices_362, vertices_402, vertices_450, vertices_706, vertices_820, vertices_240, vertices_368, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_161, vertices_193, vertices_577, vertices_74, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_52, vertices_148, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_301), (false, vertices_781), (false, vertices_181), (false, vertices_709), (false, vertices_233), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_532), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 23 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_181) then 24 else
  if p.val = (false, vertices_709) then 25 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 4 5 7 362 74 2
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 266 794 2
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 74 362 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0244

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0245.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0245

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 805, 217, 625, 481, 897, 94, 302, 598, 902, 282, 402, 620, 408, 232, 424, 81, 145, 529, 97, 289, 545, 193, 385, 641, 769, 14, 86, 262, 518, 26, 266, 146, 274, 530, 386, 642, 44, 76, 292, 548, 580, 772, 88, 152, 280, 104, 168, 296, 200, 392, 592, 400, 224, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_805, vertices_217, vertices_625, vertices_481, vertices_897, vertices_94, vertices_302, vertices_598, vertices_902, vertices_282, vertices_402, vertices_620, vertices_408, vertices_232, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_86, vertices_262, vertices_518, vertices_26, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_44, vertices_76, vertices_292, vertices_548, vertices_580, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_592, vertices_400, vertices_224, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_805), (false, vertices_217), (false, vertices_625), (false, vertices_481), (false, vertices_897), (true, vertices_14), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_266), (true, vertices_274), (true, vertices_386), (true, vertices_44), (true, vertices_76), (true, vertices_580), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 19 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 897 14 262 518 26 266 274 386 44 76 580 280 104 168 296 392 400 659 86 805 217 625 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 6 7 8 902 262 2
cert_row_4 2 0 1 2 4 7 302 14 3
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 302
cert_cover_5 1 2 0 1 2 4 14 302 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 8 86 598 3
cert_coverFacet 3 902
cert_cover_5 3 1 0 1 6 7 262 902 2
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0245

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0246.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0246

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 535, 229, 805, 617, 721, 782, 422, 602, 154, 394, 376, 408, 808, 464, 480, 23, 37, 133, 517, 145, 529, 97, 545, 193, 577, 134, 262, 518, 26, 138, 266, 522, 146, 530, 386, 164, 292, 772, 88, 152, 280, 104, 296, 552, 584, 392, 776, 208, 336, 592, 400, 224, 352, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_535, vertices_229, vertices_805, vertices_617, vertices_721, vertices_782, vertices_422, vertices_602, vertices_154, vertices_394, vertices_376, vertices_408, vertices_808, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_133, vertices_517, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_164, vertices_292, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_584, vertices_392, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_535), (false, vertices_229), (false, vertices_805), (false, vertices_617), (false, vertices_721), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 18 else
  if p.val = (false, vertices_535) then 19 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_4 1 0 1 2 7 8 782 262 2
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 262 782 2
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 6 134 422 2
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 26 602 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 88 376 2
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0246

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0247.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0247

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 563, 355, 341, 789, 241, 654, 394, 418, 674, 92, 156, 844, 692, 216, 488, 35, 259, 515, 277, 49, 81, 529, 97, 321, 769, 138, 266, 522, 162, 290, 546, 386, 642, 28, 76, 140, 524, 84, 148, 532, 324, 644, 772, 88, 152, 200, 328, 392, 776, 176, 560, 208, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_563, vertices_355, vertices_341, vertices_789, vertices_241, vertices_654, vertices_394, vertices_418, vertices_674, vertices_92, vertices_156, vertices_844, vertices_692, vertices_216, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_277, vertices_49, vertices_81, vertices_529, vertices_97, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_324, vertices_644, vertices_772, vertices_88, vertices_152, vertices_200, vertices_328, vertices_392, vertices_776, vertices_176, vertices_560, vertices_208, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_563), (false, vertices_355), (false, vertices_341), (false, vertices_789), (false, vertices_241), (true, vertices_138), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_563) then 19 else
  if p.val = (false, vertices_355) then 20 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_789) then 23 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 1 3 4 6 8 692 148 2
cert_row_4 2 1 2 5 7 8 844 76 3
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 674
cert_cover_2 3 4 0 6 8 162 674 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 844
cert_cover_5 6 2 1 2 5 7 76 844 3
cert_coverFacet 7 692
cert_cover_5 7 1 1 3 4 6 148 692 2
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 200 488 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0247

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0248.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0248

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 341, 805, 709, 457, 777, 118, 614, 170, 810, 178, 722, 316, 184, 408, 464, 69, 261, 517, 137, 265, 521, 193, 321, 641, 769, 102, 42, 138, 522, 50, 82, 146, 162, 546, 578, 642, 52, 84, 276, 292, 548, 580, 56, 152, 280, 168, 296, 392, 776, 176, 208, 336, 400, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_341, vertices_805, vertices_709, vertices_457, vertices_777, vertices_118, vertices_614, vertices_170, vertices_810, vertices_178, vertices_722, vertices_316, vertices_184, vertices_408, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_102, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_162, vertices_546, vertices_578, vertices_642, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_580, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_341), (false, vertices_805), (false, vertices_709), (false, vertices_457), (false, vertices_777), (true, vertices_102), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_52), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_176), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_102) then 19 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 777 42 50 82 146 162 546 578 52 56 152 280 168 296 176 208 400 651 102 341 805 709 457
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
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 810
cert_cover_5 3 2 0 2 4 7 42 810 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 722
cert_cover_5 5 0 0 3 5 6 82 722 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 52 316 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0248

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0249.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0249

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 357, 709, 777, 849, 614, 678, 58, 602, 170, 370, 436, 184, 408, 792, 69, 133, 261, 137, 265, 521, 321, 577, 641, 769, 550, 26, 42, 138, 522, 50, 82, 98, 162, 578, 642, 100, 164, 292, 580, 388, 644, 56, 152, 280, 536, 168, 392, 776, 176, 304, 336, 592, 400, 784, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_357, vertices_709, vertices_777, vertices_849, vertices_614, vertices_678, vertices_58, vertices_602, vertices_170, vertices_370, vertices_436, vertices_184, vertices_408, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_769, vertices_550, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_98, vertices_162, vertices_578, vertices_642, vertices_100, vertices_164, vertices_292, vertices_580, vertices_388, vertices_644, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_776, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_784, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_357), (false, vertices_709), (false, vertices_777), (false, vertices_849), (true, vertices_550), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_578), (true, vertices_164), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_176), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (true, vertices_550) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 777 26 42 50 82 98 162 578 164 56 152 280 536 168 176 304 400 651 550 397 357 709 849
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
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 602
cert_cover_5 3 0 0 2 3 5 26 602 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 370
cert_cover_5 5 2 0 3 4 5 50 370 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0249

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0250.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0250

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 651, 613, 121, 841, 689, 270, 526, 406, 678, 346, 780, 484, 836, 368, 432, 139, 25, 73, 521, 49, 145, 97, 545, 577, 641, 14, 134, 262, 518, 26, 266, 522, 146, 274, 642, 268, 524, 100, 164, 548, 324, 580, 388, 772, 88, 328, 776, 112, 176, 304, 336, 400, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_651, vertices_613, vertices_121, vertices_841, vertices_689, vertices_270, vertices_526, vertices_406, vertices_678, vertices_346, vertices_780, vertices_484, vertices_836, vertices_368, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_25, vertices_73, vertices_521, vertices_49, vertices_145, vertices_97, vertices_545, vertices_577, vertices_641, vertices_14, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_268, vertices_524, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_772, vertices_88, vertices_328, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_651), (false, vertices_613), (false, vertices_121), (false, vertices_841), (false, vertices_689), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_274), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_772), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 18 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
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
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 134 406 2
cert_coverFacet 3 678
cert_cover_5 3 0 0 1 4 6 134 678 2
cert_coverFacet 4 346
cert_cover_5 4 1 0 2 3 5 26 346 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0250

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0251.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0251

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 213, 405, 805, 457, 310, 154, 282, 650, 242, 674, 802, 628, 408, 744, 149, 69, 261, 517, 73, 265, 521, 193, 385, 769, 26, 138, 266, 522, 50, 146, 274, 162, 290, 546, 642, 770, 52, 84, 276, 292, 548, 580, 152, 280, 200, 584, 392, 648, 112, 208, 400, 224, 608, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_213, vertices_405, vertices_805, vertices_457, vertices_310, vertices_154, vertices_282, vertices_650, vertices_242, vertices_674, vertices_802, vertices_628, vertices_408, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_580, vertices_152, vertices_280, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_208, vertices_400, vertices_224, vertices_608, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_213), (false, vertices_405), (false, vertices_805), (false, vertices_457), (true, vertices_26), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_152), (true, vertices_280), (true, vertices_648), (true, vertices_112), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_213) then 23 else
  if p.val = (false, vertices_405) then 24 else
  if p.val = (false, vertices_805) then 25 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_4 1 0 3 4 5 6 242 50 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 242
cert_cover_5 4 1 0 3 4 5 50 242 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 628
cert_cover_5 7 2 1 3 4 5 52 628 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 744
cert_cover_5 9 3 2 4 5 6 200 744 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0251

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0252.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0252

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 93, 285, 229, 805, 617, 422, 602, 154, 394, 690, 802, 468, 408, 720, 736, 29, 37, 69, 261, 73, 265, 521, 97, 545, 769, 26, 138, 266, 522, 146, 530, 162, 290, 546, 386, 770, 84, 276, 164, 292, 196, 388, 88, 152, 280, 584, 392, 208, 592, 400, 656, 224, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_93, vertices_285, vertices_229, vertices_805, vertices_617, vertices_422, vertices_602, vertices_154, vertices_394, vertices_690, vertices_802, vertices_468, vertices_408, vertices_720, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_69, vertices_261, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_276, vertices_164, vertices_292, vertices_196, vertices_388, vertices_88, vertices_152, vertices_280, vertices_584, vertices_392, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_93), (false, vertices_285), (false, vertices_229), (false, vertices_805), (false, vertices_617), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 23 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_285) then 21 else
  if p.val = (false, vertices_229) then 24 else
  if p.val = (false, vertices_805) then 25 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 146 690 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coverFacet 9 736
cert_cover_2 9 5 4 6 8 224 736 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0252

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0253.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0253

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 403, 643, 181, 817, 737, 334, 618, 450, 706, 572, 796, 236, 212, 340, 464, 131, 259, 515, 49, 145, 273, 161, 545, 641, 769, 74, 266, 522, 194, 322, 578, 386, 642, 540, 44, 76, 268, 52, 84, 148, 276, 164, 196, 324, 104, 552, 776, 560, 208, 336, 400, 784, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_403, vertices_643, vertices_181, vertices_817, vertices_737, vertices_334, vertices_618, vertices_450, vertices_706, vertices_572, vertices_796, vertices_236, vertices_212, vertices_340, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_641, vertices_769, vertices_74, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_540, vertices_44, vertices_76, vertices_268, vertices_52, vertices_84, vertices_148, vertices_276, vertices_164, vertices_196, vertices_324, vertices_104, vertices_552, vertices_776, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_403), (false, vertices_643), (false, vertices_181), (false, vertices_817), (false, vertices_737), (true, vertices_74), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_540), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_104), (true, vertices_552), (true, vertices_208), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_540) then 22 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 8 540
cert_row_4 1 0 1 2 5 7 334 74 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 74 334 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 74 618 2
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 572
cert_cover_5 4 0 1 2 3 4 540 572 3
cert_coverFacet 5 796
cert_cover_5 5 0 1 2 3 7 540 796 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 44 236 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0253

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4113 : Certifies 4113 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0223.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4114 : Certifies 4114 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0225.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4115 : Certifies 4115 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0226.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4116 : Certifies 4116 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0227.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4117 : Certifies 4117 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0228.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4118 : Certifies 4118 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0229.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4119 : Certifies 4119 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0230.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4120 : Certifies 4120 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0231.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4121 : Certifies 4121 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0232.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4122 : Certifies 4122 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0233.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4123 : Certifies 4123 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0234.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4124 : Certifies 4124 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0235.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4125 : Certifies 4125 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0236.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4126 : Certifies 4126 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0237.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4127 : Certifies 4127 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0238.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4128 : Certifies 4128 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0239.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4129 : Certifies 4129 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0240.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4130 : Certifies 4130 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0241.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4131 : Certifies 4131 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0242.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4132 : Certifies 4132 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0243.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4133 : Certifies 4133 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0244.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4134 : Certifies 4134 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0245.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4135 : Certifies 4135 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0246.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4136 : Certifies 4136 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0247.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4137 : Certifies 4137 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0248.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4138 : Certifies 4138 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0249.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4139 : Certifies 4139 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0250.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4140 : Certifies 4140 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0251.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4141 : Certifies 4141 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0252.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4142 : Certifies 4142 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0253.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B136 (j : Fin 30) :
    Certifies (4113 + j.val) := by
  fin_cases j
  · exact projection_4113
  · exact projection_4114
  · exact projection_4115
  · exact projection_4116
  · exact projection_4117
  · exact projection_4118
  · exact projection_4119
  · exact projection_4120
  · exact projection_4121
  · exact projection_4122
  · exact projection_4123
  · exact projection_4124
  · exact projection_4125
  · exact projection_4126
  · exact projection_4127
  · exact projection_4128
  · exact projection_4129
  · exact projection_4130
  · exact projection_4131
  · exact projection_4132
  · exact projection_4133
  · exact projection_4134
  · exact projection_4135
  · exact projection_4136
  · exact projection_4137
  · exact projection_4138
  · exact projection_4139
  · exact projection_4140
  · exact projection_4141
  · exact projection_4142

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
