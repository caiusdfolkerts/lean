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
/- Source: ProjectionCertificates/R_m14e10q1_0697.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0697

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 551, 395, 659, 45, 809, 961, 158, 598, 220, 108, 868, 488, 720, 7, 11, 131, 515, 13, 37, 41, 265, 545, 385, 641, 769, 14, 22, 518, 138, 146, 530, 156, 44, 76, 84, 100, 548, 580, 104, 296, 200, 392, 208, 592, 656, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_551, vertices_395, vertices_659, vertices_45, vertices_809, vertices_961, vertices_158, vertices_598, vertices_220, vertices_108, vertices_868, vertices_488, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_13, vertices_37, vertices_41, vertices_265, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_518, vertices_138, vertices_146, vertices_530, vertices_156, vertices_44, vertices_76, vertices_84, vertices_100, vertices_548, vertices_580, vertices_104, vertices_296, vertices_200, vertices_392, vertices_208, vertices_592, vertices_656, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_551), (false, vertices_395), (false, vertices_659), (false, vertices_45), (false, vertices_809), (false, vertices_961), (true, vertices_22), (true, vertices_156), (true, vertices_76), (true, vertices_84), (true, vertices_100), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_208), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_156) then 17 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 1 2 3 6 156
cert_row_4 2 1 4 5 7 8 868 100 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 5 22 598 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 156 220 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 868
cert_cover_5 4 2 1 4 5 7 100 868 3
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0697

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0699.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0699

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 213, 165, 805, 961, 158, 174, 570, 722, 92, 300, 600, 872, 37, 69, 133, 261, 161, 545, 193, 321, 641, 769, 142, 26, 42, 146, 530, 162, 546, 642, 28, 44, 76, 268, 84, 148, 164, 292, 88, 536, 296, 552, 328, 584, 208, 592, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_213, vertices_165, vertices_805, vertices_961, vertices_158, vertices_174, vertices_570, vertices_722, vertices_92, vertices_300, vertices_600, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_261, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_142, vertices_26, vertices_42, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_84, vertices_148, vertices_164, vertices_292, vertices_88, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_208, vertices_592, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_213), (false, vertices_165), (false, vertices_805), (false, vertices_961), (true, vertices_142), (true, vertices_26), (true, vertices_42), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_88), (true, vertices_536), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_142) then 15 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 142 174 3
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 146 722 2
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 296 872 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0699

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0700.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0700

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 121, 305, 913, 737, 110, 270, 614, 774, 314, 92, 412, 964, 49, 81, 145, 273, 97, 289, 545, 193, 641, 769, 14, 102, 262, 518, 42, 266, 290, 546, 770, 28, 76, 268, 84, 148, 196, 580, 388, 772, 56, 88, 280, 104, 304, 400, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_121, vertices_305, vertices_913, vertices_737, vertices_110, vertices_270, vertices_614, vertices_774, vertices_314, vertices_92, vertices_412, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_102, vertices_262, vertices_518, vertices_42, vertices_266, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_268, vertices_84, vertices_148, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_304, vertices_400, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_121), (false, vertices_305), (false, vertices_913), (false, vertices_737), (true, vertices_14), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_580), (true, vertices_388), (true, vertices_772), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_280) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 305 14 262 518 42 266 28 76 268 580 388 772 280 803 102 213 121 913 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 5 6 7 8 964 196 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 2 3 4 7 314 42 2
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 8 102 614 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 314
cert_cover_5 4 2 0 2 3 4 42 314 2
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 964
cert_cover_5 7 0 1 5 6 7 196 964 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0700

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0703.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0703

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 899, 333, 805, 709, 217, 678, 314, 154, 242, 802, 372, 228, 344, 387, 69, 261, 517, 73, 137, 265, 193, 641, 769, 26, 138, 266, 50, 146, 162, 290, 546, 642, 770, 100, 164, 292, 548, 196, 324, 644, 88, 152, 280, 328, 112, 304, 208, 336, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_899, vertices_333, vertices_805, vertices_709, vertices_217, vertices_678, vertices_314, vertices_154, vertices_242, vertices_802, vertices_372, vertices_228, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_387, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_193, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_88, vertices_152, vertices_280, vertices_328, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_899), (false, vertices_333), (false, vertices_805), (false, vertices_709), (false, vertices_217), (true, vertices_26), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_280), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 2 3 4 7 314 26 3
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 26 314 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 100 372 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0703

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0704.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0704

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 309, 617, 561, 721, 481, 302, 526, 662, 278, 842, 962, 572, 360, 49, 145, 273, 529, 97, 289, 545, 193, 577, 385, 14, 22, 262, 518, 266, 522, 146, 274, 834, 386, 642, 44, 524, 52, 276, 532, 292, 104, 296, 552, 328, 584, 560, 656, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_309, vertices_617, vertices_561, vertices_721, vertices_481, vertices_302, vertices_526, vertices_662, vertices_278, vertices_842, vertices_962, vertices_572, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_266, vertices_522, vertices_146, vertices_274, vertices_834, vertices_386, vertices_642, vertices_44, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_560, vertices_656, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_309), (false, vertices_617), (false, vertices_561), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_834), (true, vertices_642), (true, vertices_44), (true, vertices_524), (true, vertices_532), (true, vertices_296), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_834) then 15 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_328) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 561 14 22 262 518 266 522 642 44 524 532 296 328 403 834 309 617 721 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_4 1 0 1 2 4 7 302 14 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 2 3 4 8 572 44 2
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 14 302 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 842
cert_cover_5 4 0 0 2 5 7 266 842 2
cert_coverFacet 5 962
cert_cover_5 5 0 0 5 6 7 834 962 2
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 44 572 2
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0704

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0713.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0713

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 563, 451, 707, 333, 617, 662, 434, 572, 300, 588, 308, 404, 964, 35, 195, 259, 515, 41, 73, 265, 545, 321, 577, 50, 146, 530, 290, 386, 642, 44, 76, 268, 524, 52, 148, 276, 532, 292, 324, 580, 388, 644, 296, 552, 584, 304, 560, 400, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_563, vertices_451, vertices_707, vertices_333, vertices_617, vertices_662, vertices_434, vertices_572, vertices_300, vertices_588, vertices_308, vertices_404, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_195, vertices_259, vertices_515, vertices_41, vertices_73, vertices_265, vertices_545, vertices_321, vertices_577, vertices_50, vertices_146, vertices_530, vertices_290, vertices_386, vertices_642, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_324, vertices_580, vertices_388, vertices_644, vertices_296, vertices_552, vertices_584, vertices_304, vertices_560, vertices_400, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_563), (false, vertices_451), (false, vertices_707), (false, vertices_333), (false, vertices_617), (true, vertices_146), (true, vertices_44), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_563) then 19 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_707) then 21 else
  if p.val = (false, vertices_333) then 14 else
  if p.val = (false, vertices_617) then 17 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 8 572 44 2
cert_row_4 1 0 3 4 6 7 434 50 3
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 5 6 7 8 964 324 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 434
cert_cover_5 1 1 0 3 4 6 50 434 3
cert_coverFacet 2 572
cert_cover_5 2 0 1 2 3 4 44 572 2
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 964
cert_cover_5 7 3 1 5 6 7 324 964 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0713

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0716.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0716

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 653, 597, 453, 689, 401, 334, 590, 314, 682, 562, 594, 428, 432, 69, 133, 517, 81, 145, 273, 529, 321, 385, 641, 78, 42, 266, 522, 50, 82, 274, 530, 546, 322, 578, 140, 268, 524, 324, 580, 388, 168, 296, 648, 176, 304, 560, 592, 400, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_653, vertices_597, vertices_453, vertices_689, vertices_401, vertices_334, vertices_590, vertices_314, vertices_682, vertices_562, vertices_594, vertices_428, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_78, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_546, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_388, vertices_168, vertices_296, vertices_648, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_653), (false, vertices_597), (false, vertices_453), (false, vertices_689), (false, vertices_401), (true, vertices_78), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_546), (true, vertices_578), (true, vertices_268), (true, vertices_168), (true, vertices_296), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 4 7 314 42 2
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 314
cert_cover_5 2 1 0 2 3 4 42 314 2
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 42 682 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 594
cert_cover_2 5 3 0 5 8 82 594 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 140 428 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0716

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0718.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0718

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 899, 781, 357, 677, 241, 654, 218, 282, 778, 370, 316, 172, 184, 387, 37, 261, 517, 97, 161, 193, 321, 641, 769, 26, 138, 266, 522, 82, 274, 194, 322, 642, 770, 44, 140, 268, 524, 164, 292, 644, 56, 152, 280, 168, 776, 112, 176, 304, 208, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_899, vertices_781, vertices_357, vertices_677, vertices_241, vertices_654, vertices_218, vertices_282, vertices_778, vertices_370, vertices_316, vertices_172, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_387, vertices_37, vertices_261, vertices_517, vertices_97, vertices_161, vertices_193, vertices_321, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_82, vertices_274, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_899), (false, vertices_781), (false, vertices_357), (false, vertices_677), (false, vertices_241), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_44), (true, vertices_140), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_304) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 0 26 1 138 266 522 82 274 44 140 56 152 280 168 304 451 899 781 357 677 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 2 3 5 6 218 26 3
cert_row_4 2 0 3 4 5 7 370 82 2
cert_row_4 3 1 2 3 4 7 316 44 2
cert_rows
cert_pivot_2 8 6 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 26 218 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 370
cert_cover_5 4 2 0 3 4 5 82 370 2
cert_coverFacet 5 316
cert_cover_5 5 3 1 2 3 4 44 316 2
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0718

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0720.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0720

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [79, 519, 659, 451, 525, 361, 905, 566, 214, 108, 812, 244, 688, 992, 7, 67, 131, 515, 13, 517, 73, 265, 521, 321, 385, 641, 22, 70, 518, 146, 530, 194, 44, 76, 524, 52, 212, 100, 548, 104, 296, 776, 176, 560, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_79, vertices_519, vertices_659, vertices_451, vertices_525, vertices_361, vertices_905, vertices_566, vertices_214, vertices_108, vertices_812, vertices_244, vertices_688, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_131, vertices_515, vertices_13, vertices_517, vertices_73, vertices_265, vertices_521, vertices_321, vertices_385, vertices_641, vertices_22, vertices_70, vertices_518, vertices_146, vertices_530, vertices_194, vertices_44, vertices_76, vertices_524, vertices_52, vertices_212, vertices_100, vertices_548, vertices_104, vertices_296, vertices_776, vertices_176, vertices_560, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_79), (false, vertices_519), (false, vertices_659), (false, vertices_451), (false, vertices_525), (false, vertices_361), (false, vertices_905), (true, vertices_22), (true, vertices_44), (true, vertices_52), (true, vertices_212), (true, vertices_100), (true, vertices_548), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_79) then 13 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_79), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 1 3 5 6 212
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 22 214 3
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 688
cert_cover_2 5 4 3 6 8 176 688 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0720

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0722.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0722

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 301, 597, 549, 453, 737, 542, 314, 682, 850, 962, 284, 556, 340, 37, 69, 261, 517, 161, 289, 545, 193, 577, 385, 26, 42, 522, 274, 530, 162, 290, 834, 386, 642, 28, 44, 268, 524, 84, 276, 532, 548, 324, 280, 296, 552, 336, 592, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_301, vertices_597, vertices_549, vertices_453, vertices_737, vertices_542, vertices_314, vertices_682, vertices_850, vertices_962, vertices_284, vertices_556, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_162, vertices_290, vertices_834, vertices_386, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_548, vertices_324, vertices_280, vertices_296, vertices_552, vertices_336, vertices_592, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_301), (false, vertices_597), (false, vertices_549), (false, vertices_453), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_834), (true, vertices_642), (true, vertices_28), (true, vertices_524), (true, vertices_276), (true, vertices_280), (true, vertices_552), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_834) then 15 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_2 0 0 5 7 8 834
cert_row_4 1 0 1 2 3 8 542 26 1
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 0 2 4 6 8 682 42 3
cert_rows
cert_pivot_2 5 1 3 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 26 542 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 682
cert_cover_5 2 3 0 2 4 6 42 682 3
cert_coverFacet 3 850
cert_cover_5 3 0 0 3 5 7 274 850 2
cert_coverFacet 4 962
cert_cover_5 4 0 0 5 6 7 834 962 2
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0722

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0724.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0724

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 405, 617, 849, 657, 481, 302, 558, 662, 390, 418, 604, 284, 376, 145, 273, 529, 97, 161, 545, 321, 577, 385, 641, 46, 134, 262, 518, 162, 290, 546, 386, 642, 28, 268, 524, 148, 276, 532, 388, 88, 280, 104, 296, 552, 584, 336, 592, 656, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_405, vertices_617, vertices_849, vertices_657, vertices_481, vertices_302, vertices_558, vertices_662, vertices_390, vertices_418, vertices_604, vertices_284, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_584, vertices_336, vertices_592, vertices_656, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_405), (false, vertices_617), (false, vertices_849), (false, vertices_657), (false, vertices_481), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_88), (true, vertices_280), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 657 134 262 518 290 386 28 268 524 532 88 280 296 675 46 405 617 849 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 1 2 3 5 8 604 28 3
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 6 134 662 2
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 604
cert_cover_5 5 2 1 2 3 5 28 604 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 88 376 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0724

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0725.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0725

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 341, 581, 217, 617, 401, 358, 614, 646, 682, 434, 376, 184, 69, 133, 261, 517, 73, 137, 521, 81, 145, 273, 577, 385, 102, 134, 262, 518, 162, 290, 546, 386, 642, 324, 580, 644, 56, 88, 152, 104, 168, 552, 648, 176, 304, 336, 400, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_341, vertices_581, vertices_217, vertices_617, vertices_401, vertices_358, vertices_614, vertices_646, vertices_682, vertices_434, vertices_376, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_385, vertices_102, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_324, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_104, vertices_168, vertices_552, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_341), (false, vertices_581), (false, vertices_217), (false, vertices_617), (false, vertices_401), (true, vertices_102), (true, vertices_518), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_56), (true, vertices_168), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_102) then 14 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 581 1 401 518 162 290 546 642 56 168 176 304 352 391 102 653 341 217 617
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 7 102 358 3
cert_coverFacet 1 614
cert_cover_5 1 0 0 1 4 8 102 614 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 162 682 1
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 162 434 1
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0725

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0726.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0726

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 213, 613, 645, 409, 849, 678, 186, 362, 394, 866, 124, 180, 344, 69, 133, 517, 81, 145, 273, 577, 385, 641, 769, 42, 138, 266, 354, 162, 546, 386, 642, 770, 52, 84, 148, 100, 164, 548, 644, 56, 88, 152, 280, 104, 328, 392, 176, 336, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_213, vertices_613, vertices_645, vertices_409, vertices_849, vertices_678, vertices_186, vertices_362, vertices_394, vertices_866, vertices_124, vertices_180, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_273, vertices_577, vertices_385, vertices_641, vertices_769, vertices_42, vertices_138, vertices_266, vertices_354, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_100, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_328, vertices_392, vertices_176, vertices_336, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_213), (false, vertices_613), (false, vertices_645), (false, vertices_409), (false, vertices_849), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_354), (true, vertices_162), (true, vertices_546), (true, vertices_52), (true, vertices_164), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_354) then 15 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 645 42 138 266 162 546 52 164 56 88 104 328 176 899 354 213 613 409 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 2 3 4 6 186 42 2
cert_row_4 3 1 2 3 4 5 124 52 1
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 186
cert_cover_5 1 2 0 2 3 4 42 186 2
cert_coverFacet 2 362
cert_cover_5 2 0 0 2 4 5 42 362 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 866
cert_cover_5 4 0 0 4 5 8 354 866 3
cert_coverFacet 5 124
cert_cover_5 5 3 1 2 3 4 52 124 1
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0726

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0727.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0727

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 837, 121, 425, 329, 737, 118, 790, 614, 186, 402, 674, 348, 408, 41, 73, 265, 97, 161, 321, 577, 385, 641, 769, 22, 102, 518, 50, 146, 274, 162, 546, 386, 642, 770, 84, 276, 324, 580, 772, 56, 88, 152, 280, 168, 328, 392, 112, 400, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_837, vertices_121, vertices_425, vertices_329, vertices_737, vertices_118, vertices_790, vertices_614, vertices_186, vertices_402, vertices_674, vertices_348, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_102, vertices_518, vertices_50, vertices_146, vertices_274, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_324, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_328, vertices_392, vertices_112, vertices_400, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_837), (false, vertices_121), (false, vertices_425), (false, vertices_329), (false, vertices_737), (true, vertices_22), (true, vertices_102), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_84), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 22 3
cert_row_4 1 0 2 3 4 6 186 50 1
cert_row_2 2 0 1 4 5 102
cert_row_4 3 1 2 3 5 7 348 84 1
cert_rows
cert_pivot_2 8 6 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 22 118 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 8 102 614 3
cert_coverFacet 3 186
cert_cover_5 3 1 0 2 3 4 50 186 1
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 84 348 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0727

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0728.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0728

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 837, 361, 681, 817, 705, 94, 790, 710, 154, 690, 348, 184, 312, 41, 73, 137, 289, 545, 193, 321, 577, 641, 769, 22, 70, 518, 26, 74, 138, 146, 530, 194, 642, 92, 276, 324, 580, 772, 56, 152, 280, 168, 296, 328, 176, 304, 560, 784, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_837, vertices_361, vertices_681, vertices_817, vertices_705, vertices_94, vertices_790, vertices_710, vertices_154, vertices_690, vertices_348, vertices_184, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_138, vertices_146, vertices_530, vertices_194, vertices_642, vertices_92, vertices_276, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_328, vertices_176, vertices_304, vertices_560, vertices_784, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_837), (false, vertices_361), (false, vertices_681), (false, vertices_817), (false, vertices_705), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_146), (true, vertices_530), (true, vertices_642), (true, vertices_92), (true, vertices_276), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_92) then 17 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 705 1 22 2 70 3 518 26 146 530 642 276 56 152 280 176 203 837 92 361 681 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 3 7 8 790 22 3
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 22 94 2
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 7 22 790 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 70 710 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 146 690 2
cert_coverFacet 5 348
cert_cover_5 5 0 1 2 3 7 92 348 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0728

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0729.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0729

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 901, 121, 305, 465, 737, 110, 270, 614, 774, 314, 92, 412, 724, 49, 81, 273, 97, 289, 545, 193, 385, 641, 769, 14, 102, 262, 518, 42, 266, 290, 546, 770, 28, 76, 268, 84, 148, 580, 388, 644, 772, 56, 88, 280, 104, 304, 208, 400, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_901, vertices_121, vertices_305, vertices_465, vertices_737, vertices_110, vertices_270, vertices_614, vertices_774, vertices_314, vertices_92, vertices_412, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_102, vertices_262, vertices_518, vertices_42, vertices_266, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_268, vertices_84, vertices_148, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_304, vertices_208, vertices_400, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_901), (false, vertices_121), (false, vertices_305), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_580), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_280) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 305 14 262 518 42 266 28 76 268 84 148 580 280 803 102 901 121 465 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 8 724 84 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 2 3 4 7 314 42 2
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 8 102 614 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 314
cert_cover_5 4 2 0 2 3 4 42 314 2
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 724
cert_cover_5 7 0 1 3 5 6 84 724 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0729

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0730.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0730

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 557, 361, 777, 625, 465, 782, 182, 566, 390, 402, 172, 460, 248, 41, 265, 521, 81, 273, 529, 97, 545, 321, 769, 54, 134, 262, 518, 146, 274, 530, 386, 770, 44, 140, 268, 524, 164, 548, 388, 104, 168, 200, 328, 776, 112, 176, 560, 208, 400, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_557, vertices_361, vertices_777, vertices_625, vertices_465, vertices_782, vertices_182, vertices_566, vertices_390, vertices_402, vertices_172, vertices_460, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_769, vertices_54, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_104, vertices_168, vertices_200, vertices_328, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_400, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_557), (false, vertices_361), (false, vertices_777), (false, vertices_625), (false, vertices_465), (true, vertices_54), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_146), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_388), (true, vertices_168), (true, vertices_200), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 0 1 3 4 54
cert_row_4 2 1 2 5 6 7 460 140 2
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 6 54 182 3
cert_coverFacet 2 566
cert_cover_5 2 1 0 1 3 8 54 566 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 460
cert_cover_5 6 2 1 2 5 6 140 460 2
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 104 248 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0730

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0731.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0731

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 309, 713, 625, 465, 801, 286, 654, 806, 394, 124, 620, 216, 408, 49, 81, 273, 289, 545, 193, 577, 385, 641, 769, 14, 262, 518, 138, 266, 386, 642, 770, 28, 108, 524, 52, 276, 292, 548, 88, 152, 280, 200, 584, 392, 648, 112, 208, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_309, vertices_713, vertices_625, vertices_465, vertices_801, vertices_286, vertices_654, vertices_806, vertices_394, vertices_124, vertices_620, vertices_216, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_138, vertices_266, vertices_386, vertices_642, vertices_770, vertices_28, vertices_108, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_88, vertices_152, vertices_280, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_208, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_309), (false, vertices_713), (false, vertices_625), (false, vertices_465), (false, vertices_801), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_28), (true, vertices_108), (true, vertices_524), (true, vertices_548), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_392) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
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
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 2 3 7 286 14 3
cert_row_4 2 0 1 2 6 8 654 14 3
cert_row_4 3 0 1 4 7 8 806 262 2
cert_rows
cert_pivot_2 5 3 2 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 654
cert_cover_5 1 2 0 1 2 6 14 654 3
cert_coverFacet 2 806
cert_cover_5 2 3 0 1 4 7 262 806 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 124
cert_cover_5 4 0 1 2 3 4 28 124 3
cert_coverFacet 5 620
cert_cover_5 5 0 1 2 4 8 108 620 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0731

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0732.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0732

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 805, 841, 689, 593, 481, 142, 782, 182, 566, 602, 202, 460, 420, 81, 145, 529, 161, 289, 545, 193, 321, 577, 769, 14, 54, 134, 518, 74, 138, 522, 82, 146, 530, 194, 140, 268, 164, 292, 548, 388, 772, 200, 328, 584, 776, 176, 560, 592, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_805, vertices_841, vertices_689, vertices_593, vertices_481, vertices_142, vertices_782, vertices_182, vertices_566, vertices_602, vertices_202, vertices_460, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_54, vertices_134, vertices_518, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_194, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_200, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_592, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_805), (false, vertices_841), (false, vertices_689), (false, vertices_593), (false, vertices_481), (true, vertices_14), (true, vertices_54), (true, vertices_134), (true, vertices_518), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_530), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_388), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_200) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 593 14 134 518 74 138 522 530 140 268 164 388 200 211 54 805 841 689 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 7 14 782 3
cert_coverFacet 2 182
cert_cover_5 2 0 0 1 3 6 54 182 3
cert_coverFacet 3 566
cert_cover_5 3 0 0 1 3 8 54 566 3
cert_coverFacet 4 602
cert_cover_5 4 1 0 2 3 5 74 602 2
cert_coverFacet 5 202
cert_cover_2 5 2 0 5 6 74 202 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 140 460 2
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0732

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0737.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0737

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 557, 397, 789, 361, 849, 662, 682, 242, 594, 652, 468, 424, 480, 13, 261, 517, 41, 265, 785, 97, 545, 321, 577, 82, 146, 530, 98, 162, 546, 578, 642, 140, 524, 148, 276, 532, 388, 644, 168, 296, 552, 392, 648, 208, 336, 592, 224, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_557, vertices_397, vertices_789, vertices_361, vertices_849, vertices_662, vertices_682, vertices_242, vertices_594, vertices_652, vertices_468, vertices_424, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_41, vertices_265, vertices_785, vertices_97, vertices_545, vertices_321, vertices_577, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_224, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_557), (false, vertices_397), (false, vertices_789), (false, vertices_361), (false, vertices_849), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_148), (true, vertices_644), (true, vertices_168), (true, vertices_648), (true, vertices_208), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 162 682 1
cert_coverFacet 2 242
cert_cover_5 2 2 0 3 4 5 82 242 2
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 148 468 2
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0737

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0738.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0738

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 331, 195, 677, 837, 721, 314, 602, 434, 210, 812, 420, 696, 840, 67, 131, 259, 133, 261, 517, 193, 321, 577, 641, 26, 74, 266, 306, 82, 146, 194, 386, 164, 292, 548, 388, 772, 56, 536, 296, 552, 328, 584, 776, 176, 208, 592, 656, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_331, vertices_195, vertices_677, vertices_837, vertices_721, vertices_314, vertices_602, vertices_434, vertices_210, vertices_812, vertices_420, vertices_696, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_577, vertices_641, vertices_26, vertices_74, vertices_266, vertices_306, vertices_82, vertices_146, vertices_194, vertices_386, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_56, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_331), (false, vertices_195), (false, vertices_677), (false, vertices_837), (false, vertices_721), (true, vertices_26), (true, vertices_306), (true, vertices_82), (true, vertices_146), (true, vertices_292), (true, vertices_56), (true, vertices_536), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_306) then 19 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_306), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 3 4 7 306
cert_row_4 2 1 2 4 7 8 812 292 1
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 314
cert_cover_5 0 1 0 2 3 4 26 314 3
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 434
cert_cover_5 2 1 0 3 4 6 306 434 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 292 812 1
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0738

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0739.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0739

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 453, 665, 617, 201, 849, 182, 358, 390, 570, 786, 866, 236, 184, 73, 137, 521, 145, 273, 529, 193, 321, 577, 385, 38, 134, 262, 50, 146, 274, 530, 354, 546, 386, 770, 100, 164, 196, 324, 388, 56, 152, 536, 104, 168, 552, 200, 176, 784, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_453, vertices_665, vertices_617, vertices_201, vertices_849, vertices_182, vertices_358, vertices_390, vertices_570, vertices_786, vertices_866, vertices_236, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_38, vertices_134, vertices_262, vertices_50, vertices_146, vertices_274, vertices_530, vertices_354, vertices_546, vertices_386, vertices_770, vertices_100, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_176, vertices_784, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_453), (false, vertices_665), (false, vertices_617), (false, vertices_201), (false, vertices_849), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_50), (true, vertices_530), (true, vertices_354), (true, vertices_546), (true, vertices_770), (true, vertices_100), (true, vertices_164), (true, vertices_56), (true, vertices_168), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_354) then 15 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 201 38 134 262 50 530 546 770 100 164 56 168 176 403 354 453 665 617 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 2 3 4 8 570 50 1
cert_row_4 2 0 1 3 4 6 182 38 2
cert_row_4 3 1 2 4 5 6 236 100 1
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 2 0 1 3 4 38 182 2
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 5 38 358 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 570
cert_cover_5 3 1 0 2 3 4 50 570 1
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 866
cert_cover_5 5 0 0 4 5 8 354 866 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 100 236 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0739

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0740.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0740

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 453, 361, 305, 913, 737, 110, 270, 406, 534, 614, 314, 332, 724, 49, 273, 529, 97, 289, 545, 193, 321, 385, 641, 14, 22, 102, 262, 518, 42, 266, 50, 274, 530, 546, 76, 268, 148, 532, 196, 324, 580, 388, 104, 296, 328, 304, 400, 656, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_453, vertices_361, vertices_305, vertices_913, vertices_737, vertices_110, vertices_270, vertices_406, vertices_534, vertices_614, vertices_314, vertices_332, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_14, vertices_22, vertices_102, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_546, vertices_76, vertices_268, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_104, vertices_296, vertices_328, vertices_304, vertices_400, vertices_656, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_453), (false, vertices_361), (false, vertices_305), (false, vertices_913), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_274), (true, vertices_76), (true, vertices_268), (true, vertices_148), (true, vertices_532), (true, vertices_580)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_580) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 305 14 22 262 518 42 266 274 76 268 148 532 580 563 102 453 361 913 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 22 406 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 614
cert_cover_5 4 1 0 1 4 8 102 614 3
cert_coverFacet 5 314
cert_cover_5 5 0 0 2 3 4 42 314 2
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 724
cert_cover_5 7 3 1 3 5 6 148 724 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0740

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0741.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0741

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 267, 339, 453, 425, 625, 737, 790, 682, 778, 562, 908, 724, 340, 11, 19, 259, 41, 265, 49, 81, 609, 161, 193, 321, 385, 42, 266, 522, 50, 274, 530, 546, 770, 84, 276, 532, 196, 324, 388, 644, 772, 168, 392, 648, 776, 560, 336, 592, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_267, vertices_339, vertices_453, vertices_425, vertices_625, vertices_737, vertices_790, vertices_682, vertices_778, vertices_562, vertices_908, vertices_724, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_41, vertices_265, vertices_49, vertices_81, vertices_609, vertices_161, vertices_193, vertices_321, vertices_385, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_168, vertices_392, vertices_648, vertices_776, vertices_560, vertices_336, vertices_592, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_267), (false, vertices_339), (false, vertices_453), (false, vertices_425), (false, vertices_625), (false, vertices_737), (true, vertices_522), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 20 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 1 2 6 7 8 908 388 1
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 42 682 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 908
cert_cover_5 4 2 1 2 6 7 388 908 1
cert_coverFacet 5 724
cert_cover_5 5 3 1 3 5 6 84 724 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0741

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0745.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0745

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 227, 835, 789, 421, 457, 682, 714, 572, 348, 300, 600, 424, 848, 35, 67, 515, 37, 261, 517, 161, 193, 321, 385, 769, 650, 162, 546, 194, 578, 28, 44, 268, 276, 532, 292, 548, 88, 536, 168, 296, 552, 200, 328, 584, 392, 336, 592, 784, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_227, vertices_835, vertices_789, vertices_421, vertices_457, vertices_682, vertices_714, vertices_572, vertices_348, vertices_300, vertices_600, vertices_424, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_193, vertices_321, vertices_385, vertices_769, vertices_650, vertices_162, vertices_546, vertices_194, vertices_578, vertices_28, vertices_44, vertices_268, vertices_276, vertices_532, vertices_292, vertices_548, vertices_88, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_336, vertices_592, vertices_784, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_227), (false, vertices_835), (false, vertices_789), (false, vertices_421), (false, vertices_457), (true, vertices_650), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_88), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 12 else
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_421) then 14 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_650) then 18 else
  if p.val = (true, vertices_28) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 1 2 3 4 8 572 28 3
cert_row_4 2 1 2 3 5 7 348 28 3
cert_rows_3
cert_pivot_3 4 0 1
cert_heightProof 3
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 650 682 2
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 650 714 2
cert_coverFacet 2 572
cert_cover_5 2 1 1 2 3 4 28 572 3
cert_coverFacet 3 348
cert_cover_5 3 2 1 2 3 5 28 348 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0745

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0746.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0746

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 551, 291, 597, 617, 465, 353, 902, 682, 482, 916, 248, 600, 664, 7, 35, 259, 21, 517, 81, 273, 97, 289, 545, 321, 577, 262, 518, 162, 290, 546, 386, 642, 276, 532, 900, 88, 152, 536, 104, 168, 552, 584, 648, 208, 592, 400, 656, 224, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_551, vertices_291, vertices_597, vertices_617, vertices_465, vertices_353, vertices_902, vertices_682, vertices_482, vertices_916, vertices_248, vertices_600, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_259, vertices_21, vertices_517, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_276, vertices_532, vertices_900, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_551), (false, vertices_291), (false, vertices_597), (false, vertices_617), (false, vertices_465), (false, vertices_353), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_900), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_648), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 13 else
  if p.val = (false, vertices_551) then 14 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_900) then 17 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_900), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 6 7 8 900
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 262 902 2
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 162 682 1
cert_coverFacet 2 482
cert_cover_5 2 2 0 4 5 6 162 482 2
cert_coverFacet 3 916
cert_cover_5 3 0 1 3 6 7 276 916 2
cert_coverFacet 4 248
cert_cover_5 4 3 2 3 4 5 88 248 2
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0746

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0747.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0747

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 157, 301, 277, 905, 849, 214, 230, 682, 626, 172, 340, 868, 808, 13, 21, 261, 137, 265, 145, 273, 529, 641, 769, 198, 82, 146, 530, 98, 162, 546, 642, 44, 140, 84, 148, 276, 100, 164, 292, 324, 168, 296, 552, 648, 776, 336, 592, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_157, vertices_301, vertices_277, vertices_905, vertices_849, vertices_214, vertices_230, vertices_682, vertices_626, vertices_172, vertices_340, vertices_868, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_198, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_642, vertices_44, vertices_140, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_324, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_336, vertices_592, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_157), (false, vertices_301), (false, vertices_277), (false, vertices_905), (false, vertices_849), (true, vertices_198), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_84), (true, vertices_100), (true, vertices_164), (true, vertices_324), (true, vertices_168), (true, vertices_552), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_157) then 17 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_198) then 15 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 277 82 98 162 546 84 100 164 324 168 552 608 800 659 198 157 301 905 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_2 1 0 1 5 6 198
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 198 214 2
cert_coverFacet 1 230
cert_cover_5 1 1 0 1 4 5 198 230 2
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 162 682 1
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 82 626 2
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0747

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0748.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0748

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 203, 659, 771, 185, 345, 785, 806, 710, 364, 740, 312, 232, 944, 67, 131, 259, 515, 25, 73, 137, 145, 273, 529, 321, 769, 70, 262, 518, 194, 642, 770, 100, 292, 548, 708, 324, 56, 280, 104, 168, 296, 200, 328, 176, 304, 656, 784, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_203, vertices_659, vertices_771, vertices_185, vertices_345, vertices_785, vertices_806, vertices_710, vertices_364, vertices_740, vertices_312, vertices_232, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_25, vertices_73, vertices_137, vertices_145, vertices_273, vertices_529, vertices_321, vertices_769, vertices_70, vertices_262, vertices_518, vertices_194, vertices_642, vertices_770, vertices_100, vertices_292, vertices_548, vertices_708, vertices_324, vertices_56, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_176, vertices_304, vertices_656, vertices_784, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_203), (false, vertices_659), (false, vertices_771), (false, vertices_185), (false, vertices_345), (false, vertices_785), (true, vertices_518), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_708), (true, vertices_104), (true, vertices_296), (true, vertices_304), (true, vertices_224), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_708) then 17 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_708), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_4 1 1 2 4 5 7 364 100 1
cert_row_2 2 1 5 6 8 708
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 262 806 2
cert_coverFacet 1 710
cert_cover_5 1 2 0 1 5 6 70 710 3
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 5 100 364 1
cert_coverFacet 3 740
cert_cover_5 3 2 1 4 5 6 100 740 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0748

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0749.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0749

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 203, 787, 643, 409, 329, 689, 806, 710, 364, 740, 248, 312, 816, 67, 131, 259, 515, 73, 137, 265, 145, 273, 529, 321, 641, 70, 262, 518, 194, 642, 770, 100, 292, 548, 708, 324, 56, 152, 280, 104, 296, 200, 328, 176, 304, 560, 784, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_203, vertices_787, vertices_643, vertices_409, vertices_329, vertices_689, vertices_806, vertices_710, vertices_364, vertices_740, vertices_248, vertices_312, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_321, vertices_641, vertices_70, vertices_262, vertices_518, vertices_194, vertices_642, vertices_770, vertices_100, vertices_292, vertices_548, vertices_708, vertices_324, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_176, vertices_304, vertices_560, vertices_784, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_203), (false, vertices_787), (false, vertices_643), (false, vertices_409), (false, vertices_329), (false, vertices_689), (true, vertices_518), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_708), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_304), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_708) then 17 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_708), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_2 1 1 5 6 8 708
cert_row_4 2 1 2 4 5 7 364 100 1
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 262 806 2
cert_coverFacet 1 710
cert_cover_5 1 1 0 1 5 6 70 710 3
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 100 364 1
cert_coverFacet 3 740
cert_cover_5 3 1 1 4 5 6 100 740 3
cert_coverFacet 4 248
cert_cover_5 4 3 2 3 4 5 56 248 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0749

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0750.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0750

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 653, 601, 409, 369, 449, 398, 358, 550, 646, 626, 450, 316, 572, 25, 137, 521, 81, 273, 193, 321, 577, 385, 641, 38, 134, 262, 518, 98, 546, 194, 322, 578, 386, 642, 60, 140, 268, 524, 292, 548, 644, 280, 536, 392, 112, 304, 560, 592, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_653, vertices_601, vertices_409, vertices_369, vertices_449, vertices_398, vertices_358, vertices_550, vertices_646, vertices_626, vertices_450, vertices_316, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_81, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_38, vertices_134, vertices_262, vertices_518, vertices_98, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_60, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_644, vertices_280, vertices_536, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_653), (false, vertices_601), (false, vertices_409), (false, vertices_369), (false, vertices_449), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_386), (true, vertices_60), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 449 1 38 2 134 3 262 518 98 546 322 386 268 292 548 560 707 653 60 601 409 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 4 5 7 358 38 3
cert_row_4 3 0 3 4 5 8 626 98 1
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 358
cert_cover_5 1 2 0 1 4 5 38 358 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 98 626 1
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0750

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2493 : Certifies 2493 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0697.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2494 : Certifies 2494 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0699.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2495 : Certifies 2495 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0700.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2496 : Certifies 2496 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0703.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2497 : Certifies 2497 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0704.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2498 : Certifies 2498 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0713.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2499 : Certifies 2499 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0716.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2500 : Certifies 2500 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0718.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2501 : Certifies 2501 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0720.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2502 : Certifies 2502 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0722.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2503 : Certifies 2503 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0724.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2504 : Certifies 2504 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0725.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2505 : Certifies 2505 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0726.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2506 : Certifies 2506 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0727.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2507 : Certifies 2507 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0728.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2508 : Certifies 2508 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0729.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2509 : Certifies 2509 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0730.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2510 : Certifies 2510 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0731.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2511 : Certifies 2511 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0732.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2512 : Certifies 2512 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0737.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2513 : Certifies 2513 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0738.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2514 : Certifies 2514 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0739.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2515 : Certifies 2515 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0740.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2516 : Certifies 2516 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0741.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2517 : Certifies 2517 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0745.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2518 : Certifies 2518 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0746.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2519 : Certifies 2519 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0747.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2520 : Certifies 2520 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0748.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2521 : Certifies 2521 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0749.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2522 : Certifies 2522 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0750.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B082 (j : Fin 30) :
    Certifies (2493 + j.val) := by
  fin_cases j
  · exact projection_2493
  · exact projection_2494
  · exact projection_2495
  · exact projection_2496
  · exact projection_2497
  · exact projection_2498
  · exact projection_2499
  · exact projection_2500
  · exact projection_2501
  · exact projection_2502
  · exact projection_2503
  · exact projection_2504
  · exact projection_2505
  · exact projection_2506
  · exact projection_2507
  · exact projection_2508
  · exact projection_2509
  · exact projection_2510
  · exact projection_2511
  · exact projection_2512
  · exact projection_2513
  · exact projection_2514
  · exact projection_2515
  · exact projection_2516
  · exact projection_2517
  · exact projection_2518
  · exact projection_2519
  · exact projection_2520
  · exact projection_2521
  · exact projection_2522

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
