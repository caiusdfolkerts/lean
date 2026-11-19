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
/- Source: ProjectionCertificates/R_one_six_1161.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1161

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 149, 553, 625, 913, 206, 458, 124, 724, 360, 808, 992, 7, 11, 259, 21, 133, 41, 521, 49, 145, 529, 545, 385, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 196, 104, 296, 552, 328, 776, 112, 592, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_149, vertices_553, vertices_625, vertices_913, vertices_206, vertices_458, vertices_124, vertices_724, vertices_360, vertices_808, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_385, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_112, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_149), (false, vertices_553), (false, vertices_625), (false, vertices_913), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 12 21 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_913) then 17 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1161

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1162.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1162

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 721, 897, 782, 458, 556, 628, 360, 808, 992, 7, 11, 131, 21, 261, 57, 73, 81, 529, 193, 385, 641, 769, 14, 262, 202, 266, 386, 44, 524, 52, 532, 548, 772, 104, 296, 552, 328, 776, 112, 592, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_721, vertices_897, vertices_782, vertices_458, vertices_556, vertices_628, vertices_360, vertices_808, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_202, vertices_266, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_112, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (false, vertices_897), (true, vertices_266), (true, vertices_524), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 8 628 52 3
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_2 2 0 2 5 6 202
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 3 1 0 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 458
cert_cover_5 1 2 0 2 5 7 202 458 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1162

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1163.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1163

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 277, 617, 817, 206, 458, 124, 212, 916, 840, 752, 960, 7, 11, 259, 21, 261, 41, 521, 49, 273, 545, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 276, 196, 388, 104, 328, 584, 776, 112, 560, 208, 656, 784, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_277, vertices_617, vertices_817, vertices_206, vertices_458, vertices_124, vertices_212, vertices_916, vertices_840, vertices_752, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_277), (false, vertices_617), (false, vertices_817), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_656), (true, vertices_448), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 21 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 916
cert_cover_5 4 2 1 3 6 7 148 916 3
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1163

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1164.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1164

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 149, 617, 689, 206, 458, 898, 124, 468, 840, 880, 912, 7, 11, 515, 21, 133, 41, 521, 49, 145, 545, 641, 14, 134, 202, 266, 386, 642, 770, 60, 76, 84, 148, 196, 104, 328, 584, 776, 112, 560, 336, 400, 656, 784, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_149, vertices_617, vertices_689, vertices_206, vertices_458, vertices_898, vertices_124, vertices_468, vertices_840, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_641, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_560, vertices_336, vertices_400, vertices_656, vertices_784, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_149), (false, vertices_617), (false, vertices_689), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_328), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 21 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_689) then 17 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1164

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1165.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1165

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 553, 865, 526, 902, 220, 652, 696, 624, 976, 7, 11, 195, 259, 53, 69, 41, 521, 97, 545, 321, 769, 14, 134, 518, 522, 386, 770, 28, 140, 524, 84, 196, 644, 56, 152, 552, 648, 112, 560, 208, 592, 656, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_553, vertices_865, vertices_526, vertices_902, vertices_220, vertices_652, vertices_696, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_545, vertices_321, vertices_769, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_140, vertices_524, vertices_84, vertices_196, vertices_644, vertices_56, vertices_152, vertices_552, vertices_648, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_553), (false, vertices_865), (true, vertices_518), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_152), (true, vertices_648), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 14 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 2 3 5 6 220 28 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1165

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1166.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1166

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 553, 865, 526, 902, 220, 652, 696, 496, 928, 7, 11, 195, 259, 53, 69, 41, 521, 97, 545, 321, 769, 14, 134, 518, 522, 386, 770, 28, 140, 524, 84, 196, 644, 56, 152, 552, 648, 112, 176, 208, 352, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_553, vertices_865, vertices_526, vertices_902, vertices_220, vertices_652, vertices_696, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_545, vertices_321, vertices_769, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_140, vertices_524, vertices_84, vertices_196, vertices_644, vertices_56, vertices_152, vertices_552, vertices_648, vertices_112, vertices_176, vertices_208, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_553), (false, vertices_865), (true, vertices_518), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_152), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 14 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 2 3 5 6 220 28 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1166

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1167.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1167

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 149, 361, 689, 801, 206, 458, 898, 124, 468, 880, 912, 7, 11, 515, 21, 133, 41, 265, 49, 145, 289, 545, 641, 769, 14, 134, 202, 266, 386, 642, 770, 60, 76, 84, 148, 196, 104, 328, 112, 560, 336, 400, 656, 784, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_149, vertices_361, vertices_689, vertices_801, vertices_206, vertices_458, vertices_898, vertices_124, vertices_468, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_133, vertices_41, vertices_265, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_328, vertices_112, vertices_560, vertices_336, vertices_400, vertices_656, vertices_784, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_149), (false, vertices_361), (false, vertices_689), (false, vertices_801), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 20 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_689) then 16 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1167

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1168.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1168

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 789, 361, 305, 206, 458, 898, 124, 724, 624, 816, 992, 7, 11, 515, 21, 517, 41, 265, 49, 273, 289, 769, 14, 134, 202, 266, 386, 642, 770, 60, 76, 84, 532, 196, 644, 104, 328, 112, 304, 560, 592, 784, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_789, vertices_361, vertices_305, vertices_206, vertices_458, vertices_898, vertices_124, vertices_724, vertices_624, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_273, vertices_289, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_532, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_304, vertices_560, vertices_592, vertices_784, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_789), (false, vertices_361), (false, vertices_305), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 21 16 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1168

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1169.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1169

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 203, 789, 121, 721, 782, 458, 898, 364, 308, 240, 944, 480, 7, 11, 131, 21, 517, 57, 73, 81, 529, 193, 641, 14, 518, 202, 266, 386, 642, 770, 44, 268, 52, 276, 292, 772, 104, 328, 112, 176, 304, 208, 656, 784, 224, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_203, vertices_789, vertices_121, vertices_721, vertices_782, vertices_458, vertices_898, vertices_364, vertices_308, vertices_240, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_641, vertices_14, vertices_518, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_772, vertices_104, vertices_328, vertices_112, vertices_176, vertices_304, vertices_208, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_328), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 3 4 6 7 8 944 176 3
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 364
cert_cover_5 3 3 1 2 4 5 44 364 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 240
cert_cover_2 5 4 3 5 6 112 240 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 176 944 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1169

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1170.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1170

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 661, 361, 817, 206, 902, 458, 124, 212, 752, 480, 928, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 518, 202, 266, 386, 770, 60, 76, 84, 148, 196, 644, 104, 328, 112, 560, 208, 656, 224, 352, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_752, vertices_480, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_560, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 21 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_2 1 0 2 5 6 202
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 7 202 458 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 480
cert_cover_2 6 5 4 6 7 224 480 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1170

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1171.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1171

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 661, 361, 817, 206, 902, 458, 124, 212, 752, 864, 960, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 518, 202, 266, 386, 770, 60, 76, 84, 148, 196, 644, 104, 328, 112, 560, 208, 656, 352, 608, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_752, vertices_864, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_560, vertices_208, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 21 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_2 1 0 2 5 6 202
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 7 202 458 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1171

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1172.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1172

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 661, 361, 817, 206, 902, 458, 124, 212, 624, 720, 992, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 518, 202, 266, 386, 770, 60, 76, 84, 148, 196, 644, 104, 328, 112, 560, 208, 592, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_624, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 21 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 3 2 0 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 902
cert_cover_5 1 2 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 7 202 458 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1172

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1173.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1173

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 661, 361, 817, 206, 902, 458, 124, 212, 240, 688, 992, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 518, 202, 266, 386, 770, 60, 76, 84, 148, 196, 644, 104, 328, 112, 176, 560, 208, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_240, vertices_688, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 21 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 2 0 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 902
cert_cover_5 1 2 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 7 202 458 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 240
cert_cover_2 5 4 3 5 6 112 240 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1173

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1174.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1174

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 540, 724, 696, 424, 904, 496, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 532, 196, 644, 56, 536, 168, 296, 392, 648, 776, 112, 176, 208, 656, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_696, vertices_424, vertices_904, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_117) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority 1 518 2 524 0 532 644 536 168 392 648 176 208 656 416 896 117 63 779 361 199 451
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1174

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1175.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1175

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 540, 724, 696, 808, 496, 928, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 532, 196, 644, 56, 536, 296, 552, 776, 112, 176, 208, 656, 352, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_696, vertices_808, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_117) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority 1 518 2 524 0 532 644 536 552 176 208 656 416 672 800 896 117 63 779 361 199 451
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1175

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1176.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1176

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 540, 724, 568, 936, 496, 688, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 532, 196, 644, 56, 536, 296, 552, 776, 112, 176, 560, 208, 656, 352, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_568, vertices_936, vertices_496, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_117) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority 1 518 2 524 0 532 644 536 552 176 560 208 656 416 672 896 117 63 779 361 199 451
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 4 6 7 8 936 296 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 936
cert_cover_5 5 2 2 4 6 7 296 936 2
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1176

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1177.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1177

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 540, 724, 184, 664, 936, 496, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 532, 196, 644, 56, 152, 536, 168, 296, 648, 776, 112, 176, 208, 656, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_184, vertices_664, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_117) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority 1 518 2 524 0 532 644 152 536 168 648 176 208 656 416 896 117 63 779 361 199 451
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 4 6 7 8 936 168 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 664
cert_cover_2 5 3 2 6 8 152 664 3
cert_coverFacet 6 936
cert_cover_5 6 2 2 4 6 7 168 936 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1177

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1178.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1178

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 779, 597, 425, 817, 270, 326, 962, 124, 460, 232, 752, 928, 7, 11, 515, 21, 581, 41, 265, 49, 529, 289, 769, 14, 70, 262, 266, 322, 578, 770, 60, 76, 268, 84, 324, 104, 168, 200, 392, 112, 560, 592, 224, 416, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_779, vertices_597, vertices_425, vertices_817, vertices_270, vertices_326, vertices_962, vertices_124, vertices_460, vertices_232, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_581, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_578, vertices_770, vertices_60, vertices_76, vertices_268, vertices_84, vertices_324, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_779), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_262), (true, vertices_322), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 262 322 76 268 324 104 200 112 224 672 448 704 896 779 63 583 597 425 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 322 2
cert_row_4 1 1 2 5 6 7 460 76 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 322 962 2
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 460
cert_cover_5 4 1 1 2 5 6 76 460 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1178

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1179.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1179

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 779, 597, 425, 177, 913, 270, 326, 962, 124, 460, 232, 752, 7, 11, 515, 21, 581, 41, 265, 49, 145, 529, 161, 385, 769, 14, 70, 262, 266, 322, 578, 770, 60, 76, 268, 84, 324, 104, 168, 200, 392, 112, 176, 592, 656, 224, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_779, vertices_597, vertices_425, vertices_177, vertices_913, vertices_270, vertices_326, vertices_962, vertices_124, vertices_460, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_581, vertices_41, vertices_265, vertices_49, vertices_145, vertices_529, vertices_161, vertices_385, vertices_769, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_578, vertices_770, vertices_60, vertices_76, vertices_268, vertices_84, vertices_324, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_779), (false, vertices_597), (false, vertices_425), (false, vertices_177), (false, vertices_913), (true, vertices_262), (true, vertices_322), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_224), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 322 2
cert_row_4 1 1 2 5 6 7 460 76 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 322 962 2
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 460
cert_cover_5 4 1 1 2 5 6 76 460 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1179

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1180.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1180

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 267, 341, 121, 457, 654, 394, 962, 684, 820, 232, 752, 848, 7, 11, 259, 21, 261, 57, 73, 265, 81, 321, 14, 518, 138, 266, 386, 642, 770, 44, 652, 52, 276, 548, 772, 104, 168, 200, 392, 112, 560, 336, 592, 784, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_267, vertices_341, vertices_121, vertices_457, vertices_654, vertices_394, vertices_962, vertices_684, vertices_820, vertices_232, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_265, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_267), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_138), (true, vertices_386), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_652) then 17 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 386 962 1
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1180

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1181.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1181

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 651, 789, 233, 689, 270, 394, 962, 124, 460, 340, 880, 736, 7, 11, 515, 21, 773, 41, 137, 49, 529, 161, 641, 14, 262, 138, 266, 386, 642, 770, 60, 76, 268, 84, 276, 324, 104, 200, 392, 112, 560, 336, 784, 224, 608, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_651, vertices_789, vertices_233, vertices_689, vertices_270, vertices_394, vertices_962, vertices_124, vertices_460, vertices_340, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_773, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_641, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_268, vertices_84, vertices_276, vertices_324, vertices_104, vertices_200, vertices_392, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_651), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_266), (true, vertices_386), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_324), (true, vertices_392), (true, vertices_112), (true, vertices_336), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 266 386 76 268 84 324 392 112 336 608 448 704 832 651 63 775 789 233 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_4 1 1 2 5 6 7 460 76 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 386 962 1
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 460
cert_cover_5 4 1 1 2 5 6 76 460 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1181

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1196.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1196

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 651, 771, 789, 233, 689, 398, 962, 124, 460, 340, 880, 736, 7, 11, 259, 515, 21, 261, 41, 137, 49, 529, 161, 641, 769, 14, 262, 138, 386, 642, 770, 60, 76, 396, 84, 276, 324, 104, 200, 112, 560, 336, 784, 224, 608, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_651, vertices_771, vertices_789, vertices_233, vertices_689, vertices_398, vertices_962, vertices_124, vertices_460, vertices_340, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_21, vertices_261, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_396, vertices_84, vertices_276, vertices_324, vertices_104, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_651), (false, vertices_771), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_386), (true, vertices_76), (true, vertices_396), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_2 1 1 2 6 7 396
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 386 962 1
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 5 60 124 3
cert_coverFacet 3 460
cert_cover_5 3 1 1 2 5 6 76 460 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1196

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1197.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1197

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 651, 117, 453, 233, 270, 778, 962, 284, 852, 824, 680, 752, 7, 11, 131, 53, 69, 389, 41, 137, 97, 193, 14, 262, 266, 522, 386, 642, 770, 28, 268, 84, 276, 324, 56, 280, 168, 552, 648, 776, 112, 560, 592, 784, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_651, vertices_117, vertices_453, vertices_233, vertices_270, vertices_778, vertices_962, vertices_284, vertices_852, vertices_824, vertices_680, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_389, vertices_41, vertices_137, vertices_97, vertices_193, vertices_14, vertices_262, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_84, vertices_276, vertices_324, vertices_56, vertices_280, vertices_168, vertices_552, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_651), (false, vertices_117), (false, vertices_453), (false, vertices_233), (true, vertices_266), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 20 15 17 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_391) then 21 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_233) then 16 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 386 962 1
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 84 852 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 680
cert_cover_2 6 4 2 6 8 168 680 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1197

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1198.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1198

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 651, 789, 233, 689, 398, 774, 962, 124, 460, 340, 880, 736, 7, 11, 515, 21, 517, 41, 137, 49, 529, 161, 641, 14, 262, 518, 138, 386, 642, 770, 60, 76, 396, 84, 276, 324, 772, 104, 200, 112, 560, 336, 784, 224, 608, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_789, vertices_233, vertices_689, vertices_398, vertices_774, vertices_962, vertices_124, vertices_460, vertices_340, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_641, vertices_14, vertices_262, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_396, vertices_84, vertices_276, vertices_324, vertices_772, vertices_104, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_262), (true, vertices_386), (true, vertices_770), (true, vertices_76), (true, vertices_396), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_396) then 18 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_2 1 1 2 6 7 396
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 386 962 1
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 460
cert_cover_5 4 1 1 2 5 6 76 460 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1198

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1199.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1199

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 651, 277, 233, 689, 785, 398, 962, 124, 460, 340, 880, 736, 7, 11, 515, 21, 261, 41, 137, 49, 273, 529, 161, 641, 769, 14, 262, 138, 386, 642, 770, 60, 76, 396, 84, 276, 324, 104, 200, 112, 560, 336, 784, 224, 608, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_651, vertices_277, vertices_233, vertices_689, vertices_785, vertices_398, vertices_962, vertices_124, vertices_460, vertices_340, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_261, vertices_41, vertices_137, vertices_49, vertices_273, vertices_529, vertices_161, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_396, vertices_84, vertices_276, vertices_324, vertices_104, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_651), (false, vertices_277), (false, vertices_233), (false, vertices_689), (false, vertices_785), (true, vertices_386), (true, vertices_76), (true, vertices_396), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_2 1 1 2 6 7 396
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 386 962 1
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 5 60 124 3
cert_coverFacet 3 460
cert_cover_5 3 1 1 2 5 6 76 460 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1199

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1200.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1200

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 651, 277, 233, 817, 673, 398, 962, 124, 460, 340, 752, 848, 7, 11, 515, 21, 261, 41, 137, 49, 273, 161, 545, 641, 769, 14, 262, 138, 386, 642, 770, 60, 76, 396, 84, 276, 324, 104, 200, 112, 560, 336, 592, 784, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_651, vertices_277, vertices_233, vertices_817, vertices_673, vertices_398, vertices_962, vertices_124, vertices_460, vertices_340, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_261, vertices_41, vertices_137, vertices_49, vertices_273, vertices_161, vertices_545, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_396, vertices_84, vertices_276, vertices_324, vertices_104, vertices_200, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_651), (false, vertices_277), (false, vertices_233), (false, vertices_817), (false, vertices_673), (true, vertices_386), (true, vertices_76), (true, vertices_396), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_592), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_2 1 1 2 6 7 396
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 386 962 1
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 5 60 124 3
cert_coverFacet 3 460
cert_cover_5 3 1 1 2 5 6 76 460 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1200

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1201.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1201

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 341, 121, 457, 654, 962, 556, 820, 232, 680, 752, 848, 7, 11, 259, 21, 261, 57, 73, 393, 81, 321, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 548, 772, 104, 168, 552, 200, 648, 112, 560, 336, 592, 784, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_341, vertices_121, vertices_457, vertices_654, vertices_962, vertices_556, vertices_820, vertices_232, vertices_680, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_393, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 20 17 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_395) then 21 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1201

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1213.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1213

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 233, 961, 94, 838, 340, 916, 120, 496, 7, 11, 515, 53, 133, 41, 73, 161, 193, 577, 641, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 104, 112, 176, 336, 400, 224, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_233, vertices_961, vertices_94, vertices_838, vertices_340, vertices_916, vertices_120, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_193, vertices_577, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_233), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_112), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_647) then 10 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_233) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 340
cert_cover_2 2 3 1 5 7 84 340 3
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 148 916 3
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1213

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1231.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1231

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 523, 835, 181, 809, 481, 94, 586, 468, 440, 856, 7, 11, 67, 515, 53, 133, 41, 521, 161, 289, 193, 321, 769, 30, 70, 74, 522, 578, 84, 148, 196, 56, 88, 280, 296, 584, 776, 176, 336, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_523, vertices_835, vertices_181, vertices_809, vertices_481, vertices_94, vertices_586, vertices_468, vertices_440, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_53, vertices_133, vertices_41, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_769, vertices_30, vertices_70, vertices_74, vertices_522, vertices_578, vertices_84, vertices_148, vertices_196, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_523), (false, vertices_835), (false, vertices_181), (false, vertices_809), (false, vertices_481), (true, vertices_74), (true, vertices_84), (true, vertices_88), (true, vertices_280), (true, vertices_584), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_835) then 10 else
  if p.val = (false, vertices_181) then 13 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_481) then 18 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 856
cert_cover_5 4 3 2 3 5 7 88 856 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1231

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1232.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1232

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 195, 805, 369, 961, 206, 188, 676, 472, 944, 7, 27, 67, 131, 37, 517, 49, 81, 289, 193, 321, 641, 769, 14, 134, 74, 194, 60, 140, 164, 548, 644, 88, 152, 200, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_195, vertices_805, vertices_369, vertices_961, vertices_206, vertices_188, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_140), (true, vertices_164), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_647) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_369) then 16 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 188
cert_cover_5 1 1 1 2 3 6 60 188 3
cert_coverFacet 2 676
cert_cover_2 2 4 1 6 8 164 676 3
cert_coverFacet 3 472
cert_cover_5 3 2 2 3 5 6 88 472 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1232

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1410 : Certifies 1410 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1161.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1411 : Certifies 1411 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1162.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1412 : Certifies 1412 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1163.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1413 : Certifies 1413 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1164.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1414 : Certifies 1414 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1165.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1415 : Certifies 1415 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1166.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1416 : Certifies 1416 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1167.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1417 : Certifies 1417 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1168.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1418 : Certifies 1418 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1169.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1419 : Certifies 1419 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1170.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1420 : Certifies 1420 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1171.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1421 : Certifies 1421 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1172.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1422 : Certifies 1422 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1173.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1423 : Certifies 1423 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1174.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1424 : Certifies 1424 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1175.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1425 : Certifies 1425 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1176.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1426 : Certifies 1426 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1177.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1427 : Certifies 1427 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1178.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1428 : Certifies 1428 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1179.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1429 : Certifies 1429 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1180.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1430 : Certifies 1430 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1181.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1431 : Certifies 1431 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1196.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1432 : Certifies 1432 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1197.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1433 : Certifies 1433 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1198.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1434 : Certifies 1434 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1199.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1435 : Certifies 1435 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1200.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1436 : Certifies 1436 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1201.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1437 : Certifies 1437 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1213.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1438 : Certifies 1438 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1231.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1439 : Certifies 1439 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1232.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B047 (j : Fin 30) :
    Certifies (1410 + j.val) := by
  fin_cases j
  · exact projection_1410
  · exact projection_1411
  · exact projection_1412
  · exact projection_1413
  · exact projection_1414
  · exact projection_1415
  · exact projection_1416
  · exact projection_1417
  · exact projection_1418
  · exact projection_1419
  · exact projection_1420
  · exact projection_1421
  · exact projection_1422
  · exact projection_1423
  · exact projection_1424
  · exact projection_1425
  · exact projection_1426
  · exact projection_1427
  · exact projection_1428
  · exact projection_1429
  · exact projection_1430
  · exact projection_1431
  · exact projection_1432
  · exact projection_1433
  · exact projection_1434
  · exact projection_1435
  · exact projection_1436
  · exact projection_1437
  · exact projection_1438
  · exact projection_1439

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
