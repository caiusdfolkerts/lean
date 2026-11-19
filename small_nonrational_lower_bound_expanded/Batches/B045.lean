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
/- Source: ProjectionCertificates/R_one_six_1058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 523, 405, 617, 817, 206, 390, 906, 124, 212, 968, 496, 864, 7, 11, 515, 21, 261, 41, 521, 49, 273, 545, 769, 14, 134, 262, 138, 522, 386, 770, 60, 76, 84, 148, 196, 388, 104, 200, 584, 904, 112, 304, 208, 400, 352, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_523, vertices_405, vertices_617, vertices_817, vertices_206, vertices_390, vertices_906, vertices_124, vertices_212, vertices_968, vertices_496, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_261, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_134, vertices_262, vertices_138, vertices_522, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_388, vertices_104, vertices_200, vertices_584, vertices_904, vertices_112, vertices_304, vertices_208, vertices_400, vertices_352, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_523), (false, vertices_405), (false, vertices_617), (false, vertices_817), (true, vertices_134), (true, vertices_138), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_200), (true, vertices_904), (true, vertices_112), (true, vertices_208), (true, vertices_352), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_904) then 20 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_904), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 6 7 8 904
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 138 906 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 968
cert_cover_5 5 0 2 5 6 7 200 968 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1058

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 789, 121, 465, 526, 906, 684, 628, 232, 848, 992, 7, 11, 131, 259, 21, 773, 57, 73, 81, 273, 193, 385, 14, 518, 138, 522, 386, 770, 44, 524, 52, 532, 548, 104, 168, 200, 648, 112, 336, 592, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_789, vertices_121, vertices_465, vertices_526, vertices_906, vertices_684, vertices_628, vertices_232, vertices_848, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_773, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_522), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_648), (true, vertices_592), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1059

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1067.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1067

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 149, 121, 721, 270, 906, 364, 692, 932, 712, 840, 880, 7, 11, 131, 21, 133, 57, 73, 81, 145, 193, 14, 262, 138, 266, 386, 44, 268, 52, 148, 676, 292, 388, 104, 200, 328, 584, 648, 776, 112, 560, 592, 656, 352, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_149, vertices_121, vertices_721, vertices_270, vertices_906, vertices_364, vertices_692, vertices_932, vertices_712, vertices_840, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_148, vertices_676, vertices_292, vertices_388, vertices_104, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_656, vertices_352, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_149), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_676), (true, vertices_292), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_352), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_676) then 17 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_2 1 1 4 6 8 676
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 44 364 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 7 676 932 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1067

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 661, 121, 721, 270, 906, 364, 564, 932, 712, 840, 880, 7, 11, 131, 21, 133, 57, 73, 81, 657, 193, 14, 262, 138, 266, 386, 44, 268, 52, 532, 292, 548, 388, 644, 104, 200, 328, 584, 648, 776, 112, 560, 592, 352, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_661, vertices_121, vertices_721, vertices_270, vertices_906, vertices_364, vertices_564, vertices_932, vertices_712, vertices_840, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_657, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_548, vertices_388, vertices_644, vertices_104, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_661), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_352), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 17 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_4 2 1 4 6 7 8 932 292 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 5 44 364 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 932
cert_cover_5 4 2 1 4 6 7 292 932 2
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1068

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1069.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1069

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 597, 709, 121, 270, 906, 300, 308, 916, 744, 808, 880, 7, 11, 131, 21, 581, 133, 57, 73, 81, 193, 14, 262, 138, 266, 386, 44, 268, 52, 276, 532, 292, 388, 644, 104, 296, 552, 200, 648, 776, 112, 304, 592, 784, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_597, vertices_709, vertices_121, vertices_270, vertices_906, vertices_300, vertices_308, vertices_916, vertices_744, vertices_808, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_581, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_292, vertices_388, vertices_644, vertices_104, vertices_296, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_592, vertices_784, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_597), (false, vertices_709), (false, vertices_121), (true, vertices_266), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_296), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_784), (true, vertices_608), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 20 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 3 6 7 8 916 276 2
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 276 916 2
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1069

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 149, 121, 721, 782, 906, 620, 436, 804, 712, 880, 912, 7, 11, 131, 21, 133, 57, 73, 81, 145, 193, 14, 262, 138, 778, 386, 44, 524, 52, 148, 292, 548, 388, 772, 104, 200, 584, 648, 112, 304, 592, 400, 656, 784, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_149, vertices_121, vertices_721, vertices_782, vertices_906, vertices_620, vertices_436, vertices_804, vertices_712, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_148, vertices_292, vertices_548, vertices_388, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_592, vertices_400, vertices_656, vertices_784, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_149), (false, vertices_121), (false, vertices_721), (true, vertices_778), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_584), (true, vertices_648), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_608), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 22 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (true, vertices_778) then 21 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 52 436 3
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1074

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 270, 906, 812, 628, 232, 680, 976, 736, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 168, 552, 200, 648, 776, 112, 464, 592, 784, 224, 608, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_270, vertices_906, vertices_812, vertices_628, vertices_232, vertices_680, vertices_976, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_592), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_2 1 3 5 6 7 464
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 52 628 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 8 464 976 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1075

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 270, 906, 812, 564, 852, 232, 680, 752, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 266, 386, 44, 268, 52, 340, 532, 548, 772, 104, 168, 552, 200, 648, 776, 112, 560, 592, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_270, vertices_906, vertices_812, vertices_564, vertices_852, vertices_232, vertices_680, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_340, vertices_532, vertices_548, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_266), (true, vertices_268), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_2 2 1 3 5 7 340
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 8 340 852 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 680
cert_cover_2 6 4 2 6 8 168 680 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1076

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1077.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 270, 906, 812, 820, 232, 680, 752, 848, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 266, 386, 44, 268, 52, 276, 804, 104, 168, 552, 200, 648, 776, 112, 560, 336, 592, 784, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_270, vertices_906, vertices_812, vertices_820, vertices_232, vertices_680, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_804, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_266), (true, vertices_268), (true, vertices_804), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_804) then 16 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 3 4 5 6 8 752 112 3
cert_rows_3
cert_pivot_3 0 1 3
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 752
cert_cover_5 6 2 3 4 5 6 112 752 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1077

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1078.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 270, 906, 300, 628, 804, 744, 808, 976, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 532, 292, 548, 772, 104, 296, 552, 200, 648, 776, 112, 464, 592, 784, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_270, vertices_906, vertices_300, vertices_628, vertices_804, vertices_744, vertices_808, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_548, vertices_772, vertices_104, vertices_296, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_592), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_2 1 3 5 6 7 464
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 8 464 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1078

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1079.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1079

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 277, 121, 721, 913, 270, 906, 812, 372, 744, 848, 864, 7, 11, 131, 21, 261, 57, 73, 81, 657, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 276, 292, 104, 552, 200, 648, 776, 112, 336, 592, 784, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_277, vertices_121, vertices_721, vertices_913, vertices_270, vertices_906, vertices_812, vertices_372, vertices_744, vertices_848, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_657, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_336, vertices_592, vertices_784, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_721), (false, vertices_913), (true, vertices_266), (true, vertices_268), (true, vertices_292), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_336), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 16 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 3 4 5 7 372 52 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 52 372 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1079

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1080.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1080

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 270, 906, 812, 116, 596, 612, 744, 976, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 84, 532, 100, 548, 580, 772, 104, 552, 200, 648, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_270, vertices_906, vertices_812, vertices_116, vertices_596, vertices_612, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_84, vertices_532, vertices_100, vertices_548, vertices_580, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 3 5 6 7 464
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 596
cert_cover_2 4 3 1 5 8 84 596 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 8 464 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1080

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1081.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1081

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 277, 121, 721, 913, 270, 906, 812, 116, 852, 612, 744, 7, 11, 131, 21, 261, 57, 73, 81, 657, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 84, 276, 100, 548, 580, 772, 104, 552, 200, 648, 776, 112, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_277, vertices_121, vertices_721, vertices_913, vertices_270, vertices_906, vertices_812, vertices_116, vertices_852, vertices_612, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_657, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_84, vertices_276, vertices_100, vertices_548, vertices_580, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_721), (false, vertices_913), (true, vertices_266), (true, vertices_268), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 16 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 84 852 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1081

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1082.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1082

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 398, 540, 780, 468, 788, 632, 976, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 266, 386, 28, 268, 524, 84, 276, 532, 196, 388, 772, 56, 536, 552, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_398, vertices_540, vertices_780, vertices_468, vertices_788, vertices_632, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_772), (true, vertices_536), (true, vertices_464), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_464) then 19 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 3 5 6 7 464
cert_row_4 2 2 3 4 5 8 632 56 3
cert_rows_3
cert_pivot_3 6 0 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 540
cert_cover_2 1 2 1 3 8 28 540 3
cert_coverFacet 2 780
cert_cover_2 2 2 1 7 8 268 780 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1082

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1083.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1083

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 782, 906, 556, 820, 232, 680, 752, 848, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 168, 552, 200, 648, 112, 560, 336, 592, 784, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_782, vertices_906, vertices_556, vertices_820, vertices_232, vertices_680, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 11 20 14 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_778) then 19 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 3 4 5 6 8 752 112 3
cert_rows_3
cert_pivot_3 1 0 3
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 752
cert_cover_5 6 2 3 4 5 6 112 752 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1083

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1084.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1084

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 556, 628, 232, 680, 848, 992, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 168, 552, 200, 648, 112, 336, 592, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_556, vertices_628, vertices_232, vertices_680, vertices_848, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_592), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 11 21 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_778) then 20 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 1 0 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 52 628 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coverFacet 7 992
cert_cover_5 7 2 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1084

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1085.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1085

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 620, 564, 712, 368, 816, 992, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 200, 584, 648, 112, 304, 560, 336, 784, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_620, vertices_564, vertices_712, vertices_368, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_304), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 11 21 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_778) then 20 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_584) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 4 5 6 7 8 992 352 2
cert_rows_3
cert_pivot_3 1 0 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 992
cert_cover_5 7 2 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1085

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1086.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1086

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 620, 564, 712, 240, 944, 736, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 200, 584, 648, 112, 176, 560, 208, 400, 784, 224, 608, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_620, vertices_564, vertices_712, vertices_240, vertices_944, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 11 21 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_778) then 20 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_584) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 3 4 6 7 8 944 176 3
cert_rows_3
cert_pivot_3 1 0 3
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 240
cert_cover_2 5 4 3 5 6 112 240 3
cert_coverFacet 6 944
cert_cover_5 6 2 3 4 6 7 176 944 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1086

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 405, 121, 721, 270, 906, 812, 372, 744, 848, 912, 864, 7, 11, 131, 21, 389, 57, 73, 81, 145, 193, 14, 262, 138, 266, 386, 44, 268, 52, 276, 292, 104, 552, 200, 648, 776, 112, 336, 592, 400, 656, 784, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_405, vertices_121, vertices_721, vertices_270, vertices_906, vertices_812, vertices_372, vertices_744, vertices_848, vertices_912, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_389, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_405), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_292), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_336), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 266 1 268 2 292 552 648 776 336 784 352 608 800 832 896 203 391 405 63 121 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 3 4 5 7 372 52 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 52 372 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1087

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1088.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1088

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 405, 121, 721, 270, 906, 812, 116, 852, 612, 744, 912, 7, 11, 131, 21, 389, 57, 73, 81, 145, 193, 14, 262, 138, 266, 386, 44, 268, 52, 84, 276, 100, 548, 580, 772, 104, 552, 200, 648, 776, 112, 592, 400, 656, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_405, vertices_121, vertices_721, vertices_270, vertices_906, vertices_812, vertices_116, vertices_852, vertices_612, vertices_744, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_389, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_84, vertices_276, vertices_100, vertices_548, vertices_580, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_400, vertices_656, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_405), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_784), (true, vertices_608), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 266 1 268 2 84 100 548 580 772 552 648 776 784 608 896 203 391 405 63 121 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 84 852 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1088

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1090.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 297, 225, 929, 270, 326, 962, 604, 844, 824, 752, 7, 11, 131, 53, 69, 41, 265, 97, 161, 289, 193, 385, 14, 70, 262, 266, 194, 322, 386, 28, 588, 268, 84, 324, 56, 536, 296, 776, 112, 560, 592, 224, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_297, vertices_225, vertices_929, vertices_270, vertices_326, vertices_962, vertices_604, vertices_844, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_588, vertices_268, vertices_84, vertices_324, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_297), (false, vertices_225), (false, vertices_929), (true, vertices_262), (true, vertices_322), (true, vertices_588), (true, vertices_268), (true, vertices_324), (true, vertices_536), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_588) then 18 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_2 0 1 2 5 8 588
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 28 604 3
cert_coverFacet 4 844
cert_cover_5 4 0 1 2 5 7 588 844 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1090

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1091.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1091

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 341, 121, 526, 906, 450, 684, 820, 232, 752, 976, 7, 11, 67, 259, 21, 261, 57, 73, 81, 321, 14, 518, 138, 522, 194, 322, 386, 770, 44, 524, 52, 276, 548, 772, 104, 168, 200, 648, 112, 560, 720, 336, 784, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_341, vertices_121, vertices_526, vertices_906, vertices_450, vertices_684, vertices_820, vertices_232, vertices_752, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_522, vertices_194, vertices_322, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_560, vertices_720, vertices_336, vertices_784, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_341), (false, vertices_121), (true, vertices_522), (true, vertices_386), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_720), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_720) then 22 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 752
cert_cover_5 6 0 3 4 5 6 112 752 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1091

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1092.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1092

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 341, 121, 526, 906, 450, 556, 692, 916, 744, 496, 7, 11, 67, 259, 21, 261, 57, 73, 81, 321, 14, 518, 138, 522, 194, 322, 386, 770, 44, 524, 52, 660, 276, 548, 772, 104, 552, 200, 648, 112, 176, 336, 400, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_341, vertices_121, vertices_526, vertices_906, vertices_450, vertices_556, vertices_692, vertices_916, vertices_744, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_522, vertices_194, vertices_322, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_660, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_341), (false, vertices_121), (true, vertices_522), (true, vertices_386), (true, vertices_524), (true, vertices_660), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 16 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_660) then 21 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 8 660
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 692
cert_cover_5 4 0 1 3 4 6 52 692 3
cert_coverFacet 5 916
cert_cover_5 5 0 1 3 6 7 660 916 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1092

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1093.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1093

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 653, 961, 342, 122, 172, 692, 788, 488, 368, 944, 7, 11, 67, 259, 13, 517, 137, 193, 321, 641, 769, 22, 262, 58, 74, 82, 322, 44, 140, 52, 276, 532, 164, 644, 772, 104, 168, 200, 112, 688, 304, 336, 784, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_653, vertices_961, vertices_342, vertices_122, vertices_172, vertices_692, vertices_788, vertices_488, vertices_368, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_517, vertices_137, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_532, vertices_164, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_688, vertices_304, vertices_336, vertices_784, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_688), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_688) then 21 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 323 82 276 532 164 104 168 112 304 336 784 352 416 775 203 653 688
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 8 688
cert_row_4 1 0 1 3 5 7 342 22 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 22 342 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 692
cert_cover_5 3 0 1 3 4 6 52 692 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coverFacet 7 944
cert_cover_5 7 0 3 4 6 7 688 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1093

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1094.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1094

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 341, 121, 654, 962, 684, 564, 788, 488, 368, 944, 7, 11, 67, 259, 21, 261, 57, 73, 81, 321, 14, 518, 138, 194, 322, 642, 770, 44, 652, 52, 276, 532, 548, 772, 104, 168, 200, 112, 304, 560, 336, 784, 352, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_341, vertices_121, vertices_654, vertices_962, vertices_684, vertices_564, vertices_788, vertices_488, vertices_368, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_341), (false, vertices_121), (true, vertices_642), (true, vertices_652), (true, vertices_532), (true, vertices_548), (true, vertices_168), (true, vertices_304), (true, vertices_560), (true, vertices_784), (true, vertices_352), (true, vertices_416), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 20 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_652) then 18 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 488
cert_cover_5 5 2 2 4 5 6 104 488 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1094

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1118.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1118

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 598, 122, 172, 436, 788, 836, 744, 624, 944, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 70, 58, 74, 82, 44, 140, 52, 276, 532, 164, 324, 580, 388, 772, 104, 168, 200, 112, 432, 560, 592, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_598, vertices_122, vertices_172, vertices_436, vertices_788, vertices_836, vertices_744, vertices_624, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_58, vertices_74, vertices_82, vertices_44, vertices_140, vertices_52, vertices_276, vertices_532, vertices_164, vertices_324, vertices_580, vertices_388, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_432, vertices_560, vertices_592, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_580), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_432) then 22 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_46 82 276 532 164 580 772 104 168 112 560 592 784 608 672 327 203 397 432
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 22 598 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 436
cert_cover_5 3 0 1 3 4 6 52 436 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coverFacet 8 944
cert_cover_5 8 0 3 4 6 8 432 944 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1118

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1119.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1119

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 597, 121, 398, 962, 428, 308, 788, 836, 744, 624, 944, 7, 11, 67, 21, 69, 57, 73, 81, 14, 262, 138, 194, 322, 386, 44, 396, 52, 276, 532, 292, 324, 580, 772, 104, 168, 200, 112, 304, 560, 592, 784, 608, 416, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_597, vertices_121, vertices_398, vertices_962, vertices_428, vertices_308, vertices_788, vertices_836, vertices_744, vertices_624, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_57, vertices_73, vertices_81, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_276, vertices_532, vertices_292, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_304, vertices_560, vertices_592, vertices_784, vertices_608, vertices_416, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_597), (false, vertices_121), (true, vertices_386), (true, vertices_396), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_304), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 21 else
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_396) then 19 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 428
cert_cover_5 2 0 1 2 4 6 44 428 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coverFacet 8 944
cert_cover_5 8 3 3 4 6 7 304 944 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1119

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1121.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1121

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 789, 121, 337, 782, 906, 450, 556, 692, 744, 496, 912, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 778, 194, 322, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 176, 336, 400, 656, 784, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_789, vertices_121, vertices_337, vertices_782, vertices_906, vertices_450, vertices_556, vertices_692, vertices_744, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_778, vertices_194, vertices_322, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_337), (true, vertices_778), (true, vertices_386), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 22 16 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_203) then 20 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_778) then 21 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1121

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1122.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1122

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 782, 906, 450, 684, 820, 232, 752, 960, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 778, 194, 322, 386, 44, 524, 52, 276, 548, 772, 104, 168, 200, 648, 112, 560, 592, 784, 224, 672, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_782, vertices_906, vertices_450, vertices_684, vertices_820, vertices_232, vertices_752, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_778, vertices_194, vertices_322, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_778), (true, vertices_386), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 22 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_203) then 20 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_778) then 21 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1122

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1123.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1123

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 270, 394, 962, 684, 908, 820, 232, 752, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 266, 194, 322, 386, 44, 652, 268, 52, 276, 548, 772, 104, 168, 200, 392, 112, 560, 592, 784, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_270, vertices_394, vertices_962, vertices_684, vertices_908, vertices_820, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_652, vertices_268, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_266), (true, vertices_386), (true, vertices_652), (true, vertices_268), (true, vertices_548), (true, vertices_772), (true, vertices_168), (true, vertices_392), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_652) then 17 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 908
cert_cover_5 4 0 1 2 6 7 652 908 3
cert_coverFacet 5 820
cert_cover_5 5 2 1 3 4 7 52 820 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1123

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1350 : Certifies 1350 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1351 : Certifies 1351 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1352 : Certifies 1352 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1067.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1353 : Certifies 1353 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1354 : Certifies 1354 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1069.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1355 : Certifies 1355 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1356 : Certifies 1356 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1357 : Certifies 1357 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1358 : Certifies 1358 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1077.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1359 : Certifies 1359 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1078.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1360 : Certifies 1360 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1079.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1361 : Certifies 1361 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1080.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1362 : Certifies 1362 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1081.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1363 : Certifies 1363 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1082.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1364 : Certifies 1364 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1083.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1365 : Certifies 1365 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1084.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1366 : Certifies 1366 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1085.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1367 : Certifies 1367 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1086.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1368 : Certifies 1368 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1369 : Certifies 1369 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1088.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1370 : Certifies 1370 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1090.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1371 : Certifies 1371 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1091.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1372 : Certifies 1372 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1092.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1373 : Certifies 1373 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1093.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1374 : Certifies 1374 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1094.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1375 : Certifies 1375 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1118.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1376 : Certifies 1376 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1119.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1377 : Certifies 1377 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1121.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1378 : Certifies 1378 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1122.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1379 : Certifies 1379 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1123.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B045 (j : Fin 30) :
    Certifies (1350 + j.val) := by
  fin_cases j
  · exact projection_1350
  · exact projection_1351
  · exact projection_1352
  · exact projection_1353
  · exact projection_1354
  · exact projection_1355
  · exact projection_1356
  · exact projection_1357
  · exact projection_1358
  · exact projection_1359
  · exact projection_1360
  · exact projection_1361
  · exact projection_1362
  · exact projection_1363
  · exact projection_1364
  · exact projection_1365
  · exact projection_1366
  · exact projection_1367
  · exact projection_1368
  · exact projection_1369
  · exact projection_1370
  · exact projection_1371
  · exact projection_1372
  · exact projection_1373
  · exact projection_1374
  · exact projection_1375
  · exact projection_1376
  · exact projection_1377
  · exact projection_1378
  · exact projection_1379

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
