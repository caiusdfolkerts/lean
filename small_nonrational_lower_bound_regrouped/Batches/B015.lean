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
/- Source: ProjectionCertificates/R_m14e11q2_0087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 203, 643, 93, 285, 901, 425, 242, 562, 594, 930, 852, 248, 824, 67, 131, 515, 29, 69, 261, 517, 73, 137, 265, 385, 641, 50, 82, 530, 162, 546, 194, 578, 642, 84, 276, 580, 772, 56, 88, 280, 168, 296, 200, 240, 560, 592, 784, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_203, vertices_643, vertices_93, vertices_285, vertices_901, vertices_425, vertices_242, vertices_562, vertices_594, vertices_930, vertices_852, vertices_248, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_29, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_385, vertices_641, vertices_50, vertices_82, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_84, vertices_276, vertices_580, vertices_772, vertices_56, vertices_88, vertices_280, vertices_168, vertices_296, vertices_200, vertices_240, vertices_560, vertices_592, vertices_784, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_203), (false, vertices_643), (false, vertices_93), (false, vertices_285), (false, vertices_901), (false, vertices_425), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_56), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_285) then 16 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 8 930 162 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 1 0 3 4 5 50 242 3
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 930
cert_cover_5 3 0 0 4 6 7 162 930 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 248
cert_cover_5 5 1 2 3 4 5 56 248 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0087

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e11q2_0088.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0088

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [31, 557, 85, 229, 217, 169, 526, 342, 614, 666, 914, 866, 936, 496, 13, 21, 37, 69, 25, 41, 137, 81, 161, 193, 14, 22, 70, 518, 26, 522, 658, 274, 610, 322, 770, 524, 84, 100, 548, 152, 168, 552, 648, 208, 336, 400, 224, 352, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_31, vertices_557, vertices_85, vertices_229, vertices_217, vertices_169, vertices_526, vertices_342, vertices_614, vertices_666, vertices_914, vertices_866, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_69, vertices_25, vertices_41, vertices_137, vertices_81, vertices_161, vertices_193, vertices_14, vertices_22, vertices_70, vertices_518, vertices_26, vertices_522, vertices_658, vertices_274, vertices_610, vertices_322, vertices_770, vertices_524, vertices_84, vertices_100, vertices_548, vertices_152, vertices_168, vertices_552, vertices_648, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_31), (false, vertices_557), (false, vertices_85), (false, vertices_229), (false, vertices_217), (false, vertices_169), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_658), (true, vertices_274), (true, vertices_610), (true, vertices_322), (true, vertices_770), (true, vertices_648), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_416), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 23 15 19 21 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_31) then 16 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_658) then 22 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_610) then 24 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_31), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 23 => Sum.inl 0
  | 24 => Sum.inr ⟨(true, vertices_610), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 2 4 6 7 8 936 168 3
cert_row_4 2 3 4 5 6 7 496 208 1
cert_row_2 3 0 3 6 8 658
cert_row_2 4 0 4 5 8 610
cert_rows_2
cert_pivot 1 2 7 3 0
cert_heightProof 5
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 5 22 342 3
cert_coverFacet 2 614
cert_cover_5 2 4 0 1 4 5 70 614 2
cert_coverFacet 3 666
cert_cover_5 3 3 0 2 3 6 26 666 3
cert_coverFacet 4 914
cert_cover_5 4 3 0 3 6 7 658 914 3
cert_coverFacet 5 866
cert_cover_5 5 4 0 4 5 7 610 866 3
cert_coverFacet 6 936
cert_cover_5 6 1 2 4 6 7 168 936 3
cert_coverFacet 7 496
cert_cover_5 7 2 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0088

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e11q2_0089.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0089

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 557, 333, 901, 345, 817, 206, 654, 90, 554, 242, 930, 468, 432, 13, 261, 517, 25, 41, 329, 49, 273, 545, 769, 142, 26, 42, 74, 522, 50, 82, 162, 546, 194, 642, 76, 524, 196, 324, 388, 644, 88, 552, 176, 304, 208, 336, 400, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_557, vertices_333, vertices_901, vertices_345, vertices_817, vertices_206, vertices_654, vertices_90, vertices_554, vertices_242, vertices_930, vertices_468, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_25, vertices_41, vertices_329, vertices_49, vertices_273, vertices_545, vertices_769, vertices_142, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_82, vertices_162, vertices_546, vertices_194, vertices_642, vertices_76, vertices_524, vertices_196, vertices_324, vertices_388, vertices_644, vertices_88, vertices_552, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_557), (false, vertices_333), (false, vertices_901), (false, vertices_345), (false, vertices_817), (true, vertices_142), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_196), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 13 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_142) then 14 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 3 5 6 7 468 196 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 142 206 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 90
cert_cover_2 2 2 0 3 5 26 90 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 50 242 3
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 162 930 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 196 468 1
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0089

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e11q2_0090.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 583, 61, 805, 369, 961, 30, 398, 902, 186, 722, 300, 488, 240, 71, 21, 37, 517, 49, 81, 289, 321, 577, 769, 14, 22, 390, 518, 26, 138, 82, 146, 578, 642, 28, 44, 268, 292, 772, 56, 168, 296, 392, 112, 176, 208, 224, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_583, vertices_61, vertices_805, vertices_369, vertices_961, vertices_30, vertices_398, vertices_902, vertices_186, vertices_722, vertices_300, vertices_488, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_21, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_390, vertices_518, vertices_26, vertices_138, vertices_82, vertices_146, vertices_578, vertices_642, vertices_28, vertices_44, vertices_268, vertices_292, vertices_772, vertices_56, vertices_168, vertices_296, vertices_392, vertices_112, vertices_176, vertices_208, vertices_224, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_583), (false, vertices_61), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_14), (true, vertices_390), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_642), (true, vertices_268), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_176), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 22 24 12 14 16 18 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 19 else
  if p.val = (false, vertices_583) then 20 else
  if p.val = (false, vertices_61) then 13 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_369) then 15 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_390) then 23 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 0
  | 23 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 24 => Sum.inl 1
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 6 14 398 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 8 390 902 3
cert_coverFacet 3 186
cert_cover_5 3 2 0 2 3 4 26 186 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0090

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e11q2_0091.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0091

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 307, 707, 323, 345, 241, 673, 334, 590, 294, 412, 684, 436, 728, 35, 67, 259, 515, 49, 81, 273, 161, 545, 193, 321, 641, 78, 38, 262, 518, 290, 322, 578, 140, 268, 524, 404, 164, 292, 548, 88, 152, 280, 328, 584, 648, 176, 304, 208, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_307, vertices_707, vertices_323, vertices_345, vertices_241, vertices_673, vertices_334, vertices_590, vertices_294, vertices_412, vertices_684, vertices_436, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_49, vertices_81, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_78, vertices_38, vertices_262, vertices_518, vertices_290, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_404, vertices_164, vertices_292, vertices_548, vertices_88, vertices_152, vertices_280, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_208, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_307), (false, vertices_707), (false, vertices_323), (false, vertices_345), (false, vertices_241), (false, vertices_673), (true, vertices_78), (true, vertices_262), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_404), (true, vertices_164), (true, vertices_292), (true, vertices_152), (true, vertices_584), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 11 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_345) then 12 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_78) then 13 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_648) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 7 404
cert_row_2 1 0 1 2 5 78
cert_row_4 2 1 2 4 6 8 684 140 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 8 78 590 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 140 412 2
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 140 684 2
cert_coverFacet 5 436
cert_cover_5 5 0 1 3 4 6 404 436 2
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0091

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e11q2_0092.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0092

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 595, 613, 569, 409, 361, 710, 666, 402, 482, 812, 908, 228, 420, 83, 25, 41, 265, 273, 529, 97, 545, 321, 577, 146, 274, 530, 194, 322, 578, 386, 642, 780, 100, 164, 292, 548, 196, 580, 388, 644, 152, 536, 296, 552, 392, 648, 400, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_595, vertices_613, vertices_569, vertices_409, vertices_361, vertices_710, vertices_666, vertices_402, vertices_482, vertices_812, vertices_908, vertices_228, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_25, vertices_41, vertices_265, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_780, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_152, vertices_536, vertices_296, vertices_552, vertices_392, vertices_648, vertices_400, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_595), (false, vertices_613), (false, vertices_569), (false, vertices_409), (false, vertices_361), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_780), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_648), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_780) then 17 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 0 4 5 6 7 482 194 1
cert_rows
cert_pivot_2 3 2 1 0
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 146 666 1
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 194 482 1
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 7 780 812 2
cert_coverFacet 5 908
cert_cover_5 5 1 1 2 6 7 780 908 2
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0092

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e11q2_0097.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0097

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 781, 409, 713, 241, 337, 558, 118, 342, 774, 738, 428, 436, 680, 137, 265, 521, 81, 145, 273, 193, 321, 577, 769, 86, 38, 262, 518, 98, 546, 322, 578, 770, 44, 268, 524, 52, 276, 420, 772, 168, 552, 392, 648, 112, 176, 336, 400, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_781, vertices_409, vertices_713, vertices_241, vertices_337, vertices_558, vertices_118, vertices_342, vertices_774, vertices_738, vertices_428, vertices_436, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_769, vertices_86, vertices_38, vertices_262, vertices_518, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_420, vertices_772, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_781), (false, vertices_409), (false, vertices_713), (false, vertices_241), (false, vertices_337), (true, vertices_86), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_546), (true, vertices_44), (true, vertices_52), (true, vertices_276), (true, vertices_420), (true, vertices_168), (true, vertices_552), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_420) then 17 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 6 7 420
cert_row_2 1 0 1 3 5 86
cert_row_4 2 0 1 2 4 8 558 38 2
cert_row_4 3 0 4 5 6 8 738 98 3
cert_rows
cert_pivot_2 7 3 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 38 558 2
cert_coverFacet 1 118
cert_cover_5 1 1 0 1 3 4 86 118 3
cert_coverFacet 2 342
cert_cover_5 2 1 0 1 3 7 86 342 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 738
cert_cover_5 4 3 0 4 5 6 98 738 3
cert_coverFacet 5 428
cert_cover_5 5 0 1 2 4 6 44 428 3
cert_coverFacet 6 436
cert_cover_5 6 0 1 3 4 6 52 436 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0097

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e11q2_0100.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0100

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 91, 395, 115, 109, 141, 901, 282, 818, 220, 740, 804, 920, 752, 11, 83, 35, 259, 13, 37, 133, 261, 73, 137, 97, 385, 26, 266, 50, 274, 290, 76, 140, 100, 292, 548, 196, 644, 772, 88, 152, 280, 392, 112, 560, 208, 656, 784, 736, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_91, vertices_395, vertices_115, vertices_109, vertices_141, vertices_901, vertices_282, vertices_818, vertices_220, vertices_740, vertices_804, vertices_920, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_83, vertices_35, vertices_259, vertices_13, vertices_37, vertices_133, vertices_261, vertices_73, vertices_137, vertices_97, vertices_385, vertices_26, vertices_266, vertices_50, vertices_274, vertices_290, vertices_76, vertices_140, vertices_100, vertices_292, vertices_548, vertices_196, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_392, vertices_112, vertices_560, vertices_208, vertices_656, vertices_784, vertices_736, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_91), (false, vertices_395), (false, vertices_115), (false, vertices_109), (false, vertices_141), (false, vertices_901), (true, vertices_274), (true, vertices_548), (true, vertices_196), (true, vertices_152), (true, vertices_280), (true, vertices_560), (true, vertices_208), (true, vertices_656), (true, vertices_784), (true, vertices_736), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_115) then 18 else
  if p.val = (false, vertices_109) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_736) then 22 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 50 3
cert_row_2 1 4 5 6 8 736
cert_row_4 2 1 2 3 5 6 220 76 2
cert_row_4 3 2 3 6 7 8 920 152 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 818
cert_cover_5 1 0 0 3 4 7 50 818 3
cert_coverFacet 2 220
cert_cover_5 2 2 1 2 3 5 76 220 2
cert_coverFacet 3 740
cert_cover_5 3 1 1 4 5 6 100 740 3
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 920
cert_cover_5 5 3 2 3 6 7 152 920 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0100

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e11q2_0101.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0101

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 147, 99, 707, 613, 409, 929, 62, 110, 218, 284, 460, 820, 964, 19, 35, 67, 131, 145, 273, 97, 289, 545, 577, 385, 641, 46, 26, 74, 50, 146, 98, 194, 28, 76, 268, 52, 276, 100, 548, 452, 580, 772, 152, 280, 200, 392, 304, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_147, vertices_99, vertices_707, vertices_613, vertices_409, vertices_929, vertices_62, vertices_110, vertices_218, vertices_284, vertices_460, vertices_820, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_131, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_46, vertices_26, vertices_74, vertices_50, vertices_146, vertices_98, vertices_194, vertices_28, vertices_76, vertices_268, vertices_52, vertices_276, vertices_100, vertices_548, vertices_452, vertices_580, vertices_772, vertices_152, vertices_280, vertices_200, vertices_392, vertices_304, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_147), (false, vertices_99), (false, vertices_707), (false, vertices_613), (false, vertices_409), (false, vertices_929), (true, vertices_46), (true, vertices_26), (true, vertices_74), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_452), (true, vertices_772), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 12 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_99) then 1 else
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_46) then 14 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_452) then 17 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_200) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_452), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_4 0 1 3 4 7 8 820 52 3
cert_row_2 1 1 5 6 7 452
cert_row_2 2 0 1 2 4 46
cert_row_4 3 0 2 3 5 6 218 26 3
cert_rows
cert_pivot_2 8 7 1 0
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 2 0 1 2 3 46 62 3
cert_coverFacet 1 110
cert_cover_5 1 2 0 1 2 5 46 110 3
cert_coverFacet 2 218
cert_cover_5 2 3 0 2 3 5 26 218 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 460
cert_cover_5 4 1 1 2 5 6 76 460 3
cert_coverFacet 5 820
cert_cover_5 5 0 1 3 4 7 52 820 3
cert_coverFacet 6 964
cert_cover_5 6 1 1 5 6 8 452 964 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0101

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e11q2_0102.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0102

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 397, 901, 345, 233, 865, 94, 206, 662, 370, 562, 226, 284, 820, 389, 73, 137, 265, 97, 161, 545, 321, 641, 769, 78, 22, 134, 50, 82, 530, 98, 162, 546, 194, 642, 28, 140, 268, 276, 532, 644, 772, 88, 280, 200, 304, 560, 336, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_397, vertices_901, vertices_345, vertices_233, vertices_865, vertices_94, vertices_206, vertices_662, vertices_370, vertices_562, vertices_226, vertices_284, vertices_820] (by decide +kernel)
  polygons := literalFinset [vertices_389, vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_769, vertices_78, vertices_22, vertices_134, vertices_50, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_28, vertices_140, vertices_268, vertices_276, vertices_532, vertices_644, vertices_772, vertices_88, vertices_280, vertices_200, vertices_304, vertices_560, vertices_336, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_397), (false, vertices_901), (false, vertices_345), (false, vertices_233), (false, vertices_865), (true, vertices_78), (true, vertices_22), (true, vertices_134), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_194), (true, vertices_28), (true, vertices_276), (true, vertices_532), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 13 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_78) then 14 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 6 8 662 22 3
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 206
cert_cover_5 1 0 0 1 2 6 78 206 3
cert_coverFacet 2 662
cert_cover_5 2 1 0 1 3 6 22 662 3
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 50 370 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 276 820 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0102

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e11q2_0103.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0103

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 397, 653, 597, 357, 737, 94, 334, 410, 626, 178, 354, 540, 696, 141, 69, 261, 517, 97, 161, 289, 577, 385, 641, 78, 26, 266, 50, 82, 146, 98, 162, 290, 322, 386, 28, 268, 524, 84, 532, 324, 152, 536, 392, 648, 176, 560, 592, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_397, vertices_653, vertices_597, vertices_357, vertices_737, vertices_94, vertices_334, vertices_410, vertices_626, vertices_178, vertices_354, vertices_540, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_78, vertices_26, vertices_266, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_28, vertices_268, vertices_524, vertices_84, vertices_532, vertices_324, vertices_152, vertices_536, vertices_392, vertices_648, vertices_176, vertices_560, vertices_592, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_397), (false, vertices_653), (false, vertices_597), (false, vertices_357), (false, vertices_737), (true, vertices_78), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_322), (true, vertices_28), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 15 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 13 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_78) then 14 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
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
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 6 7 410 26 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 26 410 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 152 696 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0103

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e11q2_0104.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0104

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 539, 397, 341, 661, 681, 598, 618, 426, 114, 306, 868, 932, 368, 27, 21, 133, 261, 137, 265, 521, 273, 529, 641, 42, 266, 522, 50, 82, 274, 530, 98, 290, 578, 84, 532, 804, 324, 580, 388, 644, 168, 552, 392, 112, 304, 336, 352, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_539, vertices_397, vertices_341, vertices_661, vertices_681, vertices_598, vertices_618, vertices_426, vertices_114, vertices_306, vertices_868, vertices_932, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_21, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_273, vertices_529, vertices_641, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_578, vertices_84, vertices_532, vertices_804, vertices_324, vertices_580, vertices_388, vertices_644, vertices_168, vertices_552, vertices_392, vertices_112, vertices_304, vertices_336, vertices_352, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_539), (false, vertices_397), (false, vertices_341), (false, vertices_661), (false, vertices_681), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_578), (true, vertices_804), (true, vertices_580), (true, vertices_112), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 13 else
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_804) then 21 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_2 1 1 4 7 8 804
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 0 2 4 6 7 426 42 3
cert_rows
cert_pivot_2 3 1 5 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 42 618 3
cert_coverFacet 2 426
cert_cover_5 2 3 0 2 4 6 42 426 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 868
cert_cover_5 5 1 1 4 5 7 804 868 2
cert_coverFacet 6 932
cert_cover_5 6 1 1 4 6 7 804 932 2
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0104

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e11q2_0105.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0105

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 899, 397, 345, 665, 625, 654, 614, 166, 370, 418, 316, 572, 420, 771, 25, 137, 265, 81, 529, 321, 577, 385, 641, 38, 134, 518, 98, 162, 290, 322, 578, 386, 642, 60, 140, 268, 524, 164, 292, 548, 388, 280, 536, 648, 112, 304, 560, 336, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_899, vertices_397, vertices_345, vertices_665, vertices_625, vertices_654, vertices_614, vertices_166, vertices_370, vertices_418, vertices_316, vertices_572, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_771, vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_38, vertices_134, vertices_518, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_386, vertices_642, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_899), (false, vertices_397), (false, vertices_345), (false, vertices_665), (false, vertices_625), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_60), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 0 3 4 5 7 370 98 1
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 38 614 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 370
cert_cover_5 3 3 0 3 4 5 98 370 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 7 60 316 3
cert_coverFacet 6 572
cert_cover_5 6 1 1 2 3 8 60 572 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0105

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e11q2_0106.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0106

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 157, 313, 681, 721, 849, 174, 302, 214, 838, 226, 610, 348, 736, 25, 41, 137, 593, 145, 273, 289, 545, 641, 769, 46, 70, 134, 262, 98, 162, 290, 546, 194, 578, 770, 28, 140, 268, 84, 148, 324, 280, 168, 296, 208, 336, 224, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_157, vertices_313, vertices_681, vertices_721, vertices_849, vertices_174, vertices_302, vertices_214, vertices_838, vertices_226, vertices_610, vertices_348, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_593, vertices_145, vertices_273, vertices_289, vertices_545, vertices_641, vertices_769, vertices_46, vertices_70, vertices_134, vertices_262, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_84, vertices_148, vertices_324, vertices_280, vertices_168, vertices_296, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_157), (false, vertices_313), (false, vertices_681), (false, vertices_721), (false, vertices_849), (true, vertices_46), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_268), (true, vertices_84), (true, vertices_324), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_313) then 18 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_46) then 14 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 1 3 5 6 214 70 2
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 1 2 3 5 7 348 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 7 46 302 3
cert_coverFacet 2 214
cert_cover_5 2 1 0 1 3 5 70 214 2
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 70 838 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 28 348 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0106

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e12q3_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e12q3_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 595, 227, 419, 217, 913, 302, 550, 610, 124, 668, 908, 628, 488, 163, 67, 259, 515, 81, 145, 529, 193, 385, 769, 38, 262, 518, 98, 290, 546, 578, 28, 44, 652, 268, 116, 532, 548, 772, 88, 152, 104, 296, 200, 392, 592, 656, 224, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_595, vertices_227, vertices_419, vertices_217, vertices_913, vertices_302, vertices_550, vertices_610, vertices_124, vertices_668, vertices_908, vertices_628, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_163, vertices_67, vertices_259, vertices_515, vertices_81, vertices_145, vertices_529, vertices_193, vertices_385, vertices_769, vertices_38, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_578, vertices_28, vertices_44, vertices_652, vertices_268, vertices_116, vertices_532, vertices_548, vertices_772, vertices_88, vertices_152, vertices_104, vertices_296, vertices_200, vertices_392, vertices_592, vertices_656, vertices_224, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_595), (false, vertices_227), (false, vertices_419), (false, vertices_217), (false, vertices_913), (true, vertices_38), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_652), (true, vertices_268), (true, vertices_116), (true, vertices_532), (true, vertices_548), (true, vertices_104), (true, vertices_296), (true, vertices_392), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 11 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_217) then 12 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_652) then 13 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_116) then 16 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_608) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 5 116
cert_row_2 1 1 2 6 8 652
cert_row_4 2 0 1 2 4 7 302 38 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 2 0 1 2 4 38 302 2
cert_coverFacet 1 550
cert_cover_2 1 1 0 4 8 38 550 3
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 4 28 124 3
cert_coverFacet 4 668
cert_cover_5 4 1 1 2 3 6 28 668 3
cert_coverFacet 5 908
cert_cover_5 5 1 1 2 6 7 652 908 3
cert_coverFacet 6 628
cert_cover_5 6 0 1 3 4 8 116 628 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e12q3_0000

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e12q3_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e12q3_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 781, 217, 665, 361, 929, 542, 54, 422, 902, 114, 722, 348, 372, 153, 73, 265, 521, 97, 161, 289, 193, 641, 769, 22, 38, 390, 518, 50, 82, 530, 98, 162, 194, 642, 28, 268, 524, 52, 340, 292, 772, 88, 536, 328, 112, 208, 656, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_781, vertices_217, vertices_665, vertices_361, vertices_929, vertices_542, vertices_54, vertices_422, vertices_902, vertices_114, vertices_722, vertices_348, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_153, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_641, vertices_769, vertices_22, vertices_38, vertices_390, vertices_518, vertices_50, vertices_82, vertices_530, vertices_98, vertices_162, vertices_194, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_340, vertices_292, vertices_772, vertices_88, vertices_536, vertices_328, vertices_112, vertices_208, vertices_656, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_781), (false, vertices_217), (false, vertices_665), (false, vertices_361), (false, vertices_929), (true, vertices_22), (true, vertices_38), (true, vertices_390), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_642), (true, vertices_28), (true, vertices_52), (true, vertices_340), (true, vertices_292), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 12 else
  if p.val = (false, vertices_781) then 15 else
  if p.val = (false, vertices_217) then 18 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_340) then 16 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_112) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_2 2 1 3 5 7 340
cert_row_2 3 0 1 6 7 390
cert_rows
cert_pivot_2 2 8 3 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 54
cert_cover_2 1 1 0 3 4 22 54 3
cert_coverFacet 2 422
cert_cover_5 2 3 0 1 4 6 38 422 3
cert_coverFacet 3 902
cert_cover_5 3 3 0 1 6 8 390 902 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 6 82 722 3
cert_coverFacet 6 348
cert_cover_5 6 2 1 2 3 5 28 348 3
cert_coverFacet 7 372
cert_cover_5 7 2 1 3 4 5 52 372 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e12q3_0001

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q0_0028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 419, 835, 181, 613, 361, 794, 394, 650, 668, 116, 852, 248, 344, 424, 131, 259, 515, 37, 133, 517, 97, 161, 289, 321, 577, 138, 266, 522, 386, 642, 770, 52, 84, 148, 532, 100, 580, 644, 88, 152, 280, 536, 104, 168, 296, 328, 392, 648, 112, 176, 336, 784, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_419, vertices_835, vertices_181, vertices_613, vertices_361, vertices_794, vertices_394, vertices_650, vertices_668, vertices_116, vertices_852, vertices_248, vertices_344, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_133, vertices_517, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_648, vertices_112, vertices_176, vertices_336, vertices_784, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_419), (false, vertices_835), (false, vertices_181), (false, vertices_613), (false, vertices_361), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_84), (true, vertices_532), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_112), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 1 2 3 6 8 668 148 1
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 266 794 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 668
cert_cover_5 3 2 1 2 3 6 148 668 1
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 852
cert_cover_5 5 1 1 3 5 7 84 852 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0028

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q0_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 179, 275, 173, 589, 313, 850, 658, 108, 724, 484, 872, 432, 464, 19, 131, 259, 515, 13, 133, 517, 41, 265, 521, 49, 273, 161, 146, 274, 530, 642, 770, 44, 76, 100, 164, 196, 580, 644, 104, 296, 584, 776, 176, 304, 208, 336, 592, 400, 656, 352, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_179, vertices_275, vertices_173, vertices_589, vertices_313, vertices_850, vertices_658, vertices_108, vertices_724, vertices_484, vertices_872, vertices_432, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_13, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_49, vertices_273, vertices_161, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_44, vertices_76, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_352, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_179), (false, vertices_275), (false, vertices_173), (false, vertices_589), (false, vertices_313), (true, vertices_530), (true, vertices_100), (true, vertices_196), (true, vertices_104), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_352), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 274 2
cert_row_4 1 1 3 5 6 8 724 196 1
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 850
cert_cover_5 0 0 0 3 5 7 274 850 2
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 196 724 1
cert_coverFacet 4 484
cert_cover_5 4 2 1 4 5 6 100 484 3
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 104 872 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0037

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 589, 229, 805, 721, 417, 782, 602, 154, 394, 658, 124, 316, 408, 496, 37, 69, 517, 161, 289, 193, 577, 385, 641, 769, 26, 138, 266, 522, 146, 530, 386, 642, 770, 60, 76, 268, 524, 100, 292, 772, 88, 152, 280, 584, 392, 112, 304, 208, 592, 400, 656, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_589, vertices_229, vertices_805, vertices_721, vertices_417, vertices_782, vertices_602, vertices_154, vertices_394, vertices_658, vertices_124, vertices_316, vertices_408, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_772, vertices_88, vertices_152, vertices_280, vertices_584, vertices_392, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_589), (false, vertices_229), (false, vertices_805), (false, vertices_721), (false, vertices_417), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_60), (true, vertices_268), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_112), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 417 1 26 2 138 3 266 522 146 530 268 88 152 280 392 112 304 400 899 589 60 229 805 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 4 5 6 7 496 112 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 6 4 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 602
cert_cover_5 1 3 0 2 3 5 26 602 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 124
cert_cover_5 5 1 1 2 3 5 60 124 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 496
cert_cover_5 8 0 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0016

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0131.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0131

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 651, 531, 419, 541, 333, 457, 786, 738, 802, 716, 628, 340, 496, 816, 19, 131, 259, 515, 13, 21, 261, 329, 137, 521, 529, 385, 274, 530, 162, 290, 546, 642, 770, 76, 524, 84, 276, 532, 324, 580, 200, 648, 112, 304, 560, 336, 784, 224, 608, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_651, vertices_531, vertices_419, vertices_541, vertices_333, vertices_457, vertices_786, vertices_738, vertices_802, vertices_716, vertices_628, vertices_340, vertices_496, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_13, vertices_21, vertices_261, vertices_329, vertices_137, vertices_521, vertices_529, vertices_385, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_200, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_651), (false, vertices_531), (false, vertices_419), (false, vertices_541), (false, vertices_333), (false, vertices_457), (true, vertices_546), (true, vertices_770), (true, vertices_84), (true, vertices_580), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 15 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 8 738 162 2
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 786
cert_cover_2 0 3 0 7 8 274 786 3
cert_coverFacet 1 738
cert_cover_5 1 0 0 4 5 6 162 738 2
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 76 716 3
cert_coverFacet 4 628
cert_cover_5 4 2 1 3 4 5 84 628 2
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0131

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0171.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0171

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 525, 453, 773, 681, 241, 782, 282, 538, 690, 466, 316, 372, 568, 13, 69, 261, 517, 41, 521, 97, 161, 193, 385, 641, 769, 26, 266, 522, 146, 274, 530, 386, 642, 770, 44, 268, 524, 308, 100, 324, 772, 56, 280, 536, 552, 112, 176, 560, 208, 336, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_525, vertices_453, vertices_773, vertices_681, vertices_241, vertices_782, vertices_282, vertices_538, vertices_690, vertices_466, vertices_316, vertices_372, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_521, vertices_97, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_308, vertices_100, vertices_324, vertices_772, vertices_56, vertices_280, vertices_536, vertices_552, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_525), (false, vertices_453), (false, vertices_773), (false, vertices_681), (false, vertices_241), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_268), (true, vertices_308), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_308) then 19 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 525 773 26 266 522 146 274 530 268 56 280 536 560 336 899 109 453 308 681 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 0 3 5 6 7 466 146 2
cert_rows
cert_pivot_2 2 1 4 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 146 690 2
cert_coverFacet 4 466
cert_cover_5 4 3 0 3 5 6 146 466 2
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 4 44 316 2
cert_coverFacet 6 372
cert_cover_5 6 1 1 3 4 5 308 372 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0171

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0244.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0244

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 181, 597, 421, 841, 369, 398, 662, 682, 778, 120, 568, 600, 488, 688, 21, 165, 261, 517, 49, 81, 289, 321, 577, 769, 134, 262, 518, 138, 266, 522, 642, 770, 148, 532, 388, 56, 88, 536, 104, 168, 552, 328, 584, 392, 776, 112, 176, 560, 592, 656, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_181, vertices_597, vertices_421, vertices_841, vertices_369, vertices_398, vertices_662, vertices_682, vertices_778, vertices_120, vertices_568, vertices_600, vertices_488, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_165, vertices_261, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_148, vertices_532, vertices_388, vertices_56, vertices_88, vertices_536, vertices_104, vertices_168, vertices_552, vertices_328, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_560, vertices_592, vertices_656, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_181), (false, vertices_597), (false, vertices_421), (false, vertices_841), (false, vertices_369), (true, vertices_134), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_642), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_560), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 134 1 138 266 522 642 56 88 536 104 168 552 392 560 656 672 775 181 597 421 841 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 1 2 6 7 398 134 2
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 134 662 2
cert_coverFacet 2 682
cert_cover_5 2 2 0 2 4 6 138 682 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0244

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0365.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0365

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 173, 781, 709, 425, 465, 662, 810, 370, 562, 210, 706, 572, 180, 432, 13, 133, 517, 169, 265, 193, 321, 577, 385, 769, 50, 82, 146, 530, 290, 546, 194, 322, 578, 642, 770, 44, 524, 52, 148, 532, 164, 644, 296, 552, 776, 176, 304, 560, 208, 336, 400, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_173, vertices_781, vertices_709, vertices_425, vertices_465, vertices_662, vertices_810, vertices_370, vertices_562, vertices_210, vertices_706, vertices_572, vertices_180, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_169, vertices_265, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_50, vertices_82, vertices_146, vertices_530, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_644, vertices_296, vertices_552, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_173), (false, vertices_781), (false, vertices_709), (false, vertices_425), (false, vertices_465), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_173) then 21 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 50 1 82 2 146 530 290 546 194 642 52 148 532 552 176 304 560 835 781 709 173 425 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 3 4 8 572 44 2
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 290 810 1
cert_coverFacet 2 370
cert_cover_5 2 1 0 3 4 5 50 370 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 44 572 2
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0365

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0371.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0371

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 57, 345, 617, 433, 654, 422, 774, 218, 586, 466, 692, 568, 664, 25, 41, 73, 49, 273, 289, 545, 321, 577, 769, 134, 262, 518, 74, 138, 522, 210, 322, 578, 386, 770, 164, 292, 548, 644, 772, 56, 88, 152, 536, 552, 584, 648, 176, 560, 336, 400, 656, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_57, vertices_345, vertices_617, vertices_433, vertices_654, vertices_422, vertices_774, vertices_218, vertices_586, vertices_466, vertices_692, vertices_568, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_74, vertices_138, vertices_522, vertices_210, vertices_322, vertices_578, vertices_386, vertices_770, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_552, vertices_584, vertices_648, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_57), (false, vertices_345), (false, vertices_617), (false, vertices_433), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_210), (true, vertices_386), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_210) then 17 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 57 134 262 518 74 138 522 386 164 644 152 536 648 560 656 835 210 805 345 617 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 0 1 4 6 7 422 134 2
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 422
cert_cover_5 1 2 0 1 4 6 134 422 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 218
cert_cover_5 3 0 0 2 3 5 74 218 2
cert_coverFacet 4 586
cert_cover_2 4 2 0 5 8 74 586 3
cert_coverFacet 5 466
cert_cover_5 5 0 0 3 5 7 210 466 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 164 692 1
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0371

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0400.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0400

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 301, 77, 613, 457, 849, 662, 426, 682, 466, 786, 220, 556, 652, 596, 13, 37, 69, 73, 265, 289, 545, 321, 577, 769, 170, 146, 274, 530, 290, 546, 386, 642, 770, 44, 76, 140, 524, 84, 148, 532, 548, 580, 644, 296, 552, 200, 392, 648, 208, 336, 592, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_301, vertices_77, vertices_613, vertices_457, vertices_849, vertices_662, vertices_426, vertices_682, vertices_466, vertices_786, vertices_220, vertices_556, vertices_652, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_73, vertices_265, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_170, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_548, vertices_580, vertices_644, vertices_296, vertices_552, vertices_200, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_301), (false, vertices_77), (false, vertices_613), (false, vertices_457), (false, vertices_849), (true, vertices_170), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_644), (true, vertices_552), (true, vertices_648), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_170) then 17 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 77 146 274 530 386 642 140 524 84 148 532 644 552 648 208 803 170 301 613 457 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 6 170
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 1 2 3 5 6 220 76 2
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 7 170 426 3
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 8 170 682 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 146 466 2
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 220
cert_cover_5 5 3 1 2 3 5 76 220 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0400

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0410.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0410

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 805, 361, 553, 713, 465, 30, 558, 406, 774, 538, 722, 124, 372, 600, 41, 73, 521, 289, 545, 193, 321, 385, 641, 769, 14, 22, 262, 518, 26, 522, 146, 530, 386, 642, 770, 28, 44, 116, 276, 292, 548, 772, 88, 536, 104, 552, 584, 208, 336, 592, 400, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_805, vertices_361, vertices_553, vertices_713, vertices_465, vertices_30, vertices_558, vertices_406, vertices_774, vertices_538, vertices_722, vertices_124, vertices_372, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_26, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_116, vertices_276, vertices_292, vertices_548, vertices_772, vertices_88, vertices_536, vertices_104, vertices_552, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_805), (false, vertices_361), (false, vertices_553), (false, vertices_713), (false, vertices_465), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_116), (true, vertices_276), (true, vertices_88), (true, vertices_536), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_116) then 19 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 553 2 14 1 22 3 262 518 26 522 146 530 28 44 276 88 536 592 899 805 116 361 713 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_2 1 1 3 4 5 116
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 2 4 1 0
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 14 558 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 22 406 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 722
cert_cover_5 5 3 0 3 5 6 146 722 2
cert_coverFacet 6 124
cert_cover_5 6 1 1 2 3 4 28 124 3
cert_coverFacet 7 372
cert_cover_5 7 1 1 3 4 7 116 372 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0410

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0431.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0431

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 333, 181, 597, 233, 657, 838, 458, 818, 402, 658, 564, 804, 440, 269, 21, 37, 69, 41, 73, 145, 529, 161, 193, 577, 641, 146, 274, 530, 194, 322, 578, 386, 642, 770, 52, 532, 292, 548, 324, 580, 772, 168, 296, 200, 328, 392, 176, 304, 560, 400, 656, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_333, vertices_181, vertices_597, vertices_233, vertices_657, vertices_838, vertices_458, vertices_818, vertices_402, vertices_658, vertices_564, vertices_804, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_21, vertices_37, vertices_69, vertices_41, vertices_73, vertices_145, vertices_529, vertices_161, vertices_193, vertices_577, vertices_641, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_333), (false, vertices_181), (false, vertices_597), (false, vertices_233), (false, vertices_657), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_548), (true, vertices_772), (true, vertices_392), (true, vertices_304), (true, vertices_560), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_597) then 22 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 2 3 4 6 7 440 168 1
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 194 458 1
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 274 818 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 168 440 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0431

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0503.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0503

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 661, 613, 421, 217, 233, 666, 282, 778, 338, 866, 908, 804, 376, 424, 37, 133, 517, 201, 81, 145, 529, 97, 161, 577, 26, 266, 522, 82, 274, 530, 322, 578, 770, 292, 548, 388, 644, 772, 88, 152, 280, 104, 168, 296, 392, 648, 776, 336, 656, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_661, vertices_613, vertices_421, vertices_217, vertices_233, vertices_666, vertices_282, vertices_778, vertices_338, vertices_866, vertices_908, vertices_804, vertices_376, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_201, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_577, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_336, vertices_656, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_661), (false, vertices_613), (false, vertices_421), (false, vertices_217), (false, vertices_233), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_322), (true, vertices_770), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_336), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 26 1 266 2 522 274 322 770 772 280 296 392 648 776 336 352 800 595 661 613 421 217 233
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 6 7 8 908 388 1
cert_row_4 1 0 2 3 6 8 666 26 3
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 1 0 2 3 6 26 666 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 908
cert_cover_5 5 0 1 2 6 7 388 908 1
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 88 376 2
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0503

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0643.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0643

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 61, 341, 677, 389, 281, 809, 454, 346, 714, 778, 244, 568, 600, 752, 21, 37, 133, 261, 25, 41, 265, 273, 545, 385, 641, 769, 74, 266, 522, 194, 322, 386, 642, 770, 52, 84, 164, 196, 324, 388, 56, 88, 280, 536, 552, 584, 776, 240, 560, 336, 592, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_61, vertices_341, vertices_677, vertices_389, vertices_281, vertices_809, vertices_454, vertices_346, vertices_714, vertices_778, vertices_244, vertices_568, vertices_600, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_261, vertices_25, vertices_41, vertices_265, vertices_273, vertices_545, vertices_385, vertices_641, vertices_769, vertices_74, vertices_266, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_280, vertices_536, vertices_552, vertices_584, vertices_776, vertices_240, vertices_560, vertices_336, vertices_592, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_61), (false, vertices_341), (false, vertices_677), (false, vertices_389), (false, vertices_281), (false, vertices_809), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_322), (true, vertices_196), (true, vertices_88), (true, vertices_536), (true, vertices_584), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_61) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_240) then 23 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 2 3 5 7 346 74 2
cert_row_4 3 0 2 5 6 8 714 74 3
cert_rows
cert_pivot_2 4 1 3 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 74 346 2
cert_coverFacet 2 714
cert_cover_5 2 3 0 2 5 6 74 714 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 752
cert_cover_5 7 0 3 4 5 8 240 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0643

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0680.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0680

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 781, 677, 457, 433, 214, 842, 626, 306, 402, 450, 604, 660, 688, 13, 133, 517, 201, 265, 161, 289, 545, 385, 769, 50, 82, 146, 274, 290, 546, 194, 322, 578, 386, 770, 76, 524, 84, 148, 532, 196, 644, 328, 584, 776, 176, 304, 560, 592, 400, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_781, vertices_677, vertices_457, vertices_433, vertices_214, vertices_842, vertices_626, vertices_306, vertices_402, vertices_450, vertices_604, vertices_660, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_201, vertices_265, vertices_161, vertices_289, vertices_545, vertices_385, vertices_769, vertices_50, vertices_82, vertices_146, vertices_274, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_76, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_644, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_781), (false, vertices_677), (false, vertices_457), (false, vertices_433), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 50 1 82 2 146 274 194 322 578 386 84 148 532 584 560 592 656 803 781 677 205 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 82 1
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 82 214 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 626
cert_cover_5 2 2 0 3 4 5 50 626 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0680

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0450 : Certifies 450 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0451 : Certifies 451 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0088.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0452 : Certifies 452 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0089.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0453 : Certifies 453 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0090.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0454 : Certifies 454 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0091.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0455 : Certifies 455 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0092.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0456 : Certifies 456 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0097.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0457 : Certifies 457 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0100.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0458 : Certifies 458 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0101.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0459 : Certifies 459 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0102.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0460 : Certifies 460 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0103.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0461 : Certifies 461 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0104.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0462 : Certifies 462 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0105.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0463 : Certifies 463 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0106.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0464 : Certifies 464 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e12q3_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0465 : Certifies 465 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e12q3_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0466 : Certifies 466 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0467 : Certifies 467 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0468 : Certifies 468 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0469 : Certifies 469 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0131.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0470 : Certifies 470 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0171.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0471 : Certifies 471 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0244.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0472 : Certifies 472 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0365.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0473 : Certifies 473 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0371.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0474 : Certifies 474 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0400.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0475 : Certifies 475 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0410.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0476 : Certifies 476 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0431.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0477 : Certifies 477 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0503.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0478 : Certifies 478 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0643.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0479 : Certifies 479 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0680.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B015 (j : Fin 30) :
    Certifies (450 + j.val) := by
  fin_cases j
  · exact projection_0450
  · exact projection_0451
  · exact projection_0452
  · exact projection_0453
  · exact projection_0454
  · exact projection_0455
  · exact projection_0456
  · exact projection_0457
  · exact projection_0458
  · exact projection_0459
  · exact projection_0460
  · exact projection_0461
  · exact projection_0462
  · exact projection_0463
  · exact projection_0464
  · exact projection_0465
  · exact projection_0466
  · exact projection_0467
  · exact projection_0468
  · exact projection_0469
  · exact projection_0470
  · exact projection_0471
  · exact projection_0472
  · exact projection_0473
  · exact projection_0474
  · exact projection_0475
  · exact projection_0476
  · exact projection_0477
  · exact projection_0478
  · exact projection_0479

end Nonrational.TerminalVerification
