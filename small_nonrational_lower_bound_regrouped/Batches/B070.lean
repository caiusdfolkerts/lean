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
/- Source: ProjectionCertificates/P0_186.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_186

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 837, 793, 465, 737, 302, 782, 614, 186, 538, 674, 484, 408, 424, 145, 273, 529, 193, 321, 577, 641, 769, 270, 38, 518, 26, 42, 522, 146, 530, 162, 546, 642, 100, 292, 324, 580, 772, 152, 280, 536, 168, 296, 392, 776, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_837, vertices_793, vertices_465, vertices_737, vertices_302, vertices_782, vertices_614, vertices_186, vertices_538, vertices_674, vertices_484, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_270, vertices_38, vertices_518, vertices_26, vertices_42, vertices_522, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_776, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_837), (false, vertices_793), (false, vertices_465), (false, vertices_737), (true, vertices_270), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_100), (true, vertices_292), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 38 3
cert_row_4 1 0 2 4 6 3 186 42 3
cert_row_4 2 1 5 6 7 4 484 324 2
cert_row_2 3 1 2 7 0 270
cert_rows
cert_pivot_2 8 3 4 0
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 3 0 1 2 4 270 302 3
cert_coverFacet 1 782
cert_cover_5 1 3 0 1 2 8 270 782 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 38 614 3
cert_coverFacet 3 186
cert_cover_5 3 1 0 2 3 4 26 186 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 484
cert_cover_5 6 2 1 4 5 6 100 484 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_186

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_187.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_187

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 837, 809, 369, 689, 398, 782, 198, 582, 682, 210, 658, 468, 440, 49, 81, 529, 289, 545, 321, 577, 769, 270, 70, 134, 518, 138, 522, 82, 146, 530, 194, 578, 642, 196, 324, 580, 388, 772, 168, 296, 552, 392, 776, 176, 304, 208, 336, 400, 656, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_837, vertices_809, vertices_369, vertices_689, vertices_398, vertices_782, vertices_198, vertices_582, vertices_682, vertices_210, vertices_658, vertices_468, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_270, vertices_70, vertices_134, vertices_518, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_656, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_837), (false, vertices_809), (false, vertices_369), (false, vertices_689), (true, vertices_270), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_194), (true, vertices_642), (true, vertices_196), (true, vertices_388), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 138 2
cert_row_4 1 1 3 6 7 5 468 388 1
cert_row_4 2 2 4 6 7 3 440 168 3
cert_row_2 3 1 2 7 0 270
cert_rows
cert_pivot_2 8 5 3 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 270 398 3
cert_coverFacet 1 782
cert_cover_5 1 3 0 1 2 8 270 782 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 682
cert_cover_5 4 0 0 2 4 6 138 682 2
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 658
cert_cover_2 6 3 0 6 8 146 658 3
cert_coverFacet 7 468
cert_cover_5 7 1 1 3 5 6 196 468 1
cert_coverFacet 8 440
cert_cover_5 8 2 2 3 4 6 168 440 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_187

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_188.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_188

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 203, 659, 771, 409, 329, 817, 806, 710, 364, 740, 248, 312, 688, 67, 131, 259, 515, 73, 137, 265, 145, 273, 529, 321, 769, 70, 262, 518, 194, 642, 770, 100, 292, 548, 708, 324, 56, 152, 280, 104, 296, 200, 328, 176, 304, 560, 656, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_203, vertices_659, vertices_771, vertices_409, vertices_329, vertices_817, vertices_806, vertices_710, vertices_364, vertices_740, vertices_248, vertices_312, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_321, vertices_769, vertices_70, vertices_262, vertices_518, vertices_194, vertices_642, vertices_770, vertices_100, vertices_292, vertices_548, vertices_708, vertices_324, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_203), (false, vertices_659), (false, vertices_771), (false, vertices_409), (false, vertices_329), (false, vertices_817), (true, vertices_518), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_708), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_176), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_771) then 10 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_329) then 11 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_708) then 17 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_708), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 1 4 7 8 0 806 292 3
cert_row_4 1 1 2 4 5 7 364 100 1
cert_row_4 2 3 4 5 6 2 248 176 2
cert_row_2 3 5 6 8 1 708
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 262 806 2
cert_coverFacet 1 710
cert_cover_5 1 3 0 1 5 6 70 710 3
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 5 100 364 1
cert_coverFacet 3 740
cert_cover_5 3 3 1 4 5 6 100 740 3
cert_coverFacet 4 248
cert_cover_5 4 2 2 3 4 5 56 248 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_188

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_189.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_189

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 653, 181, 805, 369, 657, 590, 218, 666, 338, 866, 236, 612, 240, 37, 133, 517, 49, 145, 273, 529, 289, 641, 769, 154, 74, 522, 82, 274, 530, 322, 578, 770, 76, 140, 524, 100, 164, 548, 580, 200, 648, 112, 176, 208, 336, 656, 224, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_653, vertices_181, vertices_805, vertices_369, vertices_657, vertices_590, vertices_218, vertices_666, vertices_338, vertices_866, vertices_236, vertices_612, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_49, vertices_145, vertices_273, vertices_529, vertices_289, vertices_641, vertices_769, vertices_154, vertices_74, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_580, vertices_200, vertices_648, vertices_112, vertices_176, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_653), (false, vertices_181), (false, vertices_805), (false, vertices_369), (false, vertices_657), (true, vertices_154), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_100), (true, vertices_580), (true, vertices_200), (true, vertices_208), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_657) then 12 else
  if p.val = (true, vertices_154) then 15 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 4 5 8 7 866 578 1
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 2 4 5 6 1 236 200 1
cert_row_2 3 2 3 6 0 154
cert_rows
cert_pivot_2 7 8 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 218
cert_cover_5 1 3 0 2 3 5 154 218 3
cert_coverFacet 2 666
cert_cover_5 2 3 0 2 3 8 154 666 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 866
cert_cover_5 4 0 0 4 5 7 322 866 1
cert_coverFacet 5 236
cert_cover_5 5 2 1 2 4 5 76 236 2
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_189

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_190.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_190

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 453, 345, 617, 705, 406, 774, 314, 810, 178, 738, 248, 464, 133, 261, 517, 73, 265, 521, 193, 321, 577, 641, 134, 262, 518, 298, 50, 146, 274, 162, 546, 642, 770, 388, 772, 56, 88, 280, 104, 552, 776, 176, 208, 336, 400, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_453, vertices_345, vertices_617, vertices_705, vertices_406, vertices_774, vertices_314, vertices_810, vertices_178, vertices_738, vertices_248, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_298, vertices_50, vertices_146, vertices_274, vertices_162, vertices_546, vertices_642, vertices_770, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_552, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_453), (false, vertices_345), (false, vertices_617), (false, vertices_705), (true, vertices_262), (true, vertices_298), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_56), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_705) then 12 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_298) then 15 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_298), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 1 406 146 3
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 2 4 5 6 3 248 104 3
cert_row_2 3 2 4 7 0 298
cert_rows
cert_pivot_2 1 8 3 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 134 406 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 314
cert_cover_5 2 3 0 2 3 4 298 314 2
cert_coverFacet 3 810
cert_cover_5 3 3 0 2 4 8 298 810 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 56 248 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_190

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_191.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_191

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 229, 805, 617, 849, 449, 174, 558, 790, 154, 538, 466, 728, 232, 37, 133, 261, 97, 545, 193, 321, 577, 385, 769, 46, 134, 262, 518, 26, 138, 522, 146, 274, 530, 386, 164, 548, 772, 152, 536, 104, 168, 552, 200, 584, 208, 336, 592, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_229, vertices_805, vertices_617, vertices_849, vertices_449, vertices_174, vertices_558, vertices_790, vertices_154, vertices_538, vertices_466, vertices_728, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_164, vertices_548, vertices_772, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_229), (false, vertices_805), (false, vertices_617), (false, vertices_849), (false, vertices_449), (true, vertices_46), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_200), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (false, vertices_449) then 12 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_208) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 7 8 1 790 274 3
cert_row_4 2 3 5 6 7 0 466 208 3
cert_row_4 3 3 5 6 8 2 728 208 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 790
cert_cover_5 2 1 0 1 3 7 262 790 2
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 466
cert_cover_5 5 2 0 3 5 6 146 466 2
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 152 728 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_191

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_192.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_192

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 677, 409, 369, 721, 417, 782, 346, 602, 354, 802, 668, 428, 804, 81, 145, 273, 97, 161, 289, 545, 577, 385, 641, 90, 266, 522, 98, 290, 546, 322, 578, 770, 140, 268, 524, 164, 292, 548, 644, 772, 152, 280, 536, 392, 336, 592, 656, 352, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_677, vertices_409, vertices_369, vertices_721, vertices_417, vertices_782, vertices_346, vertices_602, vertices_354, vertices_802, vertices_668, vertices_428, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_90, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_336, vertices_592, vertices_656, vertices_352, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_677), (false, vertices_409), (false, vertices_369), (false, vertices_721), (false, vertices_417), (true, vertices_90), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_322), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_772), (true, vertices_536), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_417) then 12 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 6 7 4 428 140 3
cert_row_4 1 0 1 2 8 7 782 522 1
cert_row_4 2 2 3 6 8 1 668 152 3
cert_row_2 3 2 3 5 0 90
cert_rows
cert_pivot_2 4 7 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 346
cert_cover_5 1 3 0 2 3 7 90 346 3
cert_coverFacet 2 602
cert_cover_5 2 3 0 2 3 8 90 602 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 668
cert_cover_5 5 2 1 2 3 6 140 668 2
cert_coverFacet 6 428
cert_cover_5 6 0 1 2 4 6 140 428 2
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_192

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_193.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_193

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 357, 709, 233, 689, 801, 334, 590, 282, 538, 818, 440, 728, 360, 69, 261, 517, 97, 161, 289, 545, 193, 641, 769, 78, 262, 518, 26, 266, 522, 274, 530, 770, 324, 580, 152, 280, 536, 104, 168, 296, 200, 328, 584, 176, 304, 560, 656, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_357, vertices_709, vertices_233, vertices_689, vertices_801, vertices_334, vertices_590, vertices_282, vertices_538, vertices_818, vertices_440, vertices_728, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_641, vertices_769, vertices_78, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_656, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_357), (false, vertices_709), (false, vertices_233), (false, vertices_689), (false, vertices_801), (true, vertices_78), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_328), (true, vertices_584), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_801) then 12 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_304) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_row_2 0 0 2 5 1 78
cert_row_4 1 3 4 7 8 0 818 304 3
cert_row_4 2 2 3 6 7 4 440 152 3
cert_row_4 3 3 5 6 8 2 728 656 1
cert_rows
cert_pivot_2 1 0 4 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 818
cert_cover_5 4 1 0 3 4 7 274 818 2
cert_coverFacet 5 440
cert_cover_5 5 2 2 3 4 6 152 440 2
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 152 728 2
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_193

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_194.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_194

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 653, 405, 837, 625, 657, 398, 170, 810, 242, 402, 866, 780, 696, 133, 261, 517, 81, 145, 273, 529, 321, 577, 641, 42, 138, 266, 82, 146, 274, 98, 162, 802, 322, 386, 140, 268, 524, 388, 772, 168, 552, 648, 776, 112, 176, 560, 400, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_653, vertices_405, vertices_837, vertices_625, vertices_657, vertices_398, vertices_170, vertices_810, vertices_242, vertices_402, vertices_866, vertices_780, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_641, vertices_42, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_802, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_388, vertices_772, vertices_168, vertices_552, vertices_648, vertices_776, vertices_112, vertices_176, vertices_560, vertices_400, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_653), (false, vertices_405), (false, vertices_837), (false, vertices_625), (false, vertices_657), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_802), (true, vertices_386), (true, vertices_268), (true, vertices_168), (true, vertices_552), (true, vertices_776), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_657) then 12 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_802) then 15 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_176) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 2 6 7 1 398 138 3
cert_row_4 1 0 3 4 6 5 242 146 2
cert_row_4 2 3 4 6 8 2 696 176 3
cert_row_2 3 4 7 8 0 802
cert_rows
cert_pivot_2 1 5 2 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 810
cert_cover_5 2 3 0 2 4 7 42 810 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 82 242 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 866
cert_cover_5 5 3 0 4 5 7 98 866 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 696
cert_cover_5 7 2 2 3 4 6 168 696 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_194

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_196.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_196

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 341, 409, 841, 625, 657, 422, 362, 618, 394, 690, 244, 404, 356, 137, 265, 521, 81, 145, 273, 529, 321, 577, 641, 106, 138, 266, 522, 162, 290, 546, 386, 642, 84, 148, 276, 100, 164, 292, 324, 388, 328, 584, 392, 112, 176, 560, 400, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_341, vertices_409, vertices_841, vertices_625, vertices_657, vertices_422, vertices_362, vertices_618, vertices_394, vertices_690, vertices_244, vertices_404, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_641, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_324, vertices_388, vertices_328, vertices_584, vertices_392, vertices_112, vertices_176, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_341), (false, vertices_409), (false, vertices_841), (false, vertices_625), (false, vertices_657), (true, vertices_106), (true, vertices_266), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_148), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_176), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_657) then 12 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 266 162 290 546 386 148 100 164 292 388 176 352 657 651 106 341 409 841 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 162 1
cert_row_4 1 0 3 4 6 8 690 162 1
cert_row_4 2 3 4 5 6 1 244 112 3
cert_row_2 3 2 4 5 0 106
cert_rows
cert_pivot_2 7 8 1 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 362
cert_cover_5 1 3 0 2 4 7 106 362 3
cert_coverFacet 2 618
cert_cover_5 2 3 0 2 4 8 106 618 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 162 690 1
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 84 244 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_196

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_203.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_203

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 405, 533, 677, 121, 345, 481, 790, 58, 282, 106, 842, 738, 964, 21, 133, 517, 89, 49, 273, 529, 97, 161, 545, 321, 385, 26, 42, 74, 266, 50, 274, 530, 98, 546, 578, 770, 276, 532, 388, 644, 772, 56, 280, 104, 328, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_405, vertices_533, vertices_677, vertices_121, vertices_345, vertices_481, vertices_790, vertices_58, vertices_282, vertices_106, vertices_842, vertices_738, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_89, vertices_49, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_26, vertices_42, vertices_74, vertices_266, vertices_50, vertices_274, vertices_530, vertices_98, vertices_546, vertices_578, vertices_770, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_328, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_405), (false, vertices_533), (false, vertices_677), (false, vertices_121), (false, vertices_345), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_274), (true, vertices_98), (true, vertices_578), (true, vertices_770), (true, vertices_772), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 13 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_533) then 11 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 1 7 8 3 790 770 1
cert_row_4 1 0 5 7 8 2 842 578 2
cert_row_4 2 4 5 6 8 0 738 224 3
cert_row_4 3 5 6 7 8 1 964 448 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 106
cert_cover_2 3 2 0 4 5 42 106 3
cert_coverFacet 4 842
cert_cover_5 4 1 0 2 5 7 74 842 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 964
cert_cover_5 6 3 1 5 6 7 388 964 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_203

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_204.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_204

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 61, 789, 613, 313, 481, 662, 466, 786, 738, 156, 684, 408, 424, 21, 37, 517, 57, 273, 97, 289, 321, 577, 769, 146, 274, 530, 194, 322, 578, 642, 770, 28, 44, 140, 148, 532, 548, 644, 152, 280, 168, 296, 392, 400, 784, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_61, vertices_789, vertices_613, vertices_313, vertices_481, vertices_662, vertices_466, vertices_786, vertices_738, vertices_156, vertices_684, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_57, vertices_273, vertices_97, vertices_289, vertices_321, vertices_577, vertices_769, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_148, vertices_532, vertices_548, vertices_644, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_400, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_61), (false, vertices_789), (false, vertices_613), (false, vertices_313), (false, vertices_481), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_148), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_61) then 19 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 146 2
cert_row_4 1 0 1 6 8 3 662 642 1
cert_row_4 2 4 5 6 8 0 738 224 3
cert_row_4 3 2 4 6 8 1 684 168 3
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 466
cert_cover_5 1 0 0 3 5 6 146 466 2
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 194 738 1
cert_coverFacet 4 156
cert_cover_2 4 2 1 3 6 28 156 3
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 44 684 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_204

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_205.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_205

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 227, 899, 781, 345, 481, 678, 626, 572, 284, 372, 420, 900, 600, 67, 131, 515, 73, 265, 521, 225, 321, 385, 769, 98, 162, 546, 578, 642, 28, 268, 524, 52, 276, 164, 292, 548, 388, 644, 772, 88, 280, 536, 584, 112, 560, 336, 592, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_227, vertices_899, vertices_781, vertices_345, vertices_481, vertices_678, vertices_626, vertices_572, vertices_284, vertices_372, vertices_420, vertices_900, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_73, vertices_265, vertices_521, vertices_225, vertices_321, vertices_385, vertices_769, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_276, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_584, vertices_112, vertices_560, vertices_336, vertices_592, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_227), (false, vertices_899), (false, vertices_781), (false, vertices_345), (false, vertices_481), (true, vertices_546), (true, vertices_28), (true, vertices_52), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_536), (true, vertices_112), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 21 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_227) then 22 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 8 6 678 546 1
cert_row_4 1 3 4 5 8 0 626 112 3
cert_row_4 2 1 3 4 8 2 572 52 3
cert_row_4 3 3 4 5 7 1 372 112 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 626
cert_cover_5 1 1 0 3 4 5 98 626 1
cert_coverFacet 2 572
cert_cover_5 2 2 1 2 3 4 28 572 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 372
cert_cover_5 4 3 1 3 4 5 52 372 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_205

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_206.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_206

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 675, 579, 387, 405, 617, 241, 902, 842, 124, 348, 812, 180, 676, 67, 131, 259, 515, 81, 145, 273, 97, 161, 545, 577, 385, 322, 578, 386, 642, 770, 92, 44, 268, 52, 148, 276, 164, 548, 388, 644, 772, 104, 552, 328, 584, 776, 112, 176, 336, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_675, vertices_579, vertices_387, vertices_405, vertices_617, vertices_241, vertices_902, vertices_842, vertices_124, vertices_348, vertices_812, vertices_180, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_577, vertices_385, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_92, vertices_44, vertices_268, vertices_52, vertices_148, vertices_276, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_675), (false, vertices_579), (false, vertices_387), (false, vertices_405), (false, vertices_617), (false, vertices_241), (true, vertices_770), (true, vertices_92), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_579) then 10 else
  if p.val = (false, vertices_387) then 11 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_92) then 17 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_776) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 0 1 7 8 6 902 770 1
cert_row_4 1 2 5 7 8 0 842 328 3
cert_row_4 2 1 2 7 8 4 812 268 3
cert_row_2 3 2 3 5 1 92
cert_rows
cert_pivot_2 6 0 4 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 124
cert_cover_5 2 3 1 2 3 4 92 124 3
cert_coverFacet 3 348
cert_cover_5 3 3 1 2 3 7 92 348 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 44 812 3
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_206

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_207.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_207

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 285, 653, 149, 841, 817, 182, 230, 714, 562, 866, 204, 332, 372, 13, 21, 133, 265, 521, 145, 273, 529, 641, 769, 166, 50, 146, 530, 98, 546, 194, 578, 642, 76, 140, 268, 52, 148, 276, 100, 196, 324, 200, 328, 584, 648, 304, 560, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_285, vertices_653, vertices_149, vertices_841, vertices_817, vertices_182, vertices_230, vertices_714, vertices_562, vertices_866, vertices_204, vertices_332, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_166, vertices_50, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_76, vertices_140, vertices_268, vertices_52, vertices_148, vertices_276, vertices_100, vertices_196, vertices_324, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_560, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_285), (false, vertices_653), (false, vertices_149), (false, vertices_841), (false, vertices_817), (true, vertices_166), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_52), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_200), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_149) then 12 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_166) then 15 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 5 6 8 2 714 194 3
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 1 4 5 7 3 372 100 3
cert_row_2 3 1 4 6 0 166
cert_rows
cert_pivot_2 2 8 3 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 3 0 1 3 4 166 182 2
cert_coverFacet 1 230
cert_cover_5 1 3 0 1 4 5 166 230 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 194 714 1
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 98 866 3
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 372
cert_cover_5 7 2 1 3 4 5 52 372 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_207

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_208.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_208

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 405, 313, 601, 905, 209, 118, 214, 550, 902, 618, 812, 308, 120, 25, 265, 521, 81, 145, 273, 193, 577, 385, 641, 86, 38, 134, 518, 98, 546, 194, 578, 642, 52, 148, 276, 292, 548, 388, 772, 56, 88, 104, 296, 552, 584, 776, 112, 304, 208, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_405, vertices_313, vertices_601, vertices_905, vertices_209, vertices_118, vertices_214, vertices_550, vertices_902, vertices_618, vertices_812, vertices_308, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_193, vertices_577, vertices_385, vertices_641, vertices_86, vertices_38, vertices_134, vertices_518, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_304, vertices_208, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_405), (false, vertices_313), (false, vertices_601), (false, vertices_905), (false, vertices_209), (true, vertices_86), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_98), (true, vertices_546), (true, vertices_52), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_209) then 12 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 6 902 518 2
cert_row_4 1 1 2 4 8 7 812 548 1
cert_row_4 2 0 4 5 8 2 618 98 3
cert_row_2 3 1 3 5 0 86
cert_rows
cert_pivot_2 6 7 2 0
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 3 0 1 3 4 86 118 3
cert_coverFacet 1 214
cert_cover_5 1 3 0 1 3 6 86 214 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 902
cert_cover_5 3 0 0 1 6 7 134 902 3
cert_coverFacet 4 618
cert_cover_5 4 2 0 2 4 5 98 618 1
cert_coverFacet 5 812
cert_cover_5 5 1 1 2 4 7 292 812 1
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_208

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_211.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_211

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 661, 345, 809, 713, 209, 182, 534, 806, 362, 242, 338, 684, 232, 73, 265, 521, 81, 145, 273, 529, 193, 641, 769, 22, 38, 518, 178, 82, 274, 530, 98, 290, 322, 770, 148, 532, 164, 548, 644, 104, 168, 296, 552, 200, 328, 648, 208, 336, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_661, vertices_345, vertices_809, vertices_713, vertices_209, vertices_182, vertices_534, vertices_806, vertices_362, vertices_242, vertices_338, vertices_684, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_178, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_770, vertices_148, vertices_532, vertices_164, vertices_548, vertices_644, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_648, vertices_208, vertices_336, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_661), (false, vertices_345), (false, vertices_809), (false, vertices_713), (false, vertices_209), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_178), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_164), (true, vertices_548), (true, vertices_104), (true, vertices_168), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_209) then 12 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_178) then 15 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 5 362 290 1
cert_row_4 1 0 1 4 8 7 806 38 3
cert_row_4 2 2 4 6 8 1 684 168 3
cert_row_2 3 3 4 6 0 178
cert_rows
cert_pivot_2 5 7 1 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 3 0 1 3 4 22 182 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 806
cert_cover_5 2 1 0 1 4 7 38 806 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 98 362 1
cert_coverFacet 4 242
cert_cover_5 4 3 0 3 4 5 178 242 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 684
cert_cover_5 6 2 1 2 4 6 164 684 1
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_211

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_212.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_212

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 157, 781, 277, 681, 721, 810, 370, 594, 738, 172, 300, 468, 484, 13, 21, 261, 137, 521, 145, 273, 529, 641, 769, 82, 274, 530, 98, 290, 546, 578, 770, 44, 140, 268, 148, 276, 164, 292, 452, 168, 296, 552, 776, 208, 336, 592, 224, 352, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_157, vertices_781, vertices_277, vertices_681, vertices_721, vertices_810, vertices_370, vertices_594, vertices_738, vertices_172, vertices_300, vertices_468, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_148, vertices_276, vertices_164, vertices_292, vertices_452, vertices_168, vertices_296, vertices_552, vertices_776, vertices_208, vertices_336, vertices_592, vertices_224, vertices_352, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_157), (false, vertices_781), (false, vertices_277), (false, vertices_681), (false, vertices_721), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_44), (true, vertices_164), (true, vertices_292), (true, vertices_452), (true, vertices_296), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_277) then 12 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_452) then 20 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_452), by decide +kernel⟩
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
cert_row_4 0 0 4 7 8 2 810 290 3
cert_row_4 1 0 4 5 7 3 370 98 3
cert_row_4 2 4 5 6 8 0 738 224 3
cert_row_2 3 5 6 7 1 452
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 0 0 2 4 7 290 810 1
cert_coverFacet 1 370
cert_cover_5 1 1 0 3 4 5 82 370 2
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 98 738 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 148 468 2
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 164 484 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_212

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_213.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_213

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 661, 421, 837, 361, 225, 122, 538, 842, 242, 658, 796, 404, 440, 133, 261, 517, 97, 161, 289, 193, 321, 577, 641, 26, 74, 522, 114, 146, 530, 194, 578, 642, 148, 276, 532, 388, 772, 56, 280, 536, 104, 296, 328, 776, 176, 400, 656, 224, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_661, vertices_421, vertices_837, vertices_361, vertices_225, vertices_122, vertices_538, vertices_842, vertices_242, vertices_658, vertices_796, vertices_404, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_26, vertices_74, vertices_522, vertices_114, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_776, vertices_176, vertices_400, vertices_656, vertices_224, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_661), (false, vertices_421), (false, vertices_837), (false, vertices_361), (false, vertices_225), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_114), (true, vertices_146), (true, vertices_530), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_225) then 12 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_114) then 15 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 26 74 522 146 530 276 56 280 536 776 176 400 225 707 114 661 421 837 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 7 8 1 796 280 3
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 3 4 6 7 2 440 176 3
cert_row_2 3 3 4 5 0 114
cert_rows
cert_pivot_2 1 8 2 0
cert_heightProof 4
cert_coverFacet 0 122
cert_cover_5 0 3 0 2 3 4 26 122 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 242
cert_cover_5 3 3 0 3 4 6 114 242 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 796
cert_cover_5 5 0 1 2 3 7 276 796 1
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 440
cert_cover_5 7 2 2 3 4 6 56 440 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_213

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_215.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_215

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 713, 241, 305, 849, 302, 654, 550, 842, 204, 332, 436, 468, 49, 81, 273, 161, 289, 545, 193, 577, 641, 769, 14, 38, 518, 266, 522, 290, 546, 770, 76, 140, 268, 404, 164, 292, 548, 196, 324, 644, 200, 328, 584, 648, 176, 304, 208, 336, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_713, vertices_241, vertices_305, vertices_849, vertices_302, vertices_654, vertices_550, vertices_842, vertices_204, vertices_332, vertices_436, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_518, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_76, vertices_140, vertices_268, vertices_404, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_200, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_713), (false, vertices_241), (false, vertices_305), (false, vertices_849), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_404), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_305) then 12 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_404) then 17 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_328) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 4 302 14 3
cert_row_4 1 0 2 7 8 5 842 266 3
cert_row_4 2 1 2 6 8 0 654 140 3
cert_row_2 3 3 6 7 1 404
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 14 302 3
cert_coverFacet 1 654
cert_cover_5 1 2 0 1 2 6 14 654 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 266 842 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 404 436 2
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 404 468 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_215

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_216.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_216

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 157, 589, 565, 361, 425, 177, 790, 842, 370, 562, 908, 404, 432, 13, 21, 517, 297, 73, 137, 49, 145, 97, 161, 545, 577, 50, 274, 530, 98, 546, 322, 578, 770, 140, 524, 148, 276, 532, 388, 772, 328, 584, 392, 776, 176, 304, 560, 400, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_157, vertices_589, vertices_565, vertices_361, vertices_425, vertices_177, vertices_790, vertices_842, vertices_370, vertices_562, vertices_908, vertices_404, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_297, vertices_73, vertices_137, vertices_49, vertices_145, vertices_97, vertices_161, vertices_545, vertices_577, vertices_50, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_304, vertices_560, vertices_400, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_157), (false, vertices_589), (false, vertices_565), (false, vertices_361), (false, vertices_425), (false, vertices_177), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_770), (true, vertices_276), (true, vertices_388), (true, vertices_772), (true, vertices_776), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 13 else
  if p.val = (false, vertices_157) then 15 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_177) then 11 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 4 370 274 2
cert_row_4 1 0 1 7 8 3 790 770 1
cert_row_4 2 2 5 7 8 0 842 328 3
cert_row_4 3 2 6 7 8 1 908 392 3
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 322 842 1
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 5 50 370 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 908
cert_cover_5 4 3 1 2 6 7 140 908 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_216

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_218.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_218

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 355, 707, 661, 217, 281, 329, 806, 610, 156, 796, 428, 740, 488, 67, 259, 515, 25, 73, 265, 145, 273, 529, 193, 321, 641, 98, 290, 546, 578, 770, 28, 140, 268, 148, 532, 164, 292, 548, 644, 772, 152, 280, 424, 200, 328, 784, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_355, vertices_707, vertices_661, vertices_217, vertices_281, vertices_329, vertices_806, vertices_610, vertices_156, vertices_796, vertices_428, vertices_740, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_25, vertices_73, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_152, vertices_280, vertices_424, vertices_200, vertices_328, vertices_784, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_355), (false, vertices_707), (false, vertices_661), (false, vertices_217), (false, vertices_281), (false, vertices_329), (true, vertices_546), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_424), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 13 else
  if p.val = (false, vertices_355) then 14 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_281) then 10 else
  if p.val = (false, vertices_329) then 11 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_424) then 20 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 7 8 0 806 292 3
cert_row_4 1 1 2 7 8 3 796 268 3
cert_row_4 2 4 5 6 8 1 740 224 3
cert_row_2 3 4 6 7 2 424
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 28 796 3
cert_coverFacet 4 428
cert_cover_5 4 3 1 2 4 6 140 428 2
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 164 740 2
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 424 488 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_218

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_221.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_221

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 803, 707, 309, 57, 153, 681, 838, 450, 60, 604, 812, 468, 728, 131, 259, 515, 25, 41, 137, 49, 145, 273, 289, 545, 641, 194, 322, 578, 386, 770, 28, 44, 524, 52, 84, 276, 292, 324, 580, 772, 56, 600, 152, 552, 648, 208, 400, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_803, vertices_707, vertices_309, vertices_57, vertices_153, vertices_681, vertices_838, vertices_450, vertices_60, vertices_604, vertices_812, vertices_468, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_25, vertices_41, vertices_137, vertices_49, vertices_145, vertices_273, vertices_289, vertices_545, vertices_641, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_44, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_324, vertices_580, vertices_772, vertices_56, vertices_600, vertices_152, vertices_552, vertices_648, vertices_208, vertices_400, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_803), (false, vertices_707), (false, vertices_309), (false, vertices_57), (false, vertices_153), (false, vertices_681), (true, vertices_322), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_84), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_600), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 13 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_57) then 10 else
  if p.val = (false, vertices_153) then 11 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (true, vertices_322) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_600) then 20 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 5 7 8 0 838 324 3
cert_row_4 1 1 2 7 8 4 812 524 2
cert_row_4 2 3 5 6 7 1 468 208 3
cert_row_2 3 3 5 8 2 600
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 604
cert_cover_5 3 3 1 2 3 5 28 604 3
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 7 44 812 3
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 84 468 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 600 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_221

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_222.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_222

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 405, 677, 837, 617, 449, 314, 106, 842, 434, 450, 796, 660, 696, 133, 261, 517, 97, 161, 545, 193, 321, 577, 385, 42, 74, 266, 306, 98, 162, 194, 322, 386, 148, 276, 532, 644, 772, 56, 280, 536, 104, 552, 584, 776, 176, 400, 656, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_405, vertices_677, vertices_837, vertices_617, vertices_449, vertices_314, vertices_106, vertices_842, vertices_434, vertices_450, vertices_796, vertices_660, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_42, vertices_74, vertices_266, vertices_306, vertices_98, vertices_162, vertices_194, vertices_322, vertices_386, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_552, vertices_584, vertices_776, vertices_176, vertices_400, vertices_656, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_405), (false, vertices_677), (false, vertices_837), (false, vertices_617), (false, vertices_449), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_306), (true, vertices_322), (true, vertices_386), (true, vertices_532), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_176), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_449) then 12 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_306) then 15 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 42 74 266 322 386 532 56 280 536 776 176 656 449 227 306 405 677 837 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 5 842 266 3
cert_row_4 1 2 3 7 8 1 796 280 3
cert_row_4 2 3 4 6 8 2 696 176 3
cert_row_2 3 3 4 7 0 306
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 314
cert_cover_5 0 3 0 2 3 4 42 314 2
cert_coverFacet 1 106
cert_cover_2 1 2 0 4 5 42 106 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 434
cert_cover_5 3 3 0 3 4 6 306 434 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 796
cert_cover_5 5 1 1 2 3 7 276 796 1
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 696
cert_cover_5 7 2 2 3 4 6 56 696 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_222

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_223.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_223

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 331, 275, 99, 781, 277, 613, 713, 690, 466, 738, 820, 920, 456, 19, 35, 67, 259, 21, 37, 261, 517, 73, 265, 521, 273, 97, 577, 50, 146, 274, 98, 674, 194, 322, 52, 276, 548, 772, 200, 328, 392, 648, 776, 560, 400, 656, 784, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_331, vertices_275, vertices_99, vertices_781, vertices_277, vertices_613, vertices_713, vertices_690, vertices_466, vertices_738, vertices_820, vertices_920, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_259, vertices_21, vertices_37, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_273, vertices_97, vertices_577, vertices_50, vertices_146, vertices_274, vertices_98, vertices_674, vertices_194, vertices_322, vertices_52, vertices_276, vertices_548, vertices_772, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_560, vertices_400, vertices_656, vertices_784, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_331), (false, vertices_275), (false, vertices_99), (false, vertices_781), (false, vertices_277), (false, vertices_613), (false, vertices_713), (true, vertices_146), (true, vertices_674), (true, vertices_194), (true, vertices_392), (true, vertices_560), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 12 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_275) then 8 else
  if p.val = (false, vertices_99) then 9 else
  if p.val = (false, vertices_781) then 13 else
  if p.val = (false, vertices_277) then 10 else
  if p.val = (false, vertices_613) then 14 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_674) then 17 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_392) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_400) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_448) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_674), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 5 466 146 3
cert_row_4 1 3 4 7 8 1 820 560 2
cert_row_4 2 3 6 7 8 2 920 400 3
cert_row_2 3 4 6 8 0 674
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 3 0 3 4 6 50 690 3
cert_coverFacet 1 466
cert_cover_5 1 0 0 3 5 6 146 466 2
cert_coverFacet 2 738
cert_cover_5 2 3 0 4 5 6 98 738 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 920
cert_cover_5 4 2 2 3 6 7 392 920 1
cert_coverFacet 5 456
cert_cover_2 5 5 2 6 7 200 456 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_223

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_224.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_224

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 781, 661, 569, 345, 465, 806, 646, 362, 690, 226, 450, 248, 808, 133, 261, 517, 25, 265, 521, 337, 145, 529, 385, 134, 262, 518, 98, 162, 290, 546, 194, 322, 386, 642, 644, 772, 56, 88, 104, 296, 552, 328, 776, 176, 560, 208, 656, 224, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_781, vertices_661, vertices_569, vertices_345, vertices_465, vertices_806, vertices_646, vertices_362, vertices_690, vertices_226, vertices_450, vertices_248, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_337, vertices_145, vertices_529, vertices_385, vertices_134, vertices_262, vertices_518, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_781), (false, vertices_661), (false, vertices_569), (false, vertices_345), (false, vertices_465), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_104), (true, vertices_296), (true, vertices_176), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 7 8 1 806 290 3
cert_row_4 1 0 2 4 5 7 362 98 1
cert_row_4 2 3 4 6 8 0 690 176 3
cert_row_4 3 3 4 5 6 2 248 176 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 262 806 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 98 362 1
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 162 690 1
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_224

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_225.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_225

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 661, 121, 793, 425, 241, 214, 614, 646, 810, 226, 418, 604, 616, 25, 41, 265, 113, 145, 529, 161, 385, 641, 769, 70, 134, 518, 98, 162, 290, 546, 194, 386, 642, 770, 84, 148, 532, 580, 644, 88, 536, 104, 296, 552, 584, 776, 208, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_661, vertices_121, vertices_793, vertices_425, vertices_241, vertices_214, vertices_614, vertices_646, vertices_810, vertices_226, vertices_418, vertices_604, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_113, vertices_145, vertices_529, vertices_161, vertices_385, vertices_641, vertices_769, vertices_70, vertices_134, vertices_518, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_88, vertices_536, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_208, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_661), (false, vertices_121), (false, vertices_793), (false, vertices_425), (false, vertices_241), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_84), (true, vertices_580), (true, vertices_552), (true, vertices_584), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 17 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 70 2
cert_row_4 1 0 2 4 8 7 810 546 1
cert_row_4 2 1 4 5 8 0 614 580 1
cert_row_4 3 2 3 5 8 1 604 88 3
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 70 214 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 70 614 2
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 290 810 1
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 84 604 1
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_225

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_226.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_226

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 205, 837, 601, 809, 393, 214, 598, 806, 426, 690, 184, 568, 216, 69, 133, 261, 73, 137, 265, 521, 577, 385, 769, 86, 134, 262, 518, 146, 530, 162, 290, 546, 386, 196, 580, 772, 56, 88, 152, 536, 168, 296, 552, 200, 392, 176, 560, 208, 592, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_205, vertices_837, vertices_601, vertices_809, vertices_393, vertices_214, vertices_598, vertices_806, vertices_426, vertices_690, vertices_184, vertices_568, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_265, vertices_521, vertices_577, vertices_385, vertices_769, vertices_86, vertices_134, vertices_262, vertices_518, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_196, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_392, vertices_176, vertices_560, vertices_208, vertices_592, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_205), (false, vertices_837), (false, vertices_601), (false, vertices_809), (false, vertices_393), (true, vertices_86), (true, vertices_518), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_560), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_393) then 12 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 2 426 162 3
cert_row_4 1 0 1 4 8 7 806 518 2
cert_row_4 2 0 3 6 8 4 690 146 3
cert_row_2 3 1 3 5 0 86
cert_rows
cert_pivot_2 2 7 4 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 3 0 1 3 8 86 598 3
cert_coverFacet 2 806
cert_cover_5 2 1 0 1 4 7 262 806 2
cert_coverFacet 3 426
cert_cover_5 3 0 0 2 4 6 162 426 1
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 146 690 2
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_226

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_227.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_227

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 405, 713, 369, 689, 449, 310, 566, 774, 842, 354, 668, 460, 780, 49, 145, 273, 97, 545, 193, 321, 577, 385, 641, 54, 262, 518, 98, 290, 546, 322, 578, 770, 140, 268, 524, 148, 276, 532, 388, 772, 200, 328, 584, 648, 776, 304, 560, 656, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_405, vertices_713, vertices_369, vertices_689, vertices_449, vertices_310, vertices_566, vertices_774, vertices_842, vertices_354, vertices_668, vertices_460, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_304, vertices_560, vertices_656, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_405), (false, vertices_713), (false, vertices_369), (false, vertices_689), (false, vertices_449), (true, vertices_54), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_322), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_772), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_449) then 12 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 2 5 7 8 0 842 328 3
cert_row_4 2 1 2 6 8 3 668 140 3
cert_row_4 3 2 5 6 7 1 460 200 3
cert_rows
cert_pivot_2 4 0 3 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 322 842 1
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 668
cert_cover_5 5 2 1 2 3 6 140 668 2
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 140 460 2
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_227

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_230.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_230

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 357, 105, 681, 841, 433, 310, 662, 838, 402, 124, 604, 184, 664, 41, 73, 521, 97, 161, 289, 321, 385, 641, 769, 22, 262, 518, 146, 274, 386, 642, 770, 92, 52, 532, 100, 292, 324, 580, 56, 152, 536, 104, 168, 584, 648, 176, 304, 400, 656, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_357, vertices_105, vertices_681, vertices_841, vertices_433, vertices_310, vertices_662, vertices_838, vertices_402, vertices_124, vertices_604, vertices_184, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_92, vertices_52, vertices_532, vertices_100, vertices_292, vertices_324, vertices_580, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_584, vertices_648, vertices_176, vertices_304, vertices_400, vertices_656, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_357), (false, vertices_105), (false, vertices_681), (false, vertices_841), (false, vertices_433), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_146), (true, vertices_274), (true, vertices_92), (true, vertices_52), (true, vertices_532), (true, vertices_580), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_105) then 12 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_92) then 17 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 4 310 22 3
cert_row_4 1 0 1 3 8 6 662 22 3
cert_row_4 2 1 5 7 8 0 838 324 3
cert_row_2 3 2 3 5 1 92
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 662
cert_cover_5 1 1 0 1 3 6 22 662 3
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 262 838 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 124
cert_cover_5 4 3 1 2 3 4 92 124 3
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 8 92 604 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_230

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2133 : Certifies 2133 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_186.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2134 : Certifies 2134 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_187.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2135 : Certifies 2135 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_188.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2136 : Certifies 2136 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_189.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2137 : Certifies 2137 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_190.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2138 : Certifies 2138 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_191.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2139 : Certifies 2139 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_192.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2140 : Certifies 2140 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_193.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2141 : Certifies 2141 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_194.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2142 : Certifies 2142 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_196.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2143 : Certifies 2143 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_203.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2144 : Certifies 2144 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_204.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2145 : Certifies 2145 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_205.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2146 : Certifies 2146 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_206.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2147 : Certifies 2147 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_207.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2148 : Certifies 2148 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_208.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2149 : Certifies 2149 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_211.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2150 : Certifies 2150 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_212.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2151 : Certifies 2151 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_213.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2152 : Certifies 2152 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_215.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2153 : Certifies 2153 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_216.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2154 : Certifies 2154 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_218.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2155 : Certifies 2155 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_221.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2156 : Certifies 2156 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_222.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2157 : Certifies 2157 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_223.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2158 : Certifies 2158 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_224.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2159 : Certifies 2159 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_225.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2160 : Certifies 2160 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_226.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2161 : Certifies 2161 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_227.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2162 : Certifies 2162 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_230.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B070 (j : Fin 30) :
    Certifies (2133 + j.val) := by
  fin_cases j
  · exact projection_2133
  · exact projection_2134
  · exact projection_2135
  · exact projection_2136
  · exact projection_2137
  · exact projection_2138
  · exact projection_2139
  · exact projection_2140
  · exact projection_2141
  · exact projection_2142
  · exact projection_2143
  · exact projection_2144
  · exact projection_2145
  · exact projection_2146
  · exact projection_2147
  · exact projection_2148
  · exact projection_2149
  · exact projection_2150
  · exact projection_2151
  · exact projection_2152
  · exact projection_2153
  · exact projection_2154
  · exact projection_2155
  · exact projection_2156
  · exact projection_2157
  · exact projection_2158
  · exact projection_2159
  · exact projection_2160
  · exact projection_2161
  · exact projection_2162

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
