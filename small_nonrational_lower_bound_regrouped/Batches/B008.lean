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
/- Source: ProjectionCertificates/R_m14e10q0_0072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 583, 211, 557, 601, 409, 169, 358, 426, 450, 852, 804, 824, 464, 7, 67, 131, 37, 517, 25, 41, 137, 521, 81, 145, 161, 577, 38, 70, 162, 290, 194, 322, 386, 292, 548, 324, 580, 772, 280, 536, 168, 296, 552, 392, 208, 336, 592, 400, 784, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_583, vertices_211, vertices_557, vertices_601, vertices_409, vertices_169, vertices_358, vertices_426, vertices_450, vertices_852, vertices_804, vertices_824, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_131, vertices_37, vertices_517, vertices_25, vertices_41, vertices_137, vertices_521, vertices_81, vertices_145, vertices_161, vertices_577, vertices_38, vertices_70, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_208, vertices_336, vertices_592, vertices_400, vertices_784, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_583), (false, vertices_211), (false, vertices_557), (false, vertices_601), (false, vertices_409), (false, vertices_169), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_296), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 13 else
  if p.val = (false, vertices_583) then 14 else
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 162 1
cert_row_4 1 0 1 4 5 7 358 38 3
cert_row_4 2 1 3 5 7 8 852 324 1
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 5 38 358 3
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 162 426 1
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 852
cert_cover_5 3 2 1 3 5 7 324 852 1
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 280 824 2
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0072

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q0_0074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 403, 803, 157, 109, 201, 481, 666, 562, 962, 604, 564, 868, 712, 19, 35, 259, 13, 21, 37, 73, 137, 145, 97, 289, 193, 385, 50, 146, 530, 546, 386, 642, 770, 28, 76, 52, 532, 100, 548, 580, 152, 536, 200, 584, 648, 560, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_403, vertices_803, vertices_157, vertices_109, vertices_201, vertices_481, vertices_666, vertices_562, vertices_962, vertices_604, vertices_564, vertices_868, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_13, vertices_21, vertices_37, vertices_73, vertices_137, vertices_145, vertices_97, vertices_289, vertices_193, vertices_385, vertices_50, vertices_146, vertices_530, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_52, vertices_532, vertices_100, vertices_548, vertices_580, vertices_152, vertices_536, vertices_200, vertices_584, vertices_648, vertices_560, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_403), (false, vertices_803), (false, vertices_157), (false, vertices_109), (false, vertices_201), (false, vertices_481), (true, vertices_530), (true, vertices_642), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_536), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 13 else
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_157) then 17 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 1 4 5 7 8 868 100 3
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 2 0 2 3 6 146 666 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 386 962 1
cert_coverFacet 3 604
cert_cover_5 3 3 1 2 3 5 28 604 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 868
cert_cover_5 5 0 1 4 5 7 100 868 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0074

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q0_0075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 403, 355, 613, 665, 961, 558, 282, 538, 298, 412, 300, 716, 484, 19, 35, 259, 145, 529, 97, 545, 321, 577, 385, 641, 26, 42, 266, 522, 274, 530, 290, 546, 44, 140, 268, 524, 100, 292, 548, 196, 580, 388, 152, 280, 536, 296, 648, 400, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_403, vertices_355, vertices_613, vertices_665, vertices_961, vertices_558, vertices_282, vertices_538, vertices_298, vertices_412, vertices_300, vertices_716, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_145, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_44, vertices_140, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_152, vertices_280, vertices_536, vertices_296, vertices_648, vertices_400, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_403), (false, vertices_355), (false, vertices_613), (false, vertices_665), (false, vertices_961), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_280), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 1 2 3 6 7 412 140 2
cert_row_4 2 1 2 5 6 8 716 140 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 412
cert_cover_5 4 1 1 2 3 6 140 412 2
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 716
cert_cover_5 6 2 1 2 5 6 140 716 2
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0075

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q0_0083.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0083

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 227, 803, 781, 457, 433, 722, 674, 316, 604, 692, 804, 344, 464, 35, 67, 515, 73, 265, 521, 161, 289, 193, 385, 769, 162, 546, 194, 578, 642, 28, 268, 524, 52, 532, 292, 548, 772, 88, 280, 328, 584, 176, 304, 208, 336, 592, 400, 656, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_227, vertices_803, vertices_781, vertices_457, vertices_433, vertices_722, vertices_674, vertices_316, vertices_604, vertices_692, vertices_804, vertices_344, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_385, vertices_769, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_532, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_328, vertices_584, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_227), (false, vertices_803), (false, vertices_781), (false, vertices_457), (false, vertices_433), (true, vertices_642), (true, vertices_28), (true, vertices_52), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_88), (true, vertices_280), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 0 3 5 6 8 722 194 1
cert_row_4 1 1 2 3 4 7 316 28 3
cert_row_4 2 1 2 3 5 8 604 28 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 0 0 3 5 6 194 722 1
cert_coverFacet 1 674
cert_cover_2 1 4 0 6 8 162 674 3
cert_coverFacet 2 316
cert_cover_5 2 1 1 2 3 4 28 316 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 28 604 3
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0083

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 805, 709, 121, 561, 593, 481, 654, 774, 570, 362, 458, 802, 728, 133, 261, 517, 49, 81, 529, 97, 289, 545, 193, 577, 385, 134, 262, 518, 42, 330, 138, 522, 290, 546, 386, 770, 644, 772, 56, 88, 536, 104, 200, 648, 560, 592, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_805, vertices_709, vertices_121, vertices_561, vertices_593, vertices_481, vertices_654, vertices_774, vertices_570, vertices_362, vertices_458, vertices_802, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_81, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_134, vertices_262, vertices_518, vertices_42, vertices_330, vertices_138, vertices_522, vertices_290, vertices_546, vertices_386, vertices_770, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_200, vertices_648, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_805), (false, vertices_709), (false, vertices_121), (false, vertices_561), (false, vertices_593), (false, vertices_481), (true, vertices_518), (true, vertices_42), (true, vertices_330), (true, vertices_138), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_536), (true, vertices_200), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_330) then 14 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_648) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 0 2 5 7 330
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 0 2 3 4 8 570 42 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 42 570 2
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 42 362 3
cert_coverFacet 4 458
cert_cover_5 4 0 0 2 5 6 330 458 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0004

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 403, 227, 611, 181, 817, 590, 458, 332, 780, 564, 468, 788, 740, 99, 131, 259, 515, 49, 145, 273, 161, 545, 769, 74, 266, 522, 194, 578, 386, 76, 268, 524, 52, 148, 276, 532, 164, 548, 196, 324, 580, 772, 328, 776, 560, 400, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_403, vertices_227, vertices_611, vertices_181, vertices_817, vertices_590, vertices_458, vertices_332, vertices_780, vertices_564, vertices_468, vertices_788, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_769, vertices_74, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_76, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_772, vertices_328, vertices_776, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_403), (false, vertices_227), (false, vertices_611), (false, vertices_181), (false, vertices_817), (true, vertices_74), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_328), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 15 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_611) then 20 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
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
cert_row_4 0 1 3 5 6 7 468 148 2
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 0 1 2 5 8 590 74 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 74 590 1
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 332
cert_cover_2 2 2 1 5 7 76 332 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 468
cert_cover_5 5 0 1 3 5 6 148 468 2
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 164 740 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0005

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 589, 329, 777, 817, 465, 737, 782, 406, 230, 614, 562, 786, 460, 73, 265, 521, 49, 145, 273, 161, 545, 193, 321, 577, 769, 102, 134, 262, 518, 50, 146, 274, 530, 162, 546, 770, 76, 268, 524, 196, 580, 388, 328, 776, 560, 400, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_589, vertices_329, vertices_777, vertices_817, vertices_465, vertices_737, vertices_782, vertices_406, vertices_230, vertices_614, vertices_562, vertices_786, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_102, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_770, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_328, vertices_776, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_589), (false, vertices_329), (false, vertices_777), (false, vertices_817), (false, vertices_465), (false, vertices_737), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_268), (true, vertices_196), (true, vertices_388)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 18 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 13 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_102) then 14 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 1 2 7 8 782 262 2
cert_row_4 2 0 1 3 6 7 406 134 2
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 262 782 2
cert_coverFacet 1 406
cert_cover_5 1 2 0 1 3 6 134 406 2
cert_coverFacet 2 230
cert_cover_5 2 0 0 1 4 6 102 230 3
cert_coverFacet 3 614
cert_cover_5 3 0 0 1 4 8 102 614 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0008

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 395, 803, 565, 357, 453, 714, 778, 124, 724, 568, 600, 488, 808, 131, 259, 515, 37, 325, 133, 517, 289, 545, 385, 138, 266, 522, 642, 770, 52, 84, 532, 100, 196, 644, 56, 88, 536, 104, 296, 552, 200, 584, 392, 776, 560, 592, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_395, vertices_803, vertices_565, vertices_357, vertices_453, vertices_714, vertices_778, vertices_124, vertices_724, vertices_568, vertices_600, vertices_488, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_325, vertices_133, vertices_517, vertices_289, vertices_545, vertices_385, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_100, vertices_196, vertices_644, vertices_56, vertices_88, vertices_536, vertices_104, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_776, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_395), (false, vertices_803), (false, vertices_565), (false, vertices_357), (false, vertices_453), (true, vertices_522), (true, vertices_84), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_776), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_56) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 1 2 3 4 5 124 52 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 0 0 2 5 6 138 714 2
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 4 52 124 1
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0009

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 61, 541, 421, 837, 361, 902, 666, 202, 482, 834, 692, 184, 232, 29, 37, 261, 517, 41, 73, 521, 289, 321, 577, 74, 138, 522, 194, 322, 578, 386, 642, 770, 52, 532, 164, 388, 644, 772, 56, 152, 536, 104, 168, 200, 176, 656, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_61, vertices_541, vertices_421, vertices_837, vertices_361, vertices_902, vertices_666, vertices_202, vertices_482, vertices_834, vertices_692, vertices_184, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_261, vertices_517, vertices_41, vertices_73, vertices_521, vertices_289, vertices_321, vertices_577, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_200, vertices_176, vertices_656, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_61), (false, vertices_541), (false, vertices_421), (false, vertices_837), (false, vertices_361), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 138 2 194 1 322 386 642 770 644 152 168 200 176 656 224 587 61 541 361 421 837
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 138 666 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 194 482 1
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0017

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [79, 535, 195, 899, 525, 809, 457, 214, 690, 364, 556, 244, 564, 992, 7, 67, 131, 515, 13, 517, 73, 265, 521, 193, 385, 769, 22, 70, 146, 530, 194, 642, 44, 76, 524, 52, 212, 532, 100, 548, 296, 552, 328, 176, 560, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_79, vertices_535, vertices_195, vertices_899, vertices_525, vertices_809, vertices_457, vertices_214, vertices_690, vertices_364, vertices_556, vertices_244, vertices_564, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_131, vertices_515, vertices_13, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_385, vertices_769, vertices_22, vertices_70, vertices_146, vertices_530, vertices_194, vertices_642, vertices_44, vertices_76, vertices_524, vertices_52, vertices_212, vertices_532, vertices_100, vertices_548, vertices_296, vertices_552, vertices_328, vertices_176, vertices_560, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_79), (false, vertices_535), (false, vertices_195), (false, vertices_899), (false, vertices_525), (false, vertices_809), (false, vertices_457), (true, vertices_146), (true, vertices_44), (true, vertices_52), (true, vertices_212), (true, vertices_100), (true, vertices_548), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_79) then 13 else
  if p.val = (false, vertices_535) then 14 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_79), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_2 1 1 3 5 6 212
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 690
cert_cover_5 1 0 0 3 4 6 146 690 2
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 44 364 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0023

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0025.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 661, 613, 453, 121, 217, 58, 666, 298, 778, 866, 908, 836, 488, 69, 133, 517, 89, 49, 145, 529, 97, 545, 193, 26, 42, 266, 522, 50, 530, 290, 546, 770, 324, 580, 388, 644, 772, 56, 152, 104, 296, 200, 392, 648, 776, 656, 352, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_661, vertices_613, vertices_453, vertices_121, vertices_217, vertices_58, vertices_666, vertices_298, vertices_778, vertices_866, vertices_908, vertices_836, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_89, vertices_49, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_104, vertices_296, vertices_200, vertices_392, vertices_648, vertices_776, vertices_656, vertices_352, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_661), (false, vertices_613), (false, vertices_453), (false, vertices_121), (false, vertices_217), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_770), (true, vertices_772), (true, vertices_296), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 26 1 42 2 266 522 290 770 772 296 392 648 776 352 832 563 661 613 453 121 217
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 26 3
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 1 2 6 7 8 908 388 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 58
cert_cover_2 0 2 0 3 4 26 58 3
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 26 666 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 290 866 2
cert_coverFacet 5 908
cert_cover_5 5 2 1 2 6 7 388 908 1
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0025

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0031.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0031

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 405, 677, 837, 313, 809, 454, 122, 338, 402, 226, 708, 856, 744, 133, 261, 517, 297, 49, 145, 273, 161, 545, 769, 50, 82, 146, 274, 98, 162, 194, 322, 386, 196, 324, 580, 388, 644, 56, 88, 280, 104, 552, 584, 776, 336, 400, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_405, vertices_677, vertices_837, vertices_313, vertices_809, vertices_454, vertices_122, vertices_338, vertices_402, vertices_226, vertices_708, vertices_856, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_297, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_769, vertices_50, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_194, vertices_322, vertices_386, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_104, vertices_552, vertices_584, vertices_776, vertices_336, vertices_400, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_405), (false, vertices_677), (false, vertices_837), (false, vertices_313), (false, vertices_809), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_196), (true, vertices_88), (true, vertices_104), (true, vertices_584), (true, vertices_336), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 14 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 82 1 274 2 98 194 322 386 196 88 104 584 336 224 704 179 405 677 837 313 809
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_4 1 0 2 3 4 5 122 50 1
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 50 122 1
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 88 856 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0031

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 805, 217, 681, 841, 177, 305, 678, 838, 390, 602, 666, 402, 436, 73, 137, 521, 49, 81, 145, 273, 161, 289, 545, 321, 769, 134, 262, 518, 538, 82, 146, 274, 322, 578, 386, 642, 164, 292, 548, 388, 772, 88, 152, 584, 648, 176, 304, 400, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_805, vertices_217, vertices_681, vertices_841, vertices_177, vertices_305, vertices_678, vertices_838, vertices_390, vertices_602, vertices_666, vertices_402, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_49, vertices_81, vertices_145, vertices_273, vertices_161, vertices_289, vertices_545, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_538, vertices_82, vertices_146, vertices_274, vertices_322, vertices_578, vertices_386, vertices_642, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_152, vertices_584, vertices_648, vertices_176, vertices_304, vertices_400, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_805), (false, vertices_217), (false, vertices_681), (false, vertices_841), (false, vertices_177), (false, vertices_305), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_538), (true, vertices_146), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_217) then 18 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_538) then 14 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_538), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 8 538
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_4 2 0 1 4 6 8 678 134 2
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 134 678 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 262 838 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 602
cert_cover_5 3 0 0 2 3 5 538 602 3
cert_coverFacet 4 666
cert_cover_5 4 0 0 2 3 6 538 666 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0032

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 653, 213, 773, 849, 737, 62, 526, 774, 682, 306, 866, 188, 496, 21, 133, 261, 517, 81, 273, 193, 577, 641, 769, 14, 22, 262, 518, 42, 522, 50, 274, 290, 546, 770, 60, 140, 524, 148, 772, 168, 648, 176, 304, 208, 336, 224, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_653, vertices_213, vertices_773, vertices_849, vertices_737, vertices_62, vertices_526, vertices_774, vertices_682, vertices_306, vertices_866, vertices_188, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_81, vertices_273, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_42, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_60, vertices_140, vertices_524, vertices_148, vertices_772, vertices_168, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_653), (false, vertices_213), (false, vertices_773), (false, vertices_849), (false, vertices_737), (true, vertices_14), (true, vertices_518), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_60), (true, vertices_168), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_60) then 18 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 42 682 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 290 866 2
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 6 60 188 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0040

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 651, 531, 419, 541, 333, 457, 306, 562, 738, 716, 628, 340, 496, 19, 131, 259, 515, 13, 21, 261, 329, 137, 521, 529, 385, 50, 274, 530, 162, 290, 546, 642, 76, 524, 84, 276, 532, 324, 580, 200, 648, 112, 304, 560, 336, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_651, vertices_531, vertices_419, vertices_541, vertices_333, vertices_457, vertices_306, vertices_562, vertices_738, vertices_716, vertices_628, vertices_340, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_13, vertices_21, vertices_261, vertices_329, vertices_137, vertices_521, vertices_529, vertices_385, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_76, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_200, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_651), (false, vertices_531), (false, vertices_419), (false, vertices_541), (false, vertices_333), (false, vertices_457), (true, vertices_50), (true, vertices_546), (true, vertices_84), (true, vertices_580), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_224), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
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
cert_row_4 0 0 4 5 6 8 738 162 2
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 306
cert_cover_2 0 3 0 4 7 50 306 3
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 738
cert_cover_5 2 0 0 4 5 6 162 738 2
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 76 716 3
cert_coverFacet 4 628
cert_cover_5 4 2 1 3 4 5 84 628 2
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0043

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 661, 617, 849, 401, 481, 302, 558, 406, 646, 418, 604, 284, 376, 145, 273, 529, 97, 161, 545, 321, 577, 385, 641, 46, 134, 262, 518, 162, 290, 546, 386, 642, 28, 268, 524, 148, 276, 532, 644, 88, 280, 104, 296, 552, 584, 336, 592, 400, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_661, vertices_617, vertices_849, vertices_401, vertices_481, vertices_302, vertices_558, vertices_406, vertices_646, vertices_418, vertices_604, vertices_284, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_644, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_584, vertices_336, vertices_592, vertices_400, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_661), (false, vertices_617), (false, vertices_849), (false, vertices_401), (false, vertices_481), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (false, vertices_401) then 0 else
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
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 401 134 262 518 290 386 28 268 524 276 88 280 296 675 46 661 617 849 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
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
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 134 406 2
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0048

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0051.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0051

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 661, 773, 185, 281, 809, 838, 234, 362, 722, 802, 596, 472, 21, 261, 517, 25, 41, 265, 145, 273, 161, 545, 641, 769, 106, 162, 290, 546, 194, 322, 578, 642, 770, 84, 532, 324, 580, 772, 152, 280, 168, 296, 200, 328, 208, 336, 592, 656, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_661, vertices_773, vertices_185, vertices_281, vertices_809, vertices_838, vertices_234, vertices_362, vertices_722, vertices_802, vertices_596, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_145, vertices_273, vertices_161, vertices_545, vertices_641, vertices_769, vertices_106, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_208, vertices_336, vertices_592, vertices_656, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_661), (false, vertices_773), (false, vertices_185), (false, vertices_281), (false, vertices_809), (true, vertices_106), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_580), (true, vertices_200), (true, vertices_328), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 13 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (true, vertices_106) then 14 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 773 1 281 290 194 322 578 770 580 200 328 208 592 675 106 341 661 185 809
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 3 5 6 8 722 194 1
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 6 106 234 3
cert_coverFacet 2 362
cert_cover_5 2 0 0 2 4 7 106 362 3
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 194 722 1
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 152 472 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0051

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 525, 421, 773, 713, 241, 542, 310, 774, 434, 722, 60, 632, 13, 37, 261, 517, 73, 521, 97, 161, 193, 385, 641, 769, 22, 262, 518, 306, 146, 530, 386, 642, 770, 28, 44, 524, 52, 292, 772, 56, 536, 104, 584, 112, 176, 208, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_525, vertices_421, vertices_773, vertices_713, vertices_241, vertices_542, vertices_310, vertices_774, vertices_434, vertices_722, vertices_60, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_73, vertices_521, vertices_97, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_306, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_524, vertices_52, vertices_292, vertices_772, vertices_56, vertices_536, vertices_104, vertices_584, vertices_112, vertices_176, vertices_208, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_525), (false, vertices_421), (false, vertices_773), (false, vertices_713), (false, vertices_241), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_306), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_52), (true, vertices_56), (true, vertices_536), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_109) then 16 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_306) then 14 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 525 1 773 22 262 518 146 530 28 52 56 536 592 899 306 109 421 713 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 7 306
cert_row_4 1 0 1 2 3 8 542 22 2
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 22 542 2
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 4 22 310 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 6 306 434 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 56 632 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0058

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 539, 355, 547, 533, 805, 453, 218, 234, 554, 212, 916, 696, 992, 19, 35, 67, 515, 21, 69, 261, 517, 529, 289, 545, 321, 26, 42, 202, 522, 82, 98, 546, 84, 148, 532, 196, 388, 772, 152, 536, 168, 552, 208, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_539, vertices_355, vertices_547, vertices_533, vertices_805, vertices_453, vertices_218, vertices_234, vertices_554, vertices_212, vertices_916, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_515, vertices_21, vertices_69, vertices_261, vertices_517, vertices_529, vertices_289, vertices_545, vertices_321, vertices_26, vertices_42, vertices_202, vertices_522, vertices_82, vertices_98, vertices_546, vertices_84, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_539), (false, vertices_355), (false, vertices_547), (false, vertices_533), (false, vertices_805), (false, vertices_453), (true, vertices_42), (true, vertices_202), (true, vertices_148), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_208), (true, vertices_656), (true, vertices_224), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 13 else
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_453) then 15 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
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
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 2 3 4 6 8 696 152 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 0 0 2 3 5 26 218 3
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 5 42 234 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 152 696 2
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0059

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0061.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0061

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 535, 589, 229, 689, 961, 302, 526, 842, 306, 914, 332, 356, 496, 23, 37, 69, 517, 49, 529, 161, 193, 577, 641, 14, 38, 518, 266, 522, 50, 274, 530, 290, 770, 76, 268, 524, 100, 292, 324, 328, 584, 176, 304, 400, 656, 224, 352, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_535, vertices_589, vertices_229, vertices_689, vertices_961, vertices_302, vertices_526, vertices_842, vertices_306, vertices_914, vertices_332, vertices_356, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_69, vertices_517, vertices_49, vertices_529, vertices_161, vertices_193, vertices_577, vertices_641, vertices_14, vertices_38, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_324, vertices_328, vertices_584, vertices_176, vertices_304, vertices_400, vertices_656, vertices_224, vertices_352, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_535), (false, vertices_589), (false, vertices_229), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_324), (true, vertices_328), (true, vertices_304), (true, vertices_400), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 7 302 14 3
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 14 302 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 266 842 2
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 914
cert_cover_5 4 2 0 3 6 7 274 914 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0061

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 295, 675, 405, 665, 481, 358, 582, 610, 844, 788, 472, 792, 744, 7, 35, 515, 21, 261, 145, 529, 161, 289, 385, 641, 294, 70, 518, 98, 546, 578, 276, 532, 324, 580, 772, 152, 280, 536, 200, 328, 584, 648, 776, 400, 784, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_295, vertices_675, vertices_405, vertices_665, vertices_481, vertices_358, vertices_582, vertices_610, vertices_844, vertices_788, vertices_472, vertices_792, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_515, vertices_21, vertices_261, vertices_145, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_294, vertices_70, vertices_518, vertices_98, vertices_546, vertices_578, vertices_276, vertices_532, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_400, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_295), (false, vertices_675), (false, vertices_405), (false, vertices_665), (false, vertices_481), (true, vertices_70), (true, vertices_98), (true, vertices_578), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 14 else
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 0 1 4 7 294
cert_row_4 1 1 2 5 7 8 844 324 1
cert_row_4 2 2 3 5 6 7 472 152 2
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 294 358 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 324 844 1
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 152 472 2
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 200 744 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0071

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [47, 171, 29, 341, 421, 601, 457, 526, 550, 714, 930, 540, 820, 976, 43, 13, 21, 37, 261, 25, 73, 137, 81, 161, 321, 385, 14, 38, 518, 138, 522, 162, 546, 642, 28, 524, 276, 532, 292, 548, 536, 200, 584, 336, 592, 784, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_47, vertices_171, vertices_29, vertices_341, vertices_421, vertices_601, vertices_457, vertices_526, vertices_550, vertices_714, vertices_930, vertices_540, vertices_820, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_13, vertices_21, vertices_37, vertices_261, vertices_25, vertices_73, vertices_137, vertices_81, vertices_161, vertices_321, vertices_385, vertices_14, vertices_38, vertices_518, vertices_138, vertices_522, vertices_162, vertices_546, vertices_642, vertices_28, vertices_524, vertices_276, vertices_532, vertices_292, vertices_548, vertices_536, vertices_200, vertices_584, vertices_336, vertices_592, vertices_784, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_47), (false, vertices_171), (false, vertices_29), (false, vertices_341), (false, vertices_421), (false, vertices_601), (false, vertices_457), (true, vertices_518), (true, vertices_522), (true, vertices_546), (true, vertices_642), (true, vertices_524), (true, vertices_532), (true, vertices_548), (true, vertices_784), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_47) then 13 else
  if p.val = (false, vertices_171) then 14 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_47), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 1 3 4 7 8 820 276 2
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 550
cert_cover_2 1 1 0 4 8 38 550 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 138 714 2
cert_coverFacet 3 930
cert_cover_5 3 1 0 4 6 7 162 930 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 820
cert_cover_5 5 2 1 3 4 7 276 820 2
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 336 976 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0072

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 147, 835, 387, 453, 617, 241, 790, 402, 668, 236, 844, 404, 696, 19, 131, 259, 515, 49, 145, 97, 545, 193, 321, 577, 385, 146, 274, 530, 386, 770, 76, 140, 524, 148, 276, 532, 196, 324, 388, 772, 664, 104, 168, 552, 584, 176, 560, 400, 224, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_147, vertices_835, vertices_387, vertices_453, vertices_617, vertices_241, vertices_790, vertices_402, vertices_668, vertices_236, vertices_844, vertices_404, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_76, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_772, vertices_664, vertices_104, vertices_168, vertices_552, vertices_584, vertices_176, vertices_560, vertices_400, vertices_224, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_147), (false, vertices_835), (false, vertices_387), (false, vertices_453), (false, vertices_617), (false, vertices_241), (true, vertices_274), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_664), (true, vertices_168), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 13 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_664) then 19 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 2 4 5 6 236 76 2
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 0 3 4 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 140 668 2
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 76 236 2
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 76 844 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 696
cert_cover_5 6 1 2 3 4 6 664 696 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0076

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0093.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0093

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 203, 661, 569, 905, 241, 454, 810, 394, 370, 820, 212, 340, 900, 75, 41, 137, 521, 49, 145, 529, 97, 193, 641, 42, 138, 266, 98, 290, 194, 322, 386, 84, 148, 276, 532, 196, 324, 388, 644, 772, 552, 392, 776, 112, 304, 560, 208, 336, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_203, vertices_661, vertices_569, vertices_905, vertices_241, vertices_454, vertices_810, vertices_394, vertices_370, vertices_820, vertices_212, vertices_340, vertices_900] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_41, vertices_137, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_193, vertices_641, vertices_42, vertices_138, vertices_266, vertices_98, vertices_290, vertices_194, vertices_322, vertices_386, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_552, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_203), (false, vertices_661), (false, vertices_569), (false, vertices_905), (false, vertices_241), (true, vertices_266), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_772), (true, vertices_304), (true, vertices_336), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 0 3 4 5 7 370 98 1
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 42 810 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 98 370 1
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 276 820 2
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0093

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0096.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0096

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 653, 805, 389, 217, 841, 401, 678, 602, 666, 178, 306, 866, 436, 133, 261, 517, 73, 137, 521, 81, 145, 273, 321, 385, 769, 538, 50, 82, 146, 274, 162, 290, 546, 322, 578, 642, 164, 292, 548, 388, 644, 88, 152, 584, 648, 176, 304, 400, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_653, vertices_805, vertices_389, vertices_217, vertices_841, vertices_401, vertices_678, vertices_602, vertices_666, vertices_178, vertices_306, vertices_866, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_273, vertices_321, vertices_385, vertices_769, vertices_538, vertices_50, vertices_82, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_642, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_88, vertices_152, vertices_584, vertices_648, vertices_176, vertices_304, vertices_400, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_653), (false, vertices_805), (false, vertices_389), (false, vertices_217), (false, vertices_841), (false, vertices_401), (true, vertices_538), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_164), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_538) then 14 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 389 1 401 50 146 162 290 546 578 642 164 176 304 339 538 653 805 217 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 8 538
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 0 1 4 6 8 678 162 1
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 162 678 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 538 602 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 538 666 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 290 866 2
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0096

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0097.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0097

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 309, 213, 645, 773, 121, 865, 902, 218, 410, 618, 778, 404, 824, 21, 133, 261, 517, 49, 81, 97, 289, 193, 577, 641, 769, 154, 74, 266, 522, 194, 578, 386, 642, 770, 148, 276, 388, 644, 772, 56, 88, 280, 104, 552, 776, 304, 208, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_309, vertices_213, vertices_645, vertices_773, vertices_121, vertices_865, vertices_902, vertices_218, vertices_410, vertices_618, vertices_778, vertices_404, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_81, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_154, vertices_74, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_148, vertices_276, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_552, vertices_776, vertices_304, vertices_208, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_309), (false, vertices_213), (false, vertices_645), (false, vertices_773), (false, vertices_121), (false, vertices_865), (true, vertices_154), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_770), (true, vertices_388), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_154) then 14 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 0 2 3 6 154
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 154 218 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 7 154 410 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0097

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0109.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0109

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 787, 355, 557, 533, 101, 929, 722, 962, 220, 540, 172, 484, 696, 19, 67, 259, 21, 37, 69, 517, 529, 97, 289, 545, 769, 82, 530, 706, 322, 770, 28, 44, 140, 524, 84, 532, 100, 164, 196, 152, 536, 168, 552, 208, 656, 352, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_787, vertices_355, vertices_557, vertices_533, vertices_101, vertices_929, vertices_722, vertices_962, vertices_220, vertices_540, vertices_172, vertices_484, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_21, vertices_37, vertices_69, vertices_517, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_82, vertices_530, vertices_706, vertices_322, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_84, vertices_532, vertices_100, vertices_164, vertices_196, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_656, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_787), (false, vertices_355), (false, vertices_557), (false, vertices_533), (false, vertices_101), (false, vertices_929), (true, vertices_706), (true, vertices_28), (true, vertices_140), (true, vertices_164), (true, vertices_196), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_208), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 13 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_557) then 14 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_101) then 1 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_706) then 18 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
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
cert_row_2 0 0 5 6 8 706
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_4 2 1 2 3 5 6 220 28 3
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 0 0 3 5 6 82 722 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 706 962 3
cert_coverFacet 2 220
cert_cover_5 2 2 1 2 3 5 28 220 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 100 484 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 152 696 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0109

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0111.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0111

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 597, 809, 369, 913, 174, 558, 214, 582, 226, 908, 660, 488, 464, 81, 273, 529, 97, 289, 545, 577, 769, 46, 70, 134, 518, 98, 162, 546, 194, 578, 140, 524, 84, 148, 532, 580, 644, 168, 296, 552, 392, 776, 208, 336, 400, 656, 224, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_597, vertices_809, vertices_369, vertices_913, vertices_174, vertices_558, vertices_214, vertices_582, vertices_226, vertices_908, vertices_660, vertices_488, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_46, vertices_70, vertices_134, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_597), (false, vertices_809), (false, vertices_369), (false, vertices_913), (true, vertices_46), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_194), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 70 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 1 2 6 7 8 908 140 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 214
cert_cover_5 2 0 0 1 3 5 70 214 2
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 908
cert_cover_5 5 2 1 2 6 7 140 908 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0111

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0114.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0114

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 789, 709, 433, 209, 206, 590, 570, 426, 178, 210, 812, 816, 133, 261, 517, 81, 145, 273, 529, 193, 577, 385, 78, 42, 138, 522, 50, 82, 146, 530, 162, 194, 578, 140, 268, 524, 196, 580, 772, 296, 552, 392, 176, 304, 560, 208, 784, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_789, vertices_709, vertices_433, vertices_209, vertices_206, vertices_590, vertices_570, vertices_426, vertices_178, vertices_210, vertices_812, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_78, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_772, vertices_296, vertices_552, vertices_392, vertices_176, vertices_304, vertices_560, vertices_208, vertices_784, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_789), (false, vertices_709), (false, vertices_433), (false, vertices_209), (true, vertices_78), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_194), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (true, vertices_78) then 15 else
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
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
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
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0114

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0118.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0118

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 901, 601, 457, 785, 737, 110, 334, 790, 678, 538, 554, 484, 616, 25, 73, 265, 273, 529, 193, 577, 385, 641, 769, 78, 38, 262, 518, 26, 42, 266, 522, 274, 530, 546, 100, 164, 324, 388, 644, 772, 536, 104, 552, 328, 584, 784, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_901, vertices_601, vertices_457, vertices_785, vertices_737, vertices_110, vertices_334, vertices_790, vertices_678, vertices_538, vertices_554, vertices_484, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_546, vertices_100, vertices_164, vertices_324, vertices_388, vertices_644, vertices_772, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_901), (false, vertices_601), (false, vertices_457), (false, vertices_785), (false, vertices_737), (true, vertices_78), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_522), (true, vertices_530), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_324), (true, vertices_104), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_552) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 1 0 1 3 7 8 790 262 2
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 78 110 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 790
cert_cover_5 2 1 0 1 3 7 262 790 2
cert_coverFacet 3 678
cert_cover_5 3 2 0 1 4 6 38 678 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0118

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0240 : Certifies 240 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0241 : Certifies 241 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0242 : Certifies 242 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0243 : Certifies 243 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0083.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0244 : Certifies 244 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0245 : Certifies 245 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0246 : Certifies 246 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0247 : Certifies 247 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0248 : Certifies 248 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0249 : Certifies 249 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0250 : Certifies 250 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0025.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0251 : Certifies 251 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0031.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0252 : Certifies 252 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0253 : Certifies 253 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0254 : Certifies 254 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0255 : Certifies 255 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0256 : Certifies 256 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0051.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0257 : Certifies 257 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0258 : Certifies 258 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0259 : Certifies 259 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0061.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0260 : Certifies 260 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0261 : Certifies 261 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0262 : Certifies 262 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0263 : Certifies 263 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0093.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0264 : Certifies 264 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0096.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0265 : Certifies 265 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0097.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0266 : Certifies 266 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0109.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0267 : Certifies 267 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0111.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0268 : Certifies 268 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0114.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0269 : Certifies 269 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0118.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B008 (j : Fin 30) :
    Certifies (240 + j.val) := by
  fin_cases j
  · exact projection_0240
  · exact projection_0241
  · exact projection_0242
  · exact projection_0243
  · exact projection_0244
  · exact projection_0245
  · exact projection_0246
  · exact projection_0247
  · exact projection_0248
  · exact projection_0249
  · exact projection_0250
  · exact projection_0251
  · exact projection_0252
  · exact projection_0253
  · exact projection_0254
  · exact projection_0255
  · exact projection_0256
  · exact projection_0257
  · exact projection_0258
  · exact projection_0259
  · exact projection_0260
  · exact projection_0261
  · exact projection_0262
  · exact projection_0263
  · exact projection_0264
  · exact projection_0265
  · exact projection_0266
  · exact projection_0267
  · exact projection_0268
  · exact projection_0269

end Nonrational.TerminalVerification
