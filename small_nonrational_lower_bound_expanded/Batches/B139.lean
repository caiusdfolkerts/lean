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
/- Source: ProjectionCertificates/R_m16e10q1_0314.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0314

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 781, 341, 149, 677, 409, 169, 838, 234, 458, 778, 626, 596, 660, 496, 688, 21, 133, 261, 517, 41, 137, 265, 521, 145, 273, 161, 545, 42, 202, 266, 522, 98, 546, 322, 578, 770, 84, 148, 532, 324, 580, 644, 772, 168, 392, 776, 112, 176, 560, 336, 592, 400, 656, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_781, vertices_341, vertices_149, vertices_677, vertices_409, vertices_169, vertices_838, vertices_234, vertices_458, vertices_778, vertices_626, vertices_596, vertices_660, vertices_496, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_161, vertices_545, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_532, vertices_324, vertices_580, vertices_644, vertices_772, vertices_168, vertices_392, vertices_776, vertices_112, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_781), (false, vertices_341), (false, vertices_149), (false, vertices_677), (false, vertices_409), (false, vertices_169), (true, vertices_202), (true, vertices_266), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_580), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 149 1 169 266 98 322 578 770 532 580 112 176 560 592 656 224 448 555 202 781 341 677 409
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 3 4 5 8 626 98 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 5 42 234 3
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 7 202 458 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 98 626 1
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0314

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0315.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0315

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 171, 355, 771, 837, 649, 737, 790, 282, 298, 412, 428, 244, 596, 356, 728, 11, 35, 259, 515, 137, 521, 97, 161, 321, 577, 641, 769, 26, 42, 266, 274, 530, 290, 770, 396, 84, 148, 276, 532, 100, 164, 292, 324, 580, 772, 152, 280, 536, 168, 296, 648, 208, 592, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_171, vertices_355, vertices_771, vertices_837, vertices_649, vertices_737, vertices_790, vertices_282, vertices_298, vertices_412, vertices_428, vertices_244, vertices_596, vertices_356, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_137, vertices_521, vertices_97, vertices_161, vertices_321, vertices_577, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_274, vertices_530, vertices_290, vertices_770, vertices_396, vertices_84, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_648, vertices_208, vertices_592, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_171), (false, vertices_355), (false, vertices_771), (false, vertices_837), (false, vertices_649), (false, vertices_737), (true, vertices_266), (true, vertices_274), (true, vertices_396), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_171) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_396) then 22 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 1 2 6 7 396
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 412
cert_cover_5 3 1 1 2 3 6 396 412 2
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 396 428 2
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 84 244 2
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 152 728 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0315

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0316.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0316

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 563, 451, 771, 533, 709, 841, 810, 434, 60, 156, 108, 460, 628, 440, 616, 19, 131, 259, 515, 21, 133, 517, 529, 193, 321, 577, 769, 50, 146, 290, 546, 386, 770, 28, 44, 76, 140, 52, 148, 532, 100, 196, 580, 56, 152, 104, 296, 552, 328, 584, 392, 776, 432, 560, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_563, vertices_451, vertices_771, vertices_533, vertices_709, vertices_841, vertices_810, vertices_434, vertices_60, vertices_156, vertices_108, vertices_460, vertices_628, vertices_440, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_21, vertices_133, vertices_517, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_50, vertices_146, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_52, vertices_148, vertices_532, vertices_100, vertices_196, vertices_580, vertices_56, vertices_152, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_776, vertices_432, vertices_560, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_563), (false, vertices_451), (false, vertices_771), (false, vertices_533), (false, vertices_709), (false, vertices_841), (true, vertices_290), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_52), (true, vertices_100), (true, vertices_56), (true, vertices_152), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_392), (true, vertices_432), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_432) then 25 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 290 1
cert_row_4 1 1 2 5 6 7 460 76 3
cert_row_2 2 3 4 6 7 432
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 2 6 1
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 0 0 2 4 7 290 810 1
cert_coverFacet 1 434
cert_cover_5 1 2 0 3 4 6 50 434 3
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 6 76 460 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 440
cert_cover_5 7 2 2 3 4 6 56 440 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0316

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0317.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0317

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 595, 275, 675, 333, 341, 617, 790, 418, 898, 220, 428, 660, 900, 232, 752, 19, 35, 259, 515, 325, 41, 73, 265, 81, 273, 545, 577, 274, 530, 162, 290, 386, 642, 770, 76, 140, 268, 84, 148, 276, 532, 388, 644, 772, 104, 168, 296, 200, 208, 592, 656, 224, 608, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_595, vertices_275, vertices_675, vertices_333, vertices_341, vertices_617, vertices_790, vertices_418, vertices_898, vertices_220, vertices_428, vertices_660, vertices_900, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_325, vertices_41, vertices_73, vertices_265, vertices_81, vertices_273, vertices_545, vertices_577, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_200, vertices_208, vertices_592, vertices_656, vertices_224, vertices_608, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_595), (false, vertices_275), (false, vertices_675), (false, vertices_333), (false, vertices_341), (false, vertices_617), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_148), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_168), (true, vertices_200), (true, vertices_208), (true, vertices_656), (true, vertices_224), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 1 2 4 6 7 428 140 2
cert_row_4 2 1 2 3 5 6 220 76 2
cert_row_4 3 3 4 5 6 8 752 208 1
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 418
cert_cover_2 1 4 0 6 7 162 418 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 76 220 2
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 140 428 2
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 208 752 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0317

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0318.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0318

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 179, 707, 771, 837, 305, 481, 782, 538, 658, 188, 668, 108, 332, 740, 376, 19, 131, 259, 515, 49, 273, 161, 289, 193, 321, 577, 769, 26, 266, 522, 146, 530, 642, 770, 156, 44, 76, 268, 524, 100, 164, 324, 580, 644, 772, 56, 280, 536, 104, 328, 176, 304, 656, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_179, vertices_707, vertices_771, vertices_837, vertices_305, vertices_481, vertices_782, vertices_538, vertices_658, vertices_188, vertices_668, vertices_108, vertices_332, vertices_740, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_769, vertices_26, vertices_266, vertices_522, vertices_146, vertices_530, vertices_642, vertices_770, vertices_156, vertices_44, vertices_76, vertices_268, vertices_524, vertices_100, vertices_164, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_328, vertices_176, vertices_304, vertices_656, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_179), (false, vertices_707), (false, vertices_771), (false, vertices_837), (false, vertices_305), (false, vertices_481), (true, vertices_522), (true, vertices_530), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_164), (true, vertices_644), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_328), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 17 else
  if p.val = (false, vertices_179) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_156) then 22 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 1 4 5 6 8 740 100 3
cert_row_2 2 1 2 3 6 156
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 4 156 188 3
cert_coverFacet 4 668
cert_cover_5 4 2 1 2 3 8 156 668 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 740
cert_cover_5 7 1 1 4 5 6 100 740 3
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 56 376 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0318

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0319.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0319

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 789, 229, 581, 681, 777, 598, 218, 282, 234, 298, 818, 468, 408, 808, 69, 133, 261, 517, 137, 265, 521, 97, 161, 545, 577, 769, 26, 42, 202, 266, 82, 274, 530, 98, 290, 546, 578, 84, 276, 532, 196, 580, 388, 152, 280, 168, 296, 552, 392, 776, 208, 400, 784, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_789, vertices_229, vertices_581, vertices_681, vertices_777, vertices_598, vertices_218, vertices_282, vertices_234, vertices_298, vertices_818, vertices_468, vertices_408, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_577, vertices_769, vertices_26, vertices_42, vertices_202, vertices_266, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_400, vertices_784, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_789), (false, vertices_229), (false, vertices_581), (false, vertices_681), (false, vertices_777), (true, vertices_26), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_84), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_208), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 581 1 777 26 42 266 82 274 530 290 84 152 280 296 208 400 800 611 202 397 789 229 681
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 1 3 5 8 598 82 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 82 598 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 5 42 234 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 818
cert_cover_5 5 1 0 3 4 7 274 818 2
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0319

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0320.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0320

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 397, 613, 165, 153, 721, 422, 794, 370, 626, 898, 364, 344, 664, 904, 13, 37, 69, 133, 25, 137, 81, 145, 161, 545, 577, 641, 114, 274, 530, 162, 290, 546, 386, 642, 770, 76, 268, 100, 164, 292, 388, 88, 152, 280, 536, 328, 392, 648, 776, 336, 592, 656, 352, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_397, vertices_613, vertices_165, vertices_153, vertices_721, vertices_422, vertices_794, vertices_370, vertices_626, vertices_898, vertices_364, vertices_344, vertices_664, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_133, vertices_25, vertices_137, vertices_81, vertices_145, vertices_161, vertices_545, vertices_577, vertices_641, vertices_114, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_100, vertices_164, vertices_292, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_392, vertices_648, vertices_776, vertices_336, vertices_592, vertices_656, vertices_352, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_397), (false, vertices_613), (false, vertices_165), (false, vertices_153), (false, vertices_721), (true, vertices_114), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_292), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_648), (true, vertices_776), (true, vertices_336), (true, vertices_352), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_114) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 165 1 153 274 530 290 386 770 292 280 536 328 648 776 336 352 896 675 114 93 397 613 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 162 1
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_2 2 0 3 4 5 114
cert_row_4 3 1 2 4 5 7 364 76 2
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 370
cert_cover_5 2 2 0 3 4 7 114 370 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 8 114 626 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 76 364 2
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 904
cert_cover_2 8 6 2 7 8 392 904 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0320

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0321.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0321

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 531, 899, 565, 453, 581, 713, 186, 282, 458, 690, 620, 372, 312, 360, 680, 19, 259, 515, 21, 69, 261, 517, 529, 193, 577, 385, 641, 26, 138, 266, 178, 274, 530, 386, 642, 52, 276, 100, 548, 324, 580, 56, 280, 104, 168, 296, 552, 200, 328, 584, 648, 304, 560, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_531, vertices_899, vertices_565, vertices_453, vertices_581, vertices_713, vertices_186, vertices_282, vertices_458, vertices_690, vertices_620, vertices_372, vertices_312, vertices_360, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_21, vertices_69, vertices_261, vertices_517, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_138, vertices_266, vertices_178, vertices_274, vertices_530, vertices_386, vertices_642, vertices_52, vertices_276, vertices_100, vertices_548, vertices_324, vertices_580, vertices_56, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_560, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_531), (false, vertices_899), (false, vertices_565), (false, vertices_453), (false, vertices_581), (false, vertices_713), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_178), (true, vertices_100), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_304), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_178) then 19 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 8 620 100 1
cert_row_4 1 0 2 5 6 7 458 138 2
cert_row_2 2 0 3 4 6 178
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 2 0 2 3 4 26 186 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 138 458 2
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 8 178 690 3
cert_coverFacet 4 620
cert_cover_5 4 0 1 2 4 5 100 620 1
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 52 372 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0321

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0322.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0322

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 595, 643, 341, 613, 165, 681, 410, 810, 650, 786, 236, 460, 404, 360, 880, 19, 131, 515, 21, 37, 69, 133, 81, 161, 545, 577, 641, 138, 266, 522, 146, 274, 530, 642, 770, 204, 148, 276, 100, 164, 324, 388, 104, 168, 296, 552, 328, 392, 648, 336, 592, 400, 784, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_595, vertices_643, vertices_341, vertices_613, vertices_165, vertices_681, vertices_410, vertices_810, vertices_650, vertices_786, vertices_236, vertices_460, vertices_404, vertices_360, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_21, vertices_37, vertices_69, vertices_133, vertices_81, vertices_161, vertices_545, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_204, vertices_148, vertices_276, vertices_100, vertices_164, vertices_324, vertices_388, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_336, vertices_592, vertices_400, vertices_784, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_595), (false, vertices_643), (false, vertices_341), (false, vertices_613), (false, vertices_165), (false, vertices_681), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_770), (true, vertices_204), (true, vertices_388), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_400), (true, vertices_784), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 22 19 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_341) then 23 else
  if p.val = (false, vertices_613) then 24 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_204) then 21 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
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
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 2 4 7 8 810 266 2
cert_row_4 3 3 4 5 7 8 880 336 1
cert_rows
cert_pivot_2 1 6 0 3
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_5 0 1 0 2 3 6 138 410 2
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 266 810 2
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 5 204 236 2
cert_coverFacet 5 460
cert_cover_5 5 0 1 2 5 7 204 460 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 336 880 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0322

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0324.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0324

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 155, 531, 451, 569, 201, 841, 310, 566, 402, 620, 228, 420, 964, 248, 432, 19, 131, 259, 515, 25, 73, 137, 521, 529, 193, 321, 769, 54, 262, 518, 146, 274, 530, 386, 100, 164, 292, 548, 196, 580, 388, 772, 56, 152, 104, 552, 200, 584, 176, 304, 560, 400, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_155, vertices_531, vertices_451, vertices_569, vertices_201, vertices_841, vertices_310, vertices_566, vertices_402, vertices_620, vertices_228, vertices_420, vertices_964, vertices_248, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_25, vertices_73, vertices_137, vertices_521, vertices_529, vertices_193, vertices_321, vertices_769, vertices_54, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_152, vertices_104, vertices_552, vertices_200, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_155), (false, vertices_531), (false, vertices_451), (false, vertices_569), (false, vertices_201), (false, vertices_841), (true, vertices_54), (true, vertices_274), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_104), (true, vertices_176), (true, vertices_304), (true, vertices_400), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_155) then 20 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 1 531 0 201 274 100 164 292 548 196 580 388 104 176 304 400 224 416 775 54 155 451 569 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 100 620 1
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 964
cert_cover_5 6 1 1 5 6 7 196 964 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 56 248 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0324

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0325.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0325

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 181, 341, 613, 569, 785, 206, 334, 794, 650, 738, 396, 404, 228, 440, 680, 21, 37, 69, 49, 273, 529, 545, 321, 577, 769, 78, 138, 266, 522, 194, 322, 578, 642, 770, 140, 268, 148, 276, 100, 164, 196, 324, 388, 56, 280, 536, 168, 552, 392, 648, 176, 400, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_181, vertices_341, vertices_613, vertices_569, vertices_785, vertices_206, vertices_334, vertices_794, vertices_650, vertices_738, vertices_396, vertices_404, vertices_228, vertices_440, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_49, vertices_273, vertices_529, vertices_545, vertices_321, vertices_577, vertices_769, vertices_78, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_140, vertices_268, vertices_148, vertices_276, vertices_100, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_392, vertices_648, vertices_176, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_181), (false, vertices_341), (false, vertices_613), (false, vertices_569), (false, vertices_785), (true, vertices_78), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_196), (true, vertices_388), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_400), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_613) then 23 else
  if p.val = (false, vertices_569) then 25 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_78) then 19 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 785 138 266 522 194 642 140 268 196 388 280 168 392 648 400 224 672 835 78 181 341 613 569
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 794
cert_cover_5 2 2 0 2 3 7 266 794 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 56 440 3
cert_coverFacet 9 680
cert_cover_2 9 4 2 6 8 168 680 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0325

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0326.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0326

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 651, 531, 451, 565, 709, 325, 186, 538, 434, 620, 372, 568, 360, 424, 968, 19, 131, 259, 515, 21, 69, 261, 517, 529, 193, 321, 641, 26, 138, 522, 178, 274, 530, 386, 52, 276, 100, 548, 324, 580, 56, 536, 104, 168, 296, 552, 328, 584, 392, 648, 304, 560, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_651, vertices_531, vertices_451, vertices_565, vertices_709, vertices_325, vertices_186, vertices_538, vertices_434, vertices_620, vertices_372, vertices_568, vertices_360, vertices_424, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_261, vertices_517, vertices_529, vertices_193, vertices_321, vertices_641, vertices_26, vertices_138, vertices_522, vertices_178, vertices_274, vertices_530, vertices_386, vertices_52, vertices_276, vertices_100, vertices_548, vertices_324, vertices_580, vertices_56, vertices_536, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_651), (false, vertices_531), (false, vertices_451), (false, vertices_565), (false, vertices_709), (false, vertices_325), (true, vertices_26), (true, vertices_178), (true, vertices_100), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_304), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 22 16 20 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_651) then 21 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_178) then 24 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 22 => Sum.inl 0
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 6 178
cert_row_4 1 1 3 4 5 7 372 52 3
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 0 0 2 3 4 26 186 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 434
cert_cover_5 2 0 0 3 4 7 178 434 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 100 620 1
cert_coverFacet 4 372
cert_cover_5 4 1 1 3 4 5 52 372 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 968
cert_cover_5 8 3 2 5 6 7 328 968 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0326

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0327.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0327

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 595, 803, 195, 569, 369, 449, 782, 198, 582, 668, 428, 724, 248, 808, 480, 67, 131, 259, 515, 49, 81, 529, 289, 545, 193, 321, 385, 70, 134, 262, 518, 194, 578, 770, 140, 268, 524, 660, 196, 580, 388, 56, 152, 536, 168, 296, 552, 776, 112, 208, 592, 224, 352, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_595, vertices_803, vertices_195, vertices_569, vertices_369, vertices_449, vertices_782, vertices_198, vertices_582, vertices_668, vertices_428, vertices_724, vertices_248, vertices_808, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_70, vertices_134, vertices_262, vertices_518, vertices_194, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_660, vertices_196, vertices_580, vertices_388, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_776, vertices_112, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_595), (false, vertices_803), (false, vertices_195), (false, vertices_569), (false, vertices_369), (false, vertices_449), (true, vertices_70), (true, vertices_518), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_660), (true, vertices_196), (true, vertices_580), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_776), (true, vertices_208), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_660) then 21 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 1 3 6 8 660
cert_row_4 2 1 2 4 6 7 428 140 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 140 668 2
cert_coverFacet 4 428
cert_cover_5 4 2 1 2 4 6 140 428 2
cert_coverFacet 5 724
cert_cover_5 5 1 1 3 5 6 660 724 2
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0327

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0328.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0328

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 541, 309, 677, 793, 481, 590, 410, 202, 778, 738, 124, 612, 216, 368, 464, 21, 37, 517, 537, 273, 161, 289, 385, 641, 769, 74, 138, 266, 522, 194, 578, 386, 642, 770, 28, 76, 524, 52, 100, 548, 580, 88, 152, 280, 200, 776, 112, 304, 208, 336, 400, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_541, vertices_309, vertices_677, vertices_793, vertices_481, vertices_590, vertices_410, vertices_202, vertices_778, vertices_738, vertices_124, vertices_612, vertices_216, vertices_368, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_537, vertices_273, vertices_161, vertices_289, vertices_385, vertices_641, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_52, vertices_100, vertices_548, vertices_580, vertices_88, vertices_152, vertices_280, vertices_200, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_541), (false, vertices_309), (false, vertices_677), (false, vertices_793), (false, vertices_481), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_100), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_541) then 23 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_793) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 0 1 2 5 8 590 74 1
cert_row_4 3 1 2 3 4 5 124 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 74 590 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 138 410 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 124
cert_cover_5 5 3 1 2 3 4 28 124 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0328

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0329.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0329

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 805, 709, 465, 353, 542, 662, 58, 810, 242, 706, 156, 780, 376, 408, 133, 261, 517, 97, 289, 545, 193, 321, 577, 385, 534, 26, 42, 522, 50, 146, 98, 546, 194, 578, 642, 28, 140, 268, 524, 148, 644, 772, 56, 152, 280, 296, 392, 776, 112, 208, 336, 400, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_805, vertices_709, vertices_465, vertices_353, vertices_542, vertices_662, vertices_58, vertices_810, vertices_242, vertices_706, vertices_156, vertices_780, vertices_376, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_534, vertices_26, vertices_42, vertices_522, vertices_50, vertices_146, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_296, vertices_392, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_805), (false, vertices_709), (false, vertices_465), (false, vertices_353), (true, vertices_534), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_194), (true, vertices_642), (true, vertices_28), (true, vertices_524), (true, vertices_148), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_534) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_776) then 15 else
  if p.val = (true, vertices_112) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 353 26 42 522 50 146 194 642 28 524 148 56 152 280 296 776 112 611 534 397 805 709 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 8 534
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 534 542 2
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 534 662 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 42 810 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 50 242 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 56 376 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0329

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0330.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0330

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 613, 233, 689, 465, 833, 30, 46, 278, 550, 838, 666, 682, 412, 364, 456, 145, 273, 529, 97, 161, 545, 193, 321, 577, 769, 14, 22, 38, 262, 518, 26, 42, 650, 274, 530, 546, 770, 28, 44, 268, 276, 100, 548, 324, 580, 152, 104, 168, 200, 328, 392, 400, 656, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_613, vertices_233, vertices_689, vertices_465, vertices_833, vertices_30, vertices_46, vertices_278, vertices_550, vertices_838, vertices_666, vertices_682, vertices_412, vertices_364, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_650, vertices_274, vertices_530, vertices_546, vertices_770, vertices_28, vertices_44, vertices_268, vertices_276, vertices_100, vertices_548, vertices_324, vertices_580, vertices_152, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_400, vertices_656, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_613), (false, vertices_233), (false, vertices_689), (false, vertices_465), (false, vertices_833), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_650), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_324), (true, vertices_152), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_262) then 4 else
  if p.val = (true, vertices_518) then 5 else
  if p.val = (true, vertices_26) then 6 else
  if p.val = (true, vertices_42) then 7 else
  if p.val = (true, vertices_650) then 19 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_324) then 13 else
  if p.val = (true, vertices_152) then 14 else
  if p.val = (true, vertices_328) then 15 else
  if p.val = (true, vertices_392) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 7 412 28 3
cert_row_2 1 0 2 6 8 650
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 838
cert_cover_5 4 2 0 1 5 7 262 838 2
cert_coverFacet 5 666
cert_cover_5 5 1 0 2 3 6 26 666 3
cert_coverFacet 6 682
cert_cover_5 6 1 0 2 4 6 42 682 3
cert_coverFacet 7 412
cert_cover_5 7 0 1 2 3 6 28 412 3
cert_coverFacet 8 364
cert_cover_5 8 3 1 2 4 5 44 364 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0330

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0331.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0331

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 787, 781, 341, 613, 241, 654, 58, 282, 170, 778, 738, 460, 708, 440, 464, 531, 69, 261, 517, 49, 81, 273, 97, 545, 769, 26, 42, 138, 266, 522, 50, 274, 162, 546, 642, 770, 140, 268, 524, 196, 324, 580, 644, 56, 280, 168, 392, 776, 176, 208, 336, 400, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_787, vertices_781, vertices_341, vertices_613, vertices_241, vertices_654, vertices_58, vertices_282, vertices_170, vertices_778, vertices_738, vertices_460, vertices_708, vertices_440, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_531, vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_97, vertices_545, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_546, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_280, vertices_168, vertices_392, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_787), (false, vertices_781), (false, vertices_341), (false, vertices_613), (false, vertices_241), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_642), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_400), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_613) then 23 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_448) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
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
cert_row_4 0 2 3 4 6 7 440 56 3
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 140 460 2
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 440
cert_cover_5 8 0 2 3 4 6 56 440 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0331

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0332.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0332

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 397, 781, 565, 229, 433, 654, 346, 202, 778, 626, 706, 612, 708, 488, 368, 269, 37, 133, 517, 49, 273, 529, 161, 385, 769, 74, 138, 266, 522, 82, 274, 530, 194, 578, 642, 770, 140, 524, 100, 548, 196, 580, 644, 200, 328, 392, 776, 112, 304, 560, 336, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_397, vertices_781, vertices_565, vertices_229, vertices_433, vertices_654, vertices_346, vertices_202, vertices_778, vertices_626, vertices_706, vertices_612, vertices_708, vertices_488, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_133, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_385, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_194, vertices_578, vertices_642, vertices_770, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_397), (false, vertices_781), (false, vertices_565), (false, vertices_229), (false, vertices_433), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_580), (true, vertices_644), (true, vertices_200), (true, vertices_328), (true, vertices_112), (true, vertices_336), (true, vertices_352), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_565) then 23 else
  if p.val = (false, vertices_229) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 0 2 3 5 7 346 74 2
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 74 346 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 82 626 2
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 200 488 1
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0332

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0333.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0333

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 653, 185, 617, 369, 657, 782, 214, 326, 646, 658, 866, 428, 468, 808, 432, 41, 137, 521, 49, 81, 145, 529, 97, 577, 641, 70, 134, 262, 518, 82, 146, 530, 322, 578, 642, 770, 140, 268, 524, 212, 324, 388, 644, 168, 296, 552, 776, 176, 304, 336, 400, 656, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_653, vertices_185, vertices_617, vertices_369, vertices_657, vertices_782, vertices_214, vertices_326, vertices_646, vertices_658, vertices_866, vertices_428, vertices_468, vertices_808, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_49, vertices_81, vertices_145, vertices_529, vertices_97, vertices_577, vertices_641, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_212, vertices_324, vertices_388, vertices_644, vertices_168, vertices_296, vertices_552, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_653), (false, vertices_185), (false, vertices_617), (false, vertices_369), (false, vertices_657), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_146), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_212), (true, vertices_324), (true, vertices_388), (true, vertices_296), (true, vertices_776), (true, vertices_400), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_212) then 21 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 6 212
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_4 2 0 1 2 7 8 782 262 2
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 262 782 2
cert_coverFacet 1 214
cert_cover_5 1 0 0 1 3 5 70 214 2
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 322 866 1
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 140 428 2
cert_coverFacet 7 468
cert_cover_5 7 0 1 3 5 7 212 468 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0333

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0334.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0334

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 805, 709, 369, 449, 542, 662, 58, 810, 242, 706, 156, 780, 312, 472, 133, 261, 517, 97, 289, 545, 193, 321, 577, 385, 534, 26, 42, 522, 50, 146, 98, 546, 194, 578, 642, 28, 140, 268, 524, 148, 644, 772, 56, 152, 280, 296, 392, 776, 112, 304, 208, 336, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_805, vertices_709, vertices_369, vertices_449, vertices_542, vertices_662, vertices_58, vertices_810, vertices_242, vertices_706, vertices_156, vertices_780, vertices_312, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_534, vertices_26, vertices_42, vertices_522, vertices_50, vertices_146, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_296, vertices_392, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_805), (false, vertices_709), (false, vertices_369), (false, vertices_449), (true, vertices_534), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_194), (true, vertices_642), (true, vertices_28), (true, vertices_524), (true, vertices_148), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_534) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_776) then 15 else
  if p.val = (true, vertices_208) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 449 26 42 522 50 146 194 642 28 524 148 56 152 280 296 776 208 611 534 397 805 709 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 8 534
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 534 542 2
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 534 662 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 42 810 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 50 242 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 472
cert_cover_5 9 3 2 3 5 6 152 472 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0334

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0335.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0335

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 179, 611, 771, 841, 369, 401, 782, 166, 550, 668, 460, 692, 632, 216, 464, 35, 131, 259, 515, 49, 145, 273, 97, 321, 577, 385, 769, 38, 134, 262, 518, 162, 546, 770, 140, 268, 524, 660, 164, 548, 388, 88, 152, 536, 200, 328, 584, 776, 112, 176, 560, 208, 336, 400, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_179, vertices_611, vertices_771, vertices_841, vertices_369, vertices_401, vertices_782, vertices_166, vertices_550, vertices_668, vertices_460, vertices_692, vertices_632, vertices_216, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_97, vertices_321, vertices_577, vertices_385, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_162, vertices_546, vertices_770, vertices_140, vertices_268, vertices_524, vertices_660, vertices_164, vertices_548, vertices_388, vertices_88, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_179), (false, vertices_611), (false, vertices_771), (false, vertices_841), (false, vertices_369), (false, vertices_401), (true, vertices_38), (true, vertices_518), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_660), (true, vertices_164), (true, vertices_548), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_560), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_179) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_660) then 21 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_4 1 1 2 5 6 7 460 140 2
cert_row_2 2 1 3 6 8 660
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 668
cert_cover_5 3 2 1 2 3 6 140 668 2
cert_coverFacet 4 460
cert_cover_5 4 1 1 2 5 6 140 460 2
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 660 692 2
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 88 632 2
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0335

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0336.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0336

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 653, 185, 809, 369, 657, 590, 406, 662, 326, 866, 236, 452, 616, 240, 464, 41, 137, 521, 49, 145, 273, 529, 289, 641, 769, 150, 70, 262, 518, 274, 530, 322, 578, 770, 76, 140, 524, 196, 324, 388, 644, 104, 168, 552, 584, 112, 176, 208, 336, 400, 656, 224, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_653, vertices_185, vertices_809, vertices_369, vertices_657, vertices_590, vertices_406, vertices_662, vertices_326, vertices_866, vertices_236, vertices_452, vertices_616, vertices_240, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_49, vertices_145, vertices_273, vertices_529, vertices_289, vertices_641, vertices_769, vertices_150, vertices_70, vertices_262, vertices_518, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_196, vertices_324, vertices_388, vertices_644, vertices_104, vertices_168, vertices_552, vertices_584, vertices_112, vertices_176, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_653), (false, vertices_185), (false, vertices_809), (false, vertices_369), (false, vertices_657), (true, vertices_150), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_104), (true, vertices_584), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_150) then 19 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 657 70 262 518 322 578 76 196 324 388 104 584 208 400 224 608 448 787 150 653 185 809 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_4 2 0 1 2 5 8 590 70 2
cert_row_4 3 1 2 4 5 6 236 76 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 70 590 2
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 7 150 406 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 8 150 662 3
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 322 866 1
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 76 236 2
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0336

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0337.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0337

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 781, 357, 677, 313, 169, 710, 602, 154, 434, 338, 482, 852, 228, 184, 792, 37, 261, 517, 41, 137, 265, 521, 161, 289, 641, 26, 138, 522, 82, 146, 274, 418, 194, 322, 578, 642, 100, 164, 196, 324, 580, 644, 772, 56, 152, 280, 536, 168, 776, 176, 304, 336, 592, 784, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_781, vertices_357, vertices_677, vertices_313, vertices_169, vertices_710, vertices_602, vertices_154, vertices_434, vertices_338, vertices_482, vertices_852, vertices_228, vertices_184, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_41, vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_641, vertices_26, vertices_138, vertices_522, vertices_82, vertices_146, vertices_274, vertices_418, vertices_194, vertices_322, vertices_578, vertices_642, vertices_100, vertices_164, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_776, vertices_176, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_781), (false, vertices_357), (false, vertices_677), (false, vertices_313), (false, vertices_169), (true, vertices_26), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_418), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_196), (true, vertices_580), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (false, vertices_313) then 25 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_418) then 19 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 169 26 82 146 274 194 322 578 196 580 152 536 176 336 592 784 224 651 418 781 357 677 313
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 6 7 418
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 1 3 5 7 8 852 324 1
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 6 146 434 2
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 482
cert_cover_5 5 0 0 4 5 6 418 482 2
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 324 852 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0337

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0338.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0338

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 181, 789, 293, 809, 737, 342, 794, 618, 330, 210, 706, 428, 460, 212, 232, 21, 37, 261, 145, 529, 161, 289, 545, 641, 769, 74, 266, 522, 82, 146, 274, 530, 194, 322, 578, 642, 396, 84, 148, 276, 164, 292, 196, 324, 104, 168, 296, 552, 200, 328, 776, 208, 784, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_181, vertices_789, vertices_293, vertices_809, vertices_737, vertices_342, vertices_794, vertices_618, vertices_330, vertices_210, vertices_706, vertices_428, vertices_460, vertices_212, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_74, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_396, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_776, vertices_208, vertices_784, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_181), (false, vertices_789), (false, vertices_293), (false, vertices_809), (false, vertices_737), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_396), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_396) then 22 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_328) then 15 else
  if p.val = (true, vertices_208) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 1 3 5 7 342 82 1
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 0 2 4 5 8 618 74 2
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 82 342 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 266 794 2
cert_coverFacet 2 618
cert_cover_5 2 3 0 2 4 5 74 618 2
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 428
cert_cover_5 6 0 1 2 4 6 396 428 2
cert_coverFacet 7 460
cert_cover_5 7 0 1 2 5 6 396 460 2
cert_coverFacet 8 212
cert_cover_2 8 3 1 5 6 84 212 3
cert_coverFacet 9 232
cert_cover_2 9 4 2 5 6 104 232 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0338

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0339.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0339

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 789, 569, 425, 841, 177, 342, 534, 230, 678, 458, 658, 620, 836, 232, 688, 41, 265, 521, 49, 145, 273, 529, 161, 385, 769, 22, 166, 70, 518, 146, 274, 530, 194, 322, 386, 642, 276, 532, 100, 548, 324, 580, 772, 104, 168, 552, 200, 328, 584, 392, 176, 560, 656, 224, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_789, vertices_569, vertices_425, vertices_841, vertices_177, vertices_342, vertices_534, vertices_230, vertices_678, vertices_458, vertices_658, vertices_620, vertices_836, vertices_232, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_385, vertices_769, vertices_22, vertices_166, vertices_70, vertices_518, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_560, vertices_656, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_789), (false, vertices_569), (false, vertices_425), (false, vertices_841), (false, vertices_177), (true, vertices_22), (true, vertices_166), (true, vertices_70), (true, vertices_518), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_100), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_656), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_841) then 25 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_166) then 19 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_2 2 0 1 4 6 166
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 230
cert_cover_5 2 2 0 1 4 5 166 230 3
cert_coverFacet 3 678
cert_cover_5 3 2 0 1 4 8 166 678 3
cert_coverFacet 4 458
cert_cover_5 4 1 0 2 5 6 194 458 1
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coverFacet 9 688
cert_cover_2 9 4 3 6 8 176 688 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0339

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0340.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0340

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 595, 147, 355, 653, 617, 657, 214, 454, 418, 796, 428, 340, 660, 808, 880, 19, 35, 67, 131, 41, 137, 521, 145, 529, 97, 577, 641, 198, 82, 146, 162, 290, 322, 386, 140, 268, 524, 84, 148, 276, 532, 324, 388, 644, 168, 296, 552, 776, 336, 592, 656, 784, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_595, vertices_147, vertices_355, vertices_653, vertices_617, vertices_657, vertices_214, vertices_454, vertices_418, vertices_796, vertices_428, vertices_340, vertices_660, vertices_808, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_131, vertices_41, vertices_137, vertices_521, vertices_145, vertices_529, vertices_97, vertices_577, vertices_641, vertices_198, vertices_82, vertices_146, vertices_162, vertices_290, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_388, vertices_644, vertices_168, vertices_296, vertices_552, vertices_776, vertices_336, vertices_592, vertices_656, vertices_784, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_595), (false, vertices_147), (false, vertices_355), (false, vertices_653), (false, vertices_617), (false, vertices_657), (true, vertices_198), (true, vertices_386), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_388), (true, vertices_296), (true, vertices_776), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 20 else
  if p.val = (false, vertices_595) then 21 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_355) then 22 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_198) then 18 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 1 147 0 657 386 268 84 148 276 532 324 388 296 776 336 784 416 800 653 198 171 595 355 617
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 1 2 4 6 7 428 140 2
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 3 4 5 7 8 880 336 1
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 198 214 2
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 7 198 454 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 268 796 2
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 140 428 2
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 336 880 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0340

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0341.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0341

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 453, 601, 361, 705, 310, 150, 774, 810, 562, 722, 436, 248, 568, 480, 133, 261, 517, 73, 265, 521, 193, 321, 577, 641, 22, 134, 262, 518, 50, 146, 530, 290, 546, 642, 770, 308, 148, 388, 772, 56, 88, 536, 104, 296, 552, 776, 176, 560, 208, 592, 224, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_453, vertices_601, vertices_361, vertices_705, vertices_310, vertices_150, vertices_774, vertices_810, vertices_562, vertices_722, vertices_436, vertices_248, vertices_568, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_22, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_308, vertices_148, vertices_388, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_296, vertices_552, vertices_776, vertices_176, vertices_560, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_453), (false, vertices_601), (false, vertices_361), (false, vertices_705), (true, vertices_22), (true, vertices_262), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_308), (true, vertices_148), (true, vertices_56), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 23 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_453) then 24 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_308) then 25 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 25 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 7 308
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 290 810 1
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 146 722 2
cert_coverFacet 6 436
cert_cover_5 6 0 1 3 4 6 308 436 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 56 248 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0341

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0342.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0342

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 157, 541, 805, 453, 657, 737, 302, 570, 282, 722, 338, 610, 556, 396, 472, 29, 133, 261, 517, 145, 529, 97, 289, 545, 193, 321, 641, 26, 42, 266, 82, 274, 530, 98, 290, 546, 322, 578, 44, 140, 268, 524, 292, 548, 388, 152, 280, 536, 552, 392, 208, 336, 656, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_157, vertices_541, vertices_805, vertices_453, vertices_657, vertices_737, vertices_302, vertices_570, vertices_282, vertices_722, vertices_338, vertices_610, vertices_556, vertices_396, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_133, vertices_261, vertices_517, vertices_145, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_26, vertices_42, vertices_266, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_388, vertices_152, vertices_280, vertices_536, vertices_552, vertices_392, vertices_208, vertices_336, vertices_656, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_157), (false, vertices_541), (false, vertices_805), (false, vertices_453), (false, vertices_657), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_578), (true, vertices_44), (true, vertices_268), (true, vertices_280), (true, vertices_552), (true, vertices_392), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 18 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 42 1
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 42 302 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 26 570 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 82 722 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 152 472 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0342

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0343.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0343

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 157, 541, 837, 721, 481, 142, 526, 806, 570, 234, 418, 376, 216, 816, 848, 29, 133, 261, 517, 145, 529, 193, 321, 577, 385, 14, 134, 262, 518, 42, 138, 522, 162, 290, 546, 386, 140, 524, 772, 56, 88, 152, 536, 104, 200, 304, 560, 208, 336, 592, 784, 224, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_157, vertices_541, vertices_837, vertices_721, vertices_481, vertices_142, vertices_526, vertices_806, vertices_570, vertices_234, vertices_418, vertices_376, vertices_216, vertices_816, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_133, vertices_261, vertices_517, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_14, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_140, vertices_524, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_200, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_157), (false, vertices_541), (false, vertices_837), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_200), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_157) then 20 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 5 6 234 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 262 806 2
cert_coverFacet 3 570
cert_cover_5 3 1 0 2 3 4 42 570 2
cert_coverFacet 4 234
cert_cover_5 4 2 0 2 4 5 42 234 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coverFacet 9 848
cert_cover_2 9 5 3 7 8 336 848 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0343

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0344.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0344

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 397, 569, 217, 777, 369, 449, 782, 230, 422, 582, 626, 668, 708, 720, 480, 25, 137, 265, 521, 49, 81, 289, 545, 193, 321, 385, 769, 166, 70, 262, 518, 98, 290, 546, 578, 770, 140, 268, 524, 196, 580, 388, 644, 152, 536, 776, 112, 560, 208, 592, 656, 224, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_397, vertices_569, vertices_217, vertices_777, vertices_369, vertices_449, vertices_782, vertices_230, vertices_422, vertices_582, vertices_626, vertices_668, vertices_708, vertices_720, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_81, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_166, vertices_70, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_644, vertices_152, vertices_536, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_397), (false, vertices_569), (false, vertices_217), (false, vertices_777), (false, vertices_369), (false, vertices_449), (true, vertices_166), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_578), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_592), (true, vertices_656), (true, vertices_224), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_166) then 18 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_4 1 0 3 4 5 8 626 98 1
cert_row_2 2 0 1 4 6 166
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 230
cert_cover_5 1 2 0 1 4 5 166 230 3
cert_coverFacet 2 422
cert_cover_5 2 2 0 1 4 7 166 422 3
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 98 626 1
cert_coverFacet 5 668
cert_cover_5 5 3 1 2 3 6 140 668 2
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0344

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4203 : Certifies 4203 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0314.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4204 : Certifies 4204 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0315.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4205 : Certifies 4205 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0316.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4206 : Certifies 4206 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0317.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4207 : Certifies 4207 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0318.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4208 : Certifies 4208 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0319.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4209 : Certifies 4209 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0320.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4210 : Certifies 4210 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0321.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4211 : Certifies 4211 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0322.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4212 : Certifies 4212 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0324.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4213 : Certifies 4213 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0325.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4214 : Certifies 4214 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0326.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4215 : Certifies 4215 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0327.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4216 : Certifies 4216 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0328.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4217 : Certifies 4217 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0329.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4218 : Certifies 4218 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0330.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4219 : Certifies 4219 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0331.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4220 : Certifies 4220 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0332.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4221 : Certifies 4221 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0333.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4222 : Certifies 4222 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0334.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4223 : Certifies 4223 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0335.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4224 : Certifies 4224 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0336.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4225 : Certifies 4225 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0337.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4226 : Certifies 4226 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0338.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4227 : Certifies 4227 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0339.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4228 : Certifies 4228 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0340.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4229 : Certifies 4229 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0341.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4230 : Certifies 4230 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0342.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4231 : Certifies 4231 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0343.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4232 : Certifies 4232 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0344.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B139 (j : Fin 30) :
    Certifies (4203 + j.val) := by
  fin_cases j
  · exact projection_4203
  · exact projection_4204
  · exact projection_4205
  · exact projection_4206
  · exact projection_4207
  · exact projection_4208
  · exact projection_4209
  · exact projection_4210
  · exact projection_4211
  · exact projection_4212
  · exact projection_4213
  · exact projection_4214
  · exact projection_4215
  · exact projection_4216
  · exact projection_4217
  · exact projection_4218
  · exact projection_4219
  · exact projection_4220
  · exact projection_4221
  · exact projection_4222
  · exact projection_4223
  · exact projection_4224
  · exact projection_4225
  · exact projection_4226
  · exact projection_4227
  · exact projection_4228
  · exact projection_4229
  · exact projection_4230
  · exact projection_4231
  · exact projection_4232

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
