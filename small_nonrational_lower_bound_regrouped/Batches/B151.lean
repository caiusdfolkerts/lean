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
/- Source: ProjectionCertificates/R_m16e10q1_0680.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0680

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 551, 587, 269, 421, 905, 689, 286, 534, 346, 722, 372, 564, 488, 712, 240, 7, 11, 515, 13, 37, 261, 265, 521, 161, 545, 385, 641, 14, 22, 518, 282, 74, 82, 530, 578, 268, 52, 276, 532, 292, 548, 200, 328, 584, 392, 648, 112, 176, 560, 208, 336, 656, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_551, vertices_587, vertices_269, vertices_421, vertices_905, vertices_689, vertices_286, vertices_534, vertices_346, vertices_722, vertices_372, vertices_564, vertices_488, vertices_712, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_13, vertices_37, vertices_261, vertices_265, vertices_521, vertices_161, vertices_545, vertices_385, vertices_641, vertices_14, vertices_22, vertices_518, vertices_282, vertices_74, vertices_82, vertices_530, vertices_578, vertices_268, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_551), (false, vertices_587), (false, vertices_269), (false, vertices_421), (false, vertices_905), (false, vertices_689), (true, vertices_22), (true, vertices_282), (true, vertices_82), (true, vertices_530), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_200), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_551) then 17 else
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_282) then 19 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 82 3
cert_row_2 1 0 2 3 7 282
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 5 282 346 3
cert_coverFacet 3 722
cert_cover_5 3 0 0 3 5 6 82 722 3
cert_coverFacet 4 372
cert_cover_5 4 2 1 3 4 5 52 372 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 200 488 1
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0680

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0681.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0681

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 173, 805, 105, 713, 369, 833, 30, 142, 534, 410, 818, 962, 124, 564, 472, 37, 133, 517, 41, 73, 137, 97, 289, 321, 577, 641, 769, 14, 22, 134, 518, 26, 138, 274, 530, 386, 642, 770, 28, 44, 140, 52, 532, 548, 88, 408, 104, 200, 112, 304, 560, 336, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_173, vertices_805, vertices_105, vertices_713, vertices_369, vertices_833, vertices_30, vertices_142, vertices_534, vertices_410, vertices_818, vertices_962, vertices_124, vertices_564, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_137, vertices_97, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_134, vertices_518, vertices_26, vertices_138, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_52, vertices_532, vertices_548, vertices_88, vertices_408, vertices_104, vertices_200, vertices_112, vertices_304, vertices_560, vertices_336, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_173), (false, vertices_805), (false, vertices_105), (false, vertices_713), (false, vertices_369), (false, vertices_833), (true, vertices_14), (true, vertices_22), (true, vertices_26), (true, vertices_138), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_52), (true, vertices_532), (true, vertices_88), (true, vertices_408), (true, vertices_560), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_28) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
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
cert_row_4 0 1 2 3 4 5 124 28 3
cert_row_2 1 2 3 6 7 408
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 0 5 6 7 8 962 386 1
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 410
cert_cover_5 3 1 0 2 3 6 26 410 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 274 818 2
cert_coverFacet 5 962
cert_cover_5 5 3 0 5 6 7 386 962 1
cert_coverFacet 6 124
cert_cover_5 6 0 1 2 3 4 28 124 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0681

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0682.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0682

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 309, 789, 569, 361, 713, 182, 598, 390, 774, 458, 210, 428, 680, 688, 720, 277, 41, 73, 521, 49, 529, 289, 321, 577, 769, 22, 134, 262, 518, 82, 146, 194, 322, 578, 386, 770, 52, 532, 164, 292, 388, 772, 168, 296, 552, 200, 328, 392, 648, 176, 560, 208, 592, 656, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_309, vertices_789, vertices_569, vertices_361, vertices_713, vertices_182, vertices_598, vertices_390, vertices_774, vertices_458, vertices_210, vertices_428, vertices_680, vertices_688, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_41, vertices_73, vertices_521, vertices_49, vertices_529, vertices_289, vertices_321, vertices_577, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_532, vertices_164, vertices_292, vertices_388, vertices_772, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_648, vertices_176, vertices_560, vertices_208, vertices_592, vertices_656, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_309), (false, vertices_789), (false, vertices_569), (false, vertices_361), (false, vertices_713), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_164), (true, vertices_388), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_4 1 0 1 3 4 6 182 22 3
cert_row_4 2 0 2 5 6 7 458 194 1
cert_row_4 3 1 2 4 6 7 428 164 1
cert_rows
cert_pivot_2 8 3 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 22 182 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 5 22 598 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 194 458 1
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 164 428 1
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0682

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0683.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0683

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 331, 675, 195, 565, 421, 449, 218, 650, 778, 604, 844, 116, 356, 696, 496, 67, 131, 259, 515, 37, 261, 517, 161, 545, 193, 321, 385, 74, 138, 266, 522, 194, 642, 770, 588, 52, 84, 532, 100, 292, 324, 772, 88, 152, 536, 328, 648, 776, 112, 176, 560, 208, 352, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_331, vertices_675, vertices_195, vertices_565, vertices_421, vertices_449, vertices_218, vertices_650, vertices_778, vertices_604, vertices_844, vertices_116, vertices_356, vertices_696, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_642, vertices_770, vertices_588, vertices_52, vertices_84, vertices_532, vertices_100, vertices_292, vertices_324, vertices_772, vertices_88, vertices_152, vertices_536, vertices_328, vertices_648, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_352, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_331), (false, vertices_675), (false, vertices_195), (false, vertices_565), (false, vertices_421), (false, vertices_449), (true, vertices_138), (true, vertices_522), (true, vertices_588), (true, vertices_84), (true, vertices_100), (true, vertices_324), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_776), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_588) then 23 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 195 449 138 522 84 100 324 88 152 536 648 776 112 176 208 352 775 331 675 565 421 588
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_4 1 0 2 3 5 6 218 74 2
cert_row_4 2 2 3 4 6 8 696 152 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 1 0 2 3 5 74 218 2
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 588 604 2
cert_coverFacet 4 844
cert_cover_5 4 0 1 2 5 7 588 844 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 696
cert_cover_5 7 2 2 3 4 6 152 696 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0683

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0684.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0684

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 539, 803, 661, 433, 737, 334, 714, 834, 284, 540, 236, 652, 372, 180, 864, 27, 259, 515, 145, 273, 529, 161, 289, 545, 641, 74, 266, 522, 322, 578, 770, 28, 76, 140, 268, 524, 52, 148, 276, 532, 100, 164, 324, 644, 280, 536, 200, 648, 176, 304, 224, 352, 608, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_539, vertices_803, vertices_661, vertices_433, vertices_737, vertices_334, vertices_714, vertices_834, vertices_284, vertices_540, vertices_236, vertices_652, vertices_372, vertices_180, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_259, vertices_515, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_74, vertices_266, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_76, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_324, vertices_644, vertices_280, vertices_536, vertices_200, vertices_648, vertices_176, vertices_304, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_539), (false, vertices_803), (false, vertices_661), (false, vertices_433), (false, vertices_737), (true, vertices_74), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_324), (true, vertices_200), (true, vertices_648), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 18 else
  if p.val = (false, vertices_539) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 0 1 2 5 7 334 74 1
cert_row_4 2 1 2 4 5 6 236 76 2
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 74 334 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 236
cert_cover_5 5 2 1 2 4 5 76 236 2
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 5 52 372 3
cert_coverFacet 8 180
cert_cover_2 8 3 1 4 6 52 180 3
cert_coverFacet 9 864
cert_cover_2 9 5 4 7 8 352 864 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0684

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0685.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0685

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 301, 613, 901, 665, 281, 553, 118, 310, 582, 774, 218, 962, 120, 312, 744, 37, 261, 517, 25, 41, 265, 521, 145, 273, 545, 385, 641, 54, 70, 262, 518, 82, 146, 274, 194, 578, 386, 770, 100, 292, 580, 772, 56, 88, 152, 280, 104, 296, 552, 200, 648, 112, 304, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_301, vertices_613, vertices_901, vertices_665, vertices_281, vertices_553, vertices_118, vertices_310, vertices_582, vertices_774, vertices_218, vertices_962, vertices_120, vertices_312, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_545, vertices_385, vertices_641, vertices_54, vertices_70, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_194, vertices_578, vertices_386, vertices_770, vertices_100, vertices_292, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_301), (false, vertices_613), (false, vertices_901), (false, vertices_665), (false, vertices_281), (false, vertices_553), (true, vertices_54), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_194), (true, vertices_578), (true, vertices_770), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_304), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_901) then 22 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 281 1 553 70 262 518 82 194 578 770 56 88 104 200 112 304 704 403 54 301 613 901 665
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 3 5 6 218 82 1
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 5 54 118 3
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 7 54 310 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 218
cert_cover_5 4 1 0 2 3 5 82 218 1
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 194 962 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0685

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0686.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0686

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 677, 345, 433, 209, 865, 174, 270, 838, 646, 218, 330, 572, 796, 184, 816, 81, 145, 273, 161, 289, 545, 193, 321, 577, 641, 14, 134, 262, 518, 74, 138, 266, 194, 322, 578, 642, 540, 44, 268, 164, 548, 644, 772, 56, 88, 152, 280, 168, 328, 176, 304, 560, 208, 784, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_677, vertices_345, vertices_433, vertices_209, vertices_865, vertices_174, vertices_270, vertices_838, vertices_646, vertices_218, vertices_330, vertices_572, vertices_796, vertices_184, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_134, vertices_262, vertices_518, vertices_74, vertices_138, vertices_266, vertices_194, vertices_322, vertices_578, vertices_642, vertices_540, vertices_44, vertices_268, vertices_164, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_328, vertices_176, vertices_304, vertices_560, vertices_208, vertices_784, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_677), (false, vertices_345), (false, vertices_433), (false, vertices_209), (false, vertices_865), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_322), (true, vertices_540), (true, vertices_44), (true, vertices_268), (true, vertices_772), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_266) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_540) then 21 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_560) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 6 174 14 3
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_2 2 1 2 3 8 540
cert_row_4 3 0 2 3 5 6 218 74 2
cert_rows
cert_pivot_2 4 7 1 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 14 174 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 262 838 2
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 218
cert_cover_5 4 3 0 2 3 5 74 218 2
cert_coverFacet 5 330
cert_cover_2 5 2 0 5 7 74 330 3
cert_coverFacet 6 572
cert_cover_5 6 2 1 2 3 4 540 572 3
cert_coverFacet 7 796
cert_cover_5 7 2 1 2 3 7 540 796 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coverFacet 9 816
cert_cover_2 9 4 3 7 8 304 816 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0686

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0687.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0687

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 309, 597, 773, 425, 689, 838, 602, 362, 394, 650, 220, 236, 180, 356, 664, 21, 261, 517, 49, 529, 161, 289, 385, 641, 769, 74, 138, 266, 522, 322, 578, 386, 642, 770, 204, 52, 84, 148, 100, 164, 292, 324, 580, 772, 88, 152, 536, 104, 168, 296, 392, 648, 176, 592, 656, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_309, vertices_597, vertices_773, vertices_425, vertices_689, vertices_838, vertices_602, vertices_362, vertices_394, vertices_650, vertices_220, vertices_236, vertices_180, vertices_356, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_49, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_204, vertices_52, vertices_84, vertices_148, vertices_100, vertices_164, vertices_292, vertices_324, vertices_580, vertices_772, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_392, vertices_648, vertices_176, vertices_592, vertices_656, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_309), (false, vertices_597), (false, vertices_773), (false, vertices_425), (false, vertices_689), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_578), (true, vertices_204), (true, vertices_148), (true, vertices_100), (true, vertices_164), (true, vertices_324), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_648), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_204) then 22 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_104) then 14 else
  if p.val = (true, vertices_648) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 3 5 8 602 74 2
cert_row_4 3 0 2 4 5 7 362 74 2
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 74 602 2
cert_coverFacet 2 362
cert_cover_5 2 3 0 2 4 5 74 362 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 220
cert_cover_5 5 0 1 2 3 5 204 220 2
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 204 236 2
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0687

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0688.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0688

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 589, 569, 281, 457, 865, 206, 166, 806, 838, 178, 466, 652, 692, 408, 664, 25, 73, 265, 521, 49, 273, 289, 545, 321, 577, 38, 70, 134, 774, 50, 146, 274, 162, 290, 194, 322, 76, 140, 524, 164, 548, 580, 644, 152, 280, 536, 200, 392, 648, 176, 560, 400, 656, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_589, vertices_569, vertices_281, vertices_457, vertices_865, vertices_206, vertices_166, vertices_806, vertices_838, vertices_178, vertices_466, vertices_652, vertices_692, vertices_408, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_577, vertices_38, vertices_70, vertices_134, vertices_774, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_76, vertices_140, vertices_524, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_200, vertices_392, vertices_648, vertices_176, vertices_560, vertices_400, vertices_656, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_589), (false, vertices_569), (false, vertices_281), (false, vertices_457), (false, vertices_865), (true, vertices_38), (true, vertices_70), (true, vertices_134), (true, vertices_774), (true, vertices_146), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_140), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_152), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_774) then 19 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 70 2
cert_row_4 1 0 3 5 6 7 466 146 2
cert_row_2 2 0 1 7 8 774
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 70 206 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 38 806 3
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 70 838 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 466
cert_cover_5 5 1 0 3 5 6 146 466 2
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 164 692 1
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0688

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0689.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0689

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 333, 661, 229, 773, 369, 785, 782, 58, 282, 618, 914, 738, 716, 312, 360, 69, 133, 261, 517, 49, 145, 273, 529, 97, 161, 321, 769, 26, 42, 266, 522, 50, 146, 274, 610, 162, 642, 770, 76, 268, 524, 196, 644, 772, 56, 280, 104, 296, 328, 584, 304, 656, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_333, vertices_661, vertices_229, vertices_773, vertices_369, vertices_785, vertices_782, vertices_58, vertices_282, vertices_618, vertices_914, vertices_738, vertices_716, vertices_312, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_321, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_610, vertices_162, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_196, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_296, vertices_328, vertices_584, vertices_304, vertices_656, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_333), (false, vertices_661), (false, vertices_229), (false, vertices_773), (false, vertices_369), (false, vertices_785), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_610), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_610) then 18 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 773 1 785 26 42 266 522 274 642 770 524 56 280 104 296 584 704 179 610 333 661 229 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 8 610
cert_row_4 1 0 3 6 7 8 914 146 3
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 5 42 618 3
cert_coverFacet 4 914
cert_cover_5 4 1 0 3 6 7 146 914 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 610 738 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0689

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0691.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0691

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 395, 835, 601, 361, 649, 182, 806, 418, 124, 724, 868, 312, 408, 664, 432, 131, 259, 515, 73, 137, 265, 521, 321, 577, 641, 38, 134, 518, 162, 290, 386, 770, 52, 84, 148, 100, 804, 580, 644, 56, 88, 152, 280, 536, 104, 296, 392, 648, 176, 304, 592, 400, 656, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_395, vertices_835, vertices_601, vertices_361, vertices_649, vertices_182, vertices_806, vertices_418, vertices_124, vertices_724, vertices_868, vertices_312, vertices_408, vertices_664, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_38, vertices_134, vertices_518, vertices_162, vertices_290, vertices_386, vertices_770, vertices_52, vertices_84, vertices_148, vertices_100, vertices_804, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_296, vertices_392, vertices_648, vertices_176, vertices_304, vertices_592, vertices_400, vertices_656, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_395), (false, vertices_835), (false, vertices_601), (false, vertices_361), (false, vertices_649), (true, vertices_38), (true, vertices_162), (true, vertices_290), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_804), (true, vertices_580), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_176), (true, vertices_304), (true, vertices_400), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_804) then 22 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 1 3 4 6 182 38 2
cert_row_4 2 1 2 3 4 5 124 52 1
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 38 182 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 38 806 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 52 124 1
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 84 724 3
cert_coverFacet 5 868
cert_cover_5 5 0 1 4 5 7 100 868 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0691

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0692.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0692

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 781, 613, 453, 241, 897, 286, 154, 170, 810, 466, 898, 604, 340, 632, 184, 69, 261, 517, 97, 161, 545, 193, 385, 641, 769, 26, 42, 138, 266, 146, 274, 162, 546, 386, 642, 770, 28, 268, 524, 84, 276, 324, 580, 56, 600, 152, 168, 552, 776, 112, 176, 208, 336, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_781, vertices_613, vertices_453, vertices_241, vertices_897, vertices_286, vertices_154, vertices_170, vertices_810, vertices_466, vertices_898, vertices_604, vertices_340, vertices_632, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_274, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_324, vertices_580, vertices_56, vertices_600, vertices_152, vertices_168, vertices_552, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_781), (false, vertices_613), (false, vertices_453), (false, vertices_241), (false, vertices_897), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_84), (true, vertices_276), (true, vertices_56), (true, vertices_600), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_600) then 24 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_552) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_2 2 2 3 5 8 600
cert_row_4 3 0 3 5 6 7 466 146 2
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 42 810 3
cert_coverFacet 4 466
cert_cover_5 4 3 0 3 5 6 146 466 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 604
cert_cover_5 6 2 1 2 3 5 28 604 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 632
cert_cover_5 8 2 2 3 4 5 56 632 3
cert_coverFacet 9 184
cert_cover_2 9 3 2 4 6 56 184 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0692

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0693.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0693

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 205, 837, 601, 425, 777, 790, 678, 314, 626, 418, 740, 184, 216, 792, 240, 69, 133, 261, 73, 137, 265, 521, 577, 385, 769, 134, 262, 518, 50, 274, 530, 162, 290, 546, 386, 676, 196, 580, 772, 56, 88, 152, 280, 536, 168, 296, 200, 776, 112, 176, 208, 592, 784, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_205, vertices_837, vertices_601, vertices_425, vertices_777, vertices_790, vertices_678, vertices_314, vertices_626, vertices_418, vertices_740, vertices_184, vertices_216, vertices_792, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_265, vertices_521, vertices_577, vertices_385, vertices_769, vertices_134, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_676, vertices_196, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_200, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_205), (false, vertices_837), (false, vertices_601), (false, vertices_425), (false, vertices_777), (true, vertices_518), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_676), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_784), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_676) then 22 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 6 8 676
cert_row_4 1 0 1 3 7 8 790 262 2
cert_row_4 2 0 2 3 4 7 314 50 1
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 262 790 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 134 678 2
cert_coverFacet 2 314
cert_cover_5 2 2 0 2 3 4 50 314 1
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 50 626 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 740
cert_cover_5 5 0 1 4 5 6 676 740 2
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0693

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0694.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0694

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 661, 185, 905, 369, 785, 270, 526, 342, 710, 618, 354, 780, 244, 788, 744, 41, 137, 265, 49, 145, 273, 529, 289, 641, 769, 14, 70, 262, 518, 42, 266, 522, 98, 290, 322, 578, 268, 524, 84, 148, 276, 532, 196, 644, 772, 616, 168, 648, 776, 112, 176, 336, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_661, vertices_185, vertices_905, vertices_369, vertices_785, vertices_270, vertices_526, vertices_342, vertices_710, vertices_618, vertices_354, vertices_780, vertices_244, vertices_788, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_49, vertices_145, vertices_273, vertices_529, vertices_289, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_322, vertices_578, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_616, vertices_168, vertices_648, vertices_776, vertices_112, vertices_176, vertices_336, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_661), (false, vertices_185), (false, vertices_905), (false, vertices_369), (false, vertices_785), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_772), (true, vertices_616), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 21 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_185) then 22 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_196) then 13 else
  if p.val = (true, vertices_772) then 14 else
  if p.val = (true, vertices_616) then 24 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_616), by decide +kernel⟩
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
cert_row_2 0 2 4 5 8 616
cert_row_4 1 0 1 3 5 7 342 70 2
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 342
cert_cover_5 2 1 0 1 3 5 70 342 2
cert_coverFacet 3 710
cert_cover_5 3 2 0 1 5 6 70 710 3
cert_coverFacet 4 618
cert_cover_5 4 0 0 2 4 5 42 618 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 84 244 2
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coverFacet 9 744
cert_cover_5 9 0 2 4 5 6 616 744 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0694

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0695.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0695

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 531, 355, 707, 229, 433, 657, 542, 778, 834, 412, 428, 556, 724, 612, 872, 19, 67, 259, 515, 145, 273, 529, 97, 161, 289, 193, 641, 26, 266, 522, 530, 322, 578, 770, 28, 44, 396, 524, 148, 532, 100, 164, 548, 196, 580, 280, 296, 552, 776, 400, 656, 352, 608, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_531, vertices_355, vertices_707, vertices_229, vertices_433, vertices_657, vertices_542, vertices_778, vertices_834, vertices_412, vertices_428, vertices_556, vertices_724, vertices_612, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_193, vertices_641, vertices_26, vertices_266, vertices_522, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_396, vertices_524, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_280, vertices_296, vertices_552, vertices_776, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_531), (false, vertices_355), (false, vertices_707), (false, vertices_229), (false, vertices_433), (false, vertices_657), (true, vertices_522), (true, vertices_770), (true, vertices_28), (true, vertices_44), (true, vertices_396), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 17 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_396) then 22 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 1 3 5 6 8 724 148 2
cert_row_2 2 1 2 6 7 396
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 412
cert_cover_5 3 2 1 2 3 6 28 412 3
cert_coverFacet 4 428
cert_cover_5 4 2 1 2 4 6 44 428 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 724
cert_cover_5 6 1 1 3 5 6 148 724 2
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 296 872 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0695

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0696.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0696

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 677, 185, 905, 305, 865, 206, 270, 614, 774, 218, 850, 652, 780, 244, 368, 25, 137, 265, 49, 273, 161, 289, 545, 641, 769, 14, 70, 262, 518, 26, 202, 266, 82, 274, 578, 770, 140, 268, 524, 100, 164, 548, 196, 644, 772, 152, 648, 776, 112, 176, 304, 208, 336, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_677, vertices_185, vertices_905, vertices_305, vertices_865, vertices_206, vertices_270, vertices_614, vertices_774, vertices_218, vertices_850, vertices_652, vertices_780, vertices_244, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_49, vertices_273, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_26, vertices_202, vertices_266, vertices_82, vertices_274, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_772, vertices_152, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_677), (false, vertices_185), (false, vertices_905), (false, vertices_305), (false, vertices_865), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_202), (true, vertices_82), (true, vertices_578), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_196), (true, vertices_772), (true, vertices_112), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 18 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_196) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 1 4 5 8 614 70 2
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 5 70 614 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 218
cert_cover_5 4 0 0 2 3 5 26 218 3
cert_coverFacet 5 850
cert_cover_5 5 1 0 3 5 7 82 850 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 244
cert_cover_5 8 3 1 3 4 5 100 244 1
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0696

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0697.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0697

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 357, 409, 809, 465, 737, 30, 526, 342, 102, 678, 218, 226, 540, 820, 792, 137, 265, 521, 401, 97, 289, 545, 193, 321, 641, 14, 22, 38, 70, 518, 26, 138, 522, 82, 98, 162, 194, 642, 28, 524, 276, 532, 100, 292, 548, 324, 152, 280, 536, 776, 208, 336, 784, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_357, vertices_409, vertices_809, vertices_465, vertices_737, vertices_30, vertices_526, vertices_342, vertices_102, vertices_678, vertices_218, vertices_226, vertices_540, vertices_820, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_401, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_14, vertices_22, vertices_38, vertices_70, vertices_518, vertices_26, vertices_138, vertices_522, vertices_82, vertices_98, vertices_162, vertices_194, vertices_642, vertices_28, vertices_524, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_152, vertices_280, vertices_536, vertices_776, vertices_208, vertices_336, vertices_784, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_357), (false, vertices_409), (false, vertices_809), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_28), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_536), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 21 23 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_162) then 8 else
  if p.val = (true, vertices_194) then 9 else
  if p.val = (true, vertices_28) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_532) then 13 else
  if p.val = (true, vertices_548) then 14 else
  if p.val = (true, vertices_536) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 6 218 26 3
cert_row_4 1 0 1 3 5 7 342 22 3
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 342
cert_cover_5 2 1 0 1 3 5 22 342 3
cert_coverFacet 3 102
cert_cover_2 3 1 0 4 5 38 102 3
cert_coverFacet 4 678
cert_cover_5 4 2 0 1 4 6 38 678 3
cert_coverFacet 5 218
cert_cover_5 5 0 0 2 3 5 26 218 3
cert_coverFacet 6 226
cert_cover_2 6 4 0 5 6 98 226 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 820
cert_cover_5 8 3 1 3 4 7 276 820 2
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0697

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0698.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0698

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 333, 653, 597, 361, 737, 790, 314, 394, 178, 722, 898, 780, 372, 904, 240, 13, 69, 517, 41, 329, 137, 97, 161, 577, 641, 42, 138, 266, 50, 146, 274, 530, 162, 386, 642, 770, 268, 524, 84, 276, 532, 324, 772, 296, 392, 648, 776, 112, 176, 304, 208, 592, 224, 352, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_333, vertices_653, vertices_597, vertices_361, vertices_737, vertices_790, vertices_314, vertices_394, vertices_178, vertices_722, vertices_898, vertices_780, vertices_372, vertices_904, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_41, vertices_329, vertices_137, vertices_97, vertices_161, vertices_577, vertices_641, vertices_42, vertices_138, vertices_266, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_386, vertices_642, vertices_770, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_296, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_224, vertices_352, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_333), (false, vertices_653), (false, vertices_597), (false, vertices_361), (false, vertices_737), (true, vertices_266), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_276), (true, vertices_772), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 18 else
  if p.val = (false, vertices_333) then 23 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_896) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 146 722 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 5 84 372 2
cert_coverFacet 8 904
cert_cover_2 8 6 2 7 8 392 904 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0698

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0699.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0699

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 659, 803, 29, 269, 789, 217, 614, 482, 706, 60, 812, 116, 724, 120, 488, 131, 259, 515, 13, 21, 261, 25, 137, 265, 145, 529, 769, 98, 290, 546, 194, 578, 386, 642, 28, 44, 268, 52, 84, 532, 100, 548, 580, 772, 56, 88, 104, 296, 200, 392, 112, 208, 656, 480, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_659, vertices_803, vertices_29, vertices_269, vertices_789, vertices_217, vertices_614, vertices_482, vertices_706, vertices_60, vertices_812, vertices_116, vertices_724, vertices_120, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_13, vertices_21, vertices_261, vertices_25, vertices_137, vertices_265, vertices_145, vertices_529, vertices_769, vertices_98, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_28, vertices_44, vertices_268, vertices_52, vertices_84, vertices_532, vertices_100, vertices_548, vertices_580, vertices_772, vertices_56, vertices_88, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_208, vertices_656, vertices_480, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_659), (false, vertices_803), (false, vertices_29), (false, vertices_269), (false, vertices_789), (false, vertices_217), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_44), (true, vertices_52), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_112), (true, vertices_480), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_480) then 26 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 98 1
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_2 2 4 5 6 7 480
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 0 2 4 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 98 614 1
cert_coverFacet 1 482
cert_cover_5 1 2 0 4 5 6 98 482 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 7 44 812 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 84 724 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 488
cert_cover_5 8 2 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0699

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0700.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0700

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 341, 805, 709, 345, 617, 662, 170, 394, 818, 402, 738, 220, 788, 408, 232, 69, 261, 517, 41, 73, 265, 337, 289, 545, 577, 42, 138, 266, 146, 274, 530, 162, 290, 546, 386, 642, 84, 148, 276, 532, 196, 644, 772, 88, 152, 280, 104, 168, 200, 392, 400, 784, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_341, vertices_805, vertices_709, vertices_345, vertices_617, vertices_662, vertices_170, vertices_394, vertices_818, vertices_402, vertices_738, vertices_220, vertices_788, vertices_408, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_337, vertices_289, vertices_545, vertices_577, vertices_42, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_392, vertices_400, vertices_784, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_341), (false, vertices_805), (false, vertices_709), (false, vertices_345), (false, vertices_617), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_532), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_400), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_341) then 25 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_345) then 26 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 2 3 5 6 220 84 1
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 818
cert_cover_5 3 0 0 3 4 7 274 818 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 84 220 1
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 232
cert_cover_2 9 4 2 5 6 104 232 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0700

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0701.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0701

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 779, 451, 117, 805, 481, 666, 426, 706, 60, 284, 300, 724, 788, 248, 792, 67, 259, 515, 37, 69, 517, 97, 289, 449, 769, 138, 266, 522, 194, 578, 386, 642, 28, 44, 268, 52, 84, 276, 532, 292, 580, 772, 56, 152, 280, 536, 168, 296, 776, 112, 208, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_779, vertices_451, vertices_117, vertices_805, vertices_481, vertices_666, vertices_426, vertices_706, vertices_60, vertices_284, vertices_300, vertices_724, vertices_788, vertices_248, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_97, vertices_289, vertices_449, vertices_769, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_28, vertices_44, vertices_268, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_776, vertices_112, vertices_208, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_805), (false, vertices_481), (true, vertices_138), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_208), (true, vertices_656), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 24 25 26 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 18 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_451) then 27 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_481) then 28 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 28 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 138 2
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 1 0 2 3 6 138 666 2
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 138 426 2
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 84 724 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0701

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0702.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0702

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 185, 305, 465, 737, 206, 270, 342, 682, 778, 706, 572, 220, 780, 308, 49, 145, 273, 161, 289, 545, 193, 321, 577, 769, 14, 70, 262, 138, 266, 522, 194, 322, 578, 642, 770, 28, 204, 268, 524, 52, 84, 276, 292, 548, 772, 56, 152, 168, 552, 776, 304, 208, 336, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_185, vertices_305, vertices_465, vertices_737, vertices_206, vertices_270, vertices_342, vertices_682, vertices_778, vertices_706, vertices_572, vertices_220, vertices_780, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_262, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_204, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_772, vertices_56, vertices_152, vertices_168, vertices_552, vertices_776, vertices_304, vertices_208, vertices_336, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_185), (false, vertices_305), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_28), (true, vertices_204), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_552), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_204) then 21 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_52) then 12 else
  if p.val = (true, vertices_84) then 13 else
  if p.val = (true, vertices_276) then 14 else
  if p.val = (true, vertices_552) then 15 else
  if p.val = (true, vertices_776) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 70 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 5 70 342 2
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 138 682 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 220
cert_cover_5 7 1 1 2 3 5 28 220 3
cert_coverFacet 8 780
cert_cover_2 8 2 1 7 8 268 780 3
cert_coverFacet 9 308
cert_cover_2 9 3 1 4 7 52 308 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0702

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0703.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0703

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 653, 601, 457, 369, 657, 558, 310, 774, 626, 658, 898, 236, 484, 900, 616, 73, 137, 521, 81, 145, 273, 529, 321, 385, 641, 38, 262, 518, 50, 146, 274, 530, 546, 386, 642, 770, 44, 140, 524, 228, 292, 388, 644, 772, 104, 552, 200, 584, 112, 304, 592, 656, 352, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_653, vertices_601, vertices_457, vertices_369, vertices_657, vertices_558, vertices_310, vertices_774, vertices_626, vertices_658, vertices_898, vertices_236, vertices_484, vertices_900, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_38, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_228, vertices_292, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_200, vertices_584, vertices_112, vertices_304, vertices_592, vertices_656, vertices_352, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_653), (false, vertices_601), (false, vertices_457), (false, vertices_369), (false, vertices_657), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_44), (true, vertices_228), (true, vertices_292), (true, vertices_388), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_608), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_228) then 21 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_896) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 3 4 7 310 38 2
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 310
cert_cover_5 1 2 0 1 3 4 38 310 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 50 626 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 44 236 3
cert_coverFacet 7 484
cert_cover_5 7 0 1 4 5 7 228 484 3
cert_coverFacet 8 900
cert_cover_2 8 6 1 7 8 388 900 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0703

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0704.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0704

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 677, 569, 297, 713, 481, 590, 566, 214, 778, 466, 786, 436, 708, 312, 792, 41, 73, 265, 521, 161, 289, 545, 193, 321, 641, 22, 70, 518, 74, 266, 522, 210, 274, 530, 322, 770, 52, 148, 164, 548, 196, 580, 644, 56, 280, 536, 296, 584, 776, 304, 560, 400, 784, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_677, vertices_569, vertices_297, vertices_713, vertices_481, vertices_590, vertices_566, vertices_214, vertices_778, vertices_466, vertices_786, vertices_436, vertices_708, vertices_312, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_22, vertices_70, vertices_518, vertices_74, vertices_266, vertices_522, vertices_210, vertices_274, vertices_530, vertices_322, vertices_770, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_584, vertices_776, vertices_304, vertices_560, vertices_400, vertices_784, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_677), (false, vertices_569), (false, vertices_297), (false, vertices_713), (false, vertices_481), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_52), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_280), (true, vertices_776), (true, vertices_304), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_210) then 19 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 7 210 466 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0704

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0705.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0705

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 589, 357, 901, 625, 673, 654, 570, 282, 394, 370, 674, 220, 468, 600, 408, 69, 261, 517, 97, 161, 289, 545, 577, 385, 641, 26, 138, 266, 522, 50, 274, 162, 290, 546, 386, 642, 76, 140, 524, 212, 324, 388, 644, 88, 152, 280, 536, 584, 392, 112, 560, 336, 592, 400, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_589, vertices_357, vertices_901, vertices_625, vertices_673, vertices_654, vertices_570, vertices_282, vertices_394, vertices_370, vertices_674, vertices_220, vertices_468, vertices_600, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_524, vertices_212, vertices_324, vertices_388, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_584, vertices_392, vertices_112, vertices_560, vertices_336, vertices_592, vertices_400, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_589), (false, vertices_357), (false, vertices_901), (false, vertices_625), (false, vertices_673), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_546), (true, vertices_642), (true, vertices_140), (true, vertices_212), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_901) then 23 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_212) then 24 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_2 1 1 3 5 6 212
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 0 2 3 4 8 570 26 3
cert_rows
cert_pivot_2 7 5 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 570
cert_cover_5 1 3 0 2 3 4 26 570 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 370
cert_cover_5 4 0 0 3 4 5 50 370 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 76 220 2
cert_coverFacet 7 468
cert_cover_5 7 1 1 3 5 7 212 468 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0705

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0706.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0706

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 541, 409, 617, 329, 721, 558, 182, 710, 434, 866, 284, 300, 308, 660, 360, 25, 73, 265, 521, 145, 529, 193, 321, 577, 385, 38, 134, 518, 178, 290, 546, 194, 322, 578, 386, 28, 44, 268, 524, 52, 148, 276, 532, 292, 644, 280, 104, 296, 552, 328, 304, 400, 656, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_541, vertices_409, vertices_617, vertices_329, vertices_721, vertices_558, vertices_182, vertices_710, vertices_434, vertices_866, vertices_284, vertices_300, vertices_308, vertices_660, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_38, vertices_134, vertices_518, vertices_178, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_644, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_304, vertices_400, vertices_656, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_541), (false, vertices_409), (false, vertices_617), (false, vertices_329), (false, vertices_721), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_178), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_178) then 19 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 329 38 134 518 290 546 578 44 268 52 148 276 292 644 296 304 352 451 178 541 409 617 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 6 178
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 3 2 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 4 38 182 2
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 7 178 434 3
cert_coverFacet 4 866
cert_cover_5 4 3 0 4 5 7 290 866 2
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0706

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0707.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0707

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 339, 803, 357, 593, 737, 398, 782, 154, 402, 236, 556, 468, 804, 696, 720, 19, 259, 515, 81, 529, 97, 289, 545, 321, 577, 270, 26, 138, 522, 146, 274, 386, 770, 44, 140, 524, 100, 292, 548, 196, 324, 388, 772, 152, 536, 168, 552, 208, 336, 592, 400, 656, 224, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_339, vertices_803, vertices_357, vertices_593, vertices_737, vertices_398, vertices_782, vertices_154, vertices_402, vertices_236, vertices_556, vertices_468, vertices_804, vertices_696, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_81, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_270, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_386, vertices_770, vertices_44, vertices_140, vertices_524, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_388, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_339), (false, vertices_803), (false, vertices_357), (false, vertices_593), (false, vertices_737), (true, vertices_270), (true, vertices_138), (true, vertices_146), (true, vertices_386), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_548), (true, vertices_196), (true, vertices_388), (true, vertices_772), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_208), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 17 24 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 21 else
  if p.val = (false, vertices_339) then 22 else
  if p.val = (false, vertices_803) then 23 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_270) then 19 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 24 => Sum.inl 2
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
cert_row_2 0 0 1 2 7 270
cert_row_4 1 1 3 5 6 7 468 196 1
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 270 398 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 8 270 782 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 44 236 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 468
cert_cover_5 6 1 1 3 5 6 196 468 1
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 696
cert_cover_5 8 3 2 3 4 6 152 696 2
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0707

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0708.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0708

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 659, 803, 781, 357, 581, 593, 654, 58, 154, 554, 460, 724, 440, 808, 496, 19, 35, 515, 69, 261, 517, 81, 529, 97, 289, 577, 769, 26, 42, 138, 522, 50, 146, 546, 642, 140, 268, 524, 196, 324, 580, 644, 56, 152, 296, 552, 392, 776, 112, 432, 208, 592, 656, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_659, vertices_803, vertices_781, vertices_357, vertices_581, vertices_593, vertices_654, vertices_58, vertices_154, vertices_554, vertices_460, vertices_724, vertices_440, vertices_808, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_69, vertices_261, vertices_517, vertices_81, vertices_529, vertices_97, vertices_289, vertices_577, vertices_769, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_146, vertices_546, vertices_642, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_152, vertices_296, vertices_552, vertices_392, vertices_776, vertices_112, vertices_432, vertices_208, vertices_592, vertices_656, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_659), (false, vertices_803), (false, vertices_781), (false, vertices_357), (false, vertices_581), (false, vertices_593), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_56), (true, vertices_152), (true, vertices_296), (true, vertices_552), (true, vertices_392), (true, vertices_432), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 17 else
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_432) then 25 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 1 2 6 8 654 138 1
cert_row_4 2 1 2 5 6 7 460 140 2
cert_row_4 3 1 3 5 6 8 724 196 1
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 138 654 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 460
cert_cover_5 4 2 1 2 5 6 140 460 2
cert_coverFacet 5 724
cert_cover_5 5 3 1 3 5 6 196 724 1
cert_coverFacet 6 440
cert_cover_5 6 0 2 3 4 6 56 440 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coverFacet 8 496
cert_cover_5 8 0 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0708

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0709.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0709

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 293, 837, 457, 433, 737, 62, 526, 90, 842, 690, 722, 412, 780, 308, 216, 37, 261, 517, 161, 289, 545, 193, 321, 577, 385, 14, 38, 518, 26, 74, 522, 50, 82, 658, 546, 578, 28, 268, 524, 52, 276, 292, 772, 88, 152, 200, 328, 392, 776, 176, 304, 208, 400, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_293, vertices_837, vertices_457, vertices_433, vertices_737, vertices_62, vertices_526, vertices_90, vertices_842, vertices_690, vertices_722, vertices_412, vertices_780, vertices_308, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_14, vertices_38, vertices_518, vertices_26, vertices_74, vertices_522, vertices_50, vertices_82, vertices_658, vertices_546, vertices_578, vertices_28, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_88, vertices_152, vertices_200, vertices_328, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_293), (false, vertices_837), (false, vertices_457), (false, vertices_433), (false, vertices_737), (true, vertices_14), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_658), (true, vertices_578), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_88), (true, vertices_152), (true, vertices_776), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_658) then 19 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_152) then 14 else
  if p.val = (true, vertices_776) then 15 else
  if p.val = (true, vertices_208) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 293 14 26 74 522 50 82 578 28 268 524 52 276 88 152 776 208 551 658 837 457 433 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 62 14 3
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_2 2 0 3 6 8 658
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 90
cert_cover_2 2 2 0 3 5 26 90 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 74 842 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 50 690 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 82 722 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coverFacet 9 216
cert_cover_2 9 3 2 5 6 88 216 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0709

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0710.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0710

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 109, 309, 213, 313, 537, 713, 406, 282, 538, 618, 298, 930, 356, 964, 864, 21, 37, 69, 25, 41, 73, 521, 305, 145, 529, 193, 641, 26, 42, 266, 522, 146, 274, 530, 290, 546, 386, 642, 148, 276, 100, 292, 196, 324, 388, 280, 536, 104, 296, 584, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_109, vertices_309, vertices_213, vertices_313, vertices_537, vertices_713, vertices_406, vertices_282, vertices_538, vertices_618, vertices_298, vertices_930, vertices_356, vertices_964, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_25, vertices_41, vertices_73, vertices_521, vertices_305, vertices_145, vertices_529, vertices_193, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_280, vertices_536, vertices_104, vertices_296, vertices_584, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_109), (false, vertices_309), (false, vertices_213), (false, vertices_313), (false, vertices_537), (false, vertices_713), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_324), (true, vertices_388), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_309) then 24 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_313) then 25 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_832) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 42 618 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 290 930 2
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 964
cert_cover_5 7 3 1 5 6 7 196 964 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0710

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4563 : Certifies 4563 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0680.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4564 : Certifies 4564 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0681.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4565 : Certifies 4565 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0682.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4566 : Certifies 4566 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0683.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4567 : Certifies 4567 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0684.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4568 : Certifies 4568 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0685.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4569 : Certifies 4569 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0686.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4570 : Certifies 4570 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0687.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4571 : Certifies 4571 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0688.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4572 : Certifies 4572 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0689.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4573 : Certifies 4573 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0691.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4574 : Certifies 4574 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0692.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4575 : Certifies 4575 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0693.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4576 : Certifies 4576 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0694.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4577 : Certifies 4577 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0695.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4578 : Certifies 4578 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0696.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4579 : Certifies 4579 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0697.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4580 : Certifies 4580 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0698.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4581 : Certifies 4581 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0699.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4582 : Certifies 4582 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0700.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4583 : Certifies 4583 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0701.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4584 : Certifies 4584 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0702.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4585 : Certifies 4585 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0703.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4586 : Certifies 4586 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0704.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4587 : Certifies 4587 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0705.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4588 : Certifies 4588 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0706.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4589 : Certifies 4589 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0707.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4590 : Certifies 4590 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0708.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4591 : Certifies 4591 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0709.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4592 : Certifies 4592 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0710.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B151 (j : Fin 30) :
    Certifies (4563 + j.val) := by
  fin_cases j
  · exact projection_4563
  · exact projection_4564
  · exact projection_4565
  · exact projection_4566
  · exact projection_4567
  · exact projection_4568
  · exact projection_4569
  · exact projection_4570
  · exact projection_4571
  · exact projection_4572
  · exact projection_4573
  · exact projection_4574
  · exact projection_4575
  · exact projection_4576
  · exact projection_4577
  · exact projection_4578
  · exact projection_4579
  · exact projection_4580
  · exact projection_4581
  · exact projection_4582
  · exact projection_4583
  · exact projection_4584
  · exact projection_4585
  · exact projection_4586
  · exact projection_4587
  · exact projection_4588
  · exact projection_4589
  · exact projection_4590
  · exact projection_4591
  · exact projection_4592

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
