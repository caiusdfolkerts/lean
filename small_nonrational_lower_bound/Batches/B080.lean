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
/- Source: ProjectionCertificates/R_m14e10q1_0584.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0584

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 117, 181, 901, 681, 865, 94, 406, 282, 362, 120, 184, 920, 808, 53, 69, 133, 261, 97, 161, 545, 321, 641, 769, 22, 70, 262, 26, 74, 266, 274, 322, 84, 148, 388, 56, 88, 152, 280, 104, 168, 296, 552, 648, 776, 112, 176, 400, 352, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_117, vertices_181, vertices_901, vertices_681, vertices_865, vertices_94, vertices_406, vertices_282, vertices_362, vertices_120, vertices_184, vertices_920, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_53, vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_262, vertices_26, vertices_74, vertices_266, vertices_274, vertices_322, vertices_84, vertices_148, vertices_388, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_112, vertices_176, vertices_400, vertices_352, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_117), (false, vertices_181), (false, vertices_901), (false, vertices_681), (false, vertices_865), (true, vertices_22), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_274), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_776), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 2 4 5 7 362 74 2
cert_row_4 1 0 1 2 3 5 94 22 2
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 2 3 6 7 8 920 152 3
cert_rows
cert_pivot_2 4 5 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 22 94 2
cert_coverFacet 1 406
cert_cover_5 1 2 0 1 3 6 22 406 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 74 362 2
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 920
cert_cover_5 6 3 2 3 6 7 152 920 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0584

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0585.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0585

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 779, 563, 387, 109, 397, 617, 242, 402, 786, 844, 468, 228, 880, 35, 131, 259, 515, 13, 37, 133, 105, 265, 521, 545, 385, 50, 146, 274, 530, 162, 386, 770, 76, 268, 100, 164, 196, 324, 388, 584, 776, 112, 560, 208, 336, 400, 784, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_779, vertices_563, vertices_387, vertices_109, vertices_397, vertices_617, vertices_242, vertices_402, vertices_786, vertices_844, vertices_468, vertices_228, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_133, vertices_105, vertices_265, vertices_521, vertices_545, vertices_385, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_386, vertices_770, vertices_76, vertices_268, vertices_100, vertices_164, vertices_196, vertices_324, vertices_388, vertices_584, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_779), (false, vertices_563), (false, vertices_387), (false, vertices_109), (false, vertices_397), (false, vertices_617), (true, vertices_146), (true, vertices_274), (true, vertices_196), (true, vertices_324), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_224), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_4 2 1 3 5 6 7 468 196 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 0 0 3 4 5 50 242 3
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 76 844 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 196 468 1
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0585

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0589.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0589

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 551, 395, 787, 45, 233, 929, 94, 534, 346, 108, 852, 740, 968, 7, 11, 259, 515, 13, 37, 41, 137, 161, 545, 385, 769, 14, 22, 518, 90, 266, 274, 530, 44, 76, 84, 532, 100, 548, 580, 104, 200, 328, 392, 336, 784, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_551, vertices_395, vertices_787, vertices_45, vertices_233, vertices_929, vertices_94, vertices_534, vertices_346, vertices_108, vertices_852, vertices_740, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_13, vertices_37, vertices_41, vertices_137, vertices_161, vertices_545, vertices_385, vertices_769, vertices_14, vertices_22, vertices_518, vertices_90, vertices_266, vertices_274, vertices_530, vertices_44, vertices_76, vertices_84, vertices_532, vertices_100, vertices_548, vertices_580, vertices_104, vertices_200, vertices_328, vertices_392, vertices_336, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_551), (false, vertices_395), (false, vertices_787), (false, vertices_45), (false, vertices_233), (false, vertices_929), (true, vertices_22), (true, vertices_90), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_328), (true, vertices_336), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 12 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 0 0 2 3 5 90
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 84 852 3
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 100 740 3
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 200 968 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0589

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0593.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0593

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 781, 149, 421, 569, 361, 177, 214, 454, 774, 842, 626, 616, 496, 21, 133, 261, 517, 41, 265, 521, 49, 145, 529, 161, 289, 22, 198, 262, 518, 82, 530, 322, 578, 770, 148, 388, 772, 104, 552, 328, 584, 776, 112, 176, 560, 208, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_781, vertices_149, vertices_421, vertices_569, vertices_361, vertices_177, vertices_214, vertices_454, vertices_774, vertices_842, vertices_626, vertices_616, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_22, vertices_198, vertices_262, vertices_518, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_148, vertices_388, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_781), (false, vertices_149), (false, vertices_421), (false, vertices_569), (false, vertices_361), (false, vertices_177), (true, vertices_198), (true, vertices_262), (true, vertices_82), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_584), (true, vertices_112), (true, vertices_208), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (true, vertices_198) then 14 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 149 1 177 262 82 322 578 770 584 112 208 608 448 535 198 781 421 569 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 7 198 454 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 322 842 1
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 82 626 2
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0593

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0594.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0594

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 653, 421, 837, 345, 393, 678, 122, 186, 650, 866, 804, 408, 496, 133, 261, 517, 73, 137, 265, 521, 321, 577, 385, 58, 74, 138, 522, 98, 162, 546, 578, 642, 164, 292, 548, 644, 772, 88, 152, 280, 392, 648, 112, 176, 336, 400, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_653, vertices_421, vertices_837, vertices_345, vertices_393, vertices_678, vertices_122, vertices_186, vertices_650, vertices_866, vertices_804, vertices_408, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_385, vertices_58, vertices_74, vertices_138, vertices_522, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_392, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_653), (false, vertices_421), (false, vertices_837), (false, vertices_345), (false, vertices_393), (true, vertices_58), (true, vertices_138), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_548), (true, vertices_152), (true, vertices_112), (true, vertices_176), (true, vertices_400), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_58) then 15 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 186
cert_cover_5 2 0 0 2 3 6 58 186 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 98 866 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0594

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0595.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0595

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 789, 425, 201, 841, 625, 305, 118, 598, 166, 646, 714, 908, 436, 73, 137, 265, 49, 273, 529, 97, 161, 289, 193, 577, 769, 86, 38, 134, 518, 98, 162, 194, 578, 642, 52, 276, 532, 164, 388, 644, 772, 200, 584, 392, 648, 776, 112, 304, 592, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_789, vertices_425, vertices_201, vertices_841, vertices_625, vertices_305, vertices_118, vertices_598, vertices_166, vertices_646, vertices_714, vertices_908, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_49, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_769, vertices_86, vertices_38, vertices_134, vertices_518, vertices_98, vertices_162, vertices_194, vertices_578, vertices_642, vertices_52, vertices_276, vertices_532, vertices_164, vertices_388, vertices_644, vertices_772, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_592, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_789), (false, vertices_425), (false, vertices_201), (false, vertices_841), (false, vertices_625), (false, vertices_305), (true, vertices_86), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_52), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 13 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_648) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 7 436 52 3
cert_row_2 1 0 1 3 5 86
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 1 2 6 7 8 908 388 1
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 86 118 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 8 86 598 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 714
cert_cover_5 4 2 0 2 5 6 194 714 1
cert_coverFacet 5 908
cert_cover_5 5 3 1 2 6 7 388 908 1
cert_coverFacet 6 436
cert_cover_5 6 0 1 3 4 6 52 436 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0595

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0596.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0596

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 565, 277, 617, 169, 433, 342, 598, 646, 714, 482, 232, 880, 21, 133, 261, 517, 41, 137, 521, 49, 273, 161, 545, 385, 86, 134, 262, 518, 194, 322, 578, 386, 642, 276, 532, 644, 104, 168, 200, 584, 648, 304, 560, 336, 592, 224, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_565, vertices_277, vertices_617, vertices_169, vertices_433, vertices_342, vertices_598, vertices_646, vertices_714, vertices_482, vertices_232, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_521, vertices_49, vertices_273, vertices_161, vertices_545, vertices_385, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_276, vertices_532, vertices_644, vertices_104, vertices_168, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_336, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_565), (false, vertices_277), (false, vertices_617), (false, vertices_169), (false, vertices_433), (true, vertices_86), (true, vertices_518), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_200), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 277 1 169 518 194 322 578 642 200 336 592 224 352 391 86 653 565 617 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 7 86 342 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 194 714 1
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 194 482 1
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 304 880 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0596

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0599.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0599

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 27, 211, 899, 61, 117, 709, 282, 778, 434, 620, 312, 936, 752, 11, 19, 131, 515, 13, 53, 69, 517, 25, 81, 193, 641, 26, 266, 522, 146, 274, 386, 770, 44, 524, 100, 580, 56, 280, 296, 552, 776, 112, 176, 304, 208, 608, 416, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_27, vertices_211, vertices_899, vertices_61, vertices_117, vertices_709, vertices_282, vertices_778, vertices_434, vertices_620, vertices_312, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_131, vertices_515, vertices_13, vertices_53, vertices_69, vertices_517, vertices_25, vertices_81, vertices_193, vertices_641, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_770, vertices_44, vertices_524, vertices_100, vertices_580, vertices_56, vertices_280, vertices_296, vertices_552, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_608, vertices_416, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_27), (false, vertices_211), (false, vertices_899), (false, vertices_61), (false, vertices_117), (false, vertices_709), (true, vertices_266), (true, vertices_274), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_608), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 13 else
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_211) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_61) then 17 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_27), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 2 4 6 7 8 936 296 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 434
cert_cover_5 2 0 0 3 4 6 146 434 2
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 44 620 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 936
cert_cover_5 5 2 2 4 6 7 296 936 2
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0599

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0601.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0601

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 651, 147, 803, 93, 781, 217, 370, 178, 674, 716, 340, 868, 752, 19, 131, 259, 515, 13, 21, 261, 89, 137, 521, 145, 769, 50, 146, 274, 162, 290, 546, 642, 76, 524, 84, 276, 324, 580, 772, 200, 648, 112, 176, 208, 336, 352, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_651, vertices_147, vertices_803, vertices_93, vertices_781, vertices_217, vertices_370, vertices_178, vertices_674, vertices_716, vertices_340, vertices_868, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_13, vertices_21, vertices_261, vertices_89, vertices_137, vertices_521, vertices_145, vertices_769, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_76, vertices_524, vertices_84, vertices_276, vertices_324, vertices_580, vertices_772, vertices_200, vertices_648, vertices_112, vertices_176, vertices_208, vertices_336, vertices_352, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_651), (false, vertices_147), (false, vertices_803), (false, vertices_93), (false, vertices_781), (false, vertices_217), (true, vertices_50), (true, vertices_162), (true, vertices_324), (true, vertices_580), (true, vertices_112), (true, vertices_176), (true, vertices_336), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 4 5 7 8 868 324 1
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 0 0 3 4 5 50 370 3
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 76 716 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 868
cert_cover_5 5 2 1 4 5 7 324 868 1
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0601

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0602.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0602

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 675, 835, 453, 617, 225, 790, 658, 572, 220, 844, 404, 248, 688, 131, 259, 515, 97, 161, 545, 193, 321, 577, 385, 146, 274, 530, 642, 770, 28, 76, 524, 148, 276, 532, 196, 324, 388, 772, 56, 216, 104, 552, 584, 176, 560, 400, 656, 224, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_675, vertices_835, vertices_453, vertices_617, vertices_225, vertices_790, vertices_658, vertices_572, vertices_220, vertices_844, vertices_404, vertices_248, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_772, vertices_56, vertices_216, vertices_104, vertices_552, vertices_584, vertices_176, vertices_560, vertices_400, vertices_656, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_675), (false, vertices_835), (false, vertices_453), (false, vertices_617), (false, vertices_225), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_56), (true, vertices_216), (true, vertices_176), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_216) then 21 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 1 2 3 4 8 572 28 3
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 6 0 3 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 572
cert_cover_5 2 2 1 2 3 4 28 572 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 28 220 3
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 76 844 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 248
cert_cover_5 6 0 2 3 4 5 56 248 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0602

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0605.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0605

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 709, 601, 281, 457, 929, 542, 110, 678, 282, 362, 802, 588, 484, 25, 73, 265, 273, 529, 193, 577, 385, 641, 769, 14, 38, 518, 26, 106, 266, 274, 530, 290, 546, 770, 76, 524, 100, 164, 196, 580, 644, 280, 536, 328, 584, 352, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_709, vertices_601, vertices_281, vertices_457, vertices_929, vertices_542, vertices_110, vertices_678, vertices_282, vertices_362, vertices_802, vertices_588, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_518, vertices_26, vertices_106, vertices_266, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_76, vertices_524, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_280, vertices_536, vertices_328, vertices_584, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_709), (false, vertices_601), (false, vertices_281), (false, vertices_457), (false, vertices_929), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_106), (true, vertices_266), (true, vertices_290), (true, vertices_546), (true, vertices_76), (true, vertices_524), (true, vertices_100), (true, vertices_164), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 110
cert_cover_5 1 1 0 1 2 4 14 110 3
cert_coverFacet 2 678
cert_cover_5 2 2 0 1 4 6 38 678 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 362
cert_cover_5 4 1 0 2 4 7 106 362 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0605

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0606.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0606

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 709, 57, 217, 681, 369, 833, 398, 678, 838, 426, 348, 204, 312, 25, 41, 137, 49, 81, 289, 545, 193, 321, 577, 641, 769, 134, 262, 518, 394, 162, 290, 546, 770, 76, 140, 268, 196, 324, 580, 644, 56, 88, 280, 168, 296, 200, 304, 336, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_709, vertices_57, vertices_217, vertices_681, vertices_369, vertices_833, vertices_398, vertices_678, vertices_838, vertices_426, vertices_348, vertices_204, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_49, vertices_81, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_134, vertices_262, vertices_518, vertices_394, vertices_162, vertices_290, vertices_546, vertices_770, vertices_76, vertices_140, vertices_268, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_168, vertices_296, vertices_200, vertices_304, vertices_336, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_709), (false, vertices_57), (false, vertices_217), (false, vertices_681), (false, vertices_369), (false, vertices_833), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_394), (true, vertices_162), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_217) then 18 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_394) then 14 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 134 2
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 2 3 5 7 348 76 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 134 678 2
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 262 838 2
cert_coverFacet 3 426
cert_cover_5 3 1 0 2 4 6 394 426 2
cert_coverFacet 4 348
cert_cover_5 4 3 1 2 3 5 76 348 2
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0606

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0608.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0608

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 653, 53, 805, 841, 393, 433, 118, 614, 646, 714, 210, 472, 880, 21, 37, 133, 517, 137, 265, 521, 49, 145, 289, 385, 769, 22, 102, 134, 518, 82, 146, 194, 578, 642, 52, 548, 644, 200, 328, 584, 392, 648, 112, 304, 208, 336, 400, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_653, vertices_53, vertices_805, vertices_841, vertices_393, vertices_433, vertices_118, vertices_614, vertices_646, vertices_714, vertices_210, vertices_472, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_385, vertices_769, vertices_22, vertices_102, vertices_134, vertices_518, vertices_82, vertices_146, vertices_194, vertices_578, vertices_642, vertices_52, vertices_548, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_653), (false, vertices_53), (false, vertices_805), (false, vertices_841), (false, vertices_393), (false, vertices_433), (true, vertices_102), (true, vertices_518), (true, vertices_82), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_200), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_102) then 14 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 53 1 393 518 82 194 578 642 200 112 208 336 608 151 102 653 805 841 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 2 3 5 6 7 472 200 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 614
cert_cover_5 1 0 0 1 4 8 102 614 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 194 714 1
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 200 472 1
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0608

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0610.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0610

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 217, 281, 369, 961, 270, 526, 678, 294, 866, 188, 316, 752, 25, 137, 265, 521, 81, 273, 193, 321, 641, 769, 14, 38, 262, 518, 266, 522, 290, 546, 770, 60, 140, 268, 524, 164, 292, 644, 152, 280, 112, 176, 304, 208, 352, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_217, vertices_281, vertices_369, vertices_961, vertices_270, vertices_526, vertices_678, vertices_294, vertices_866, vertices_188, vertices_316, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_644, vertices_152, vertices_280, vertices_112, vertices_176, vertices_304, vertices_208, vertices_352, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_217), (false, vertices_281), (false, vertices_369), (false, vertices_961), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_546), (true, vertices_60), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_176), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 290 866 2
cert_coverFacet 5 188
cert_cover_5 5 0 1 2 3 6 60 188 3
cert_coverFacet 6 316
cert_cover_5 6 0 1 2 3 7 60 316 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0610

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0611.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0611

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 181, 805, 453, 569, 721, 206, 334, 666, 810, 706, 60, 156, 300, 37, 133, 261, 49, 145, 529, 545, 193, 321, 577, 769, 78, 138, 266, 522, 194, 322, 578, 642, 770, 28, 44, 140, 268, 52, 148, 292, 196, 324, 56, 152, 536, 296, 552, 656, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_181, vertices_805, vertices_453, vertices_569, vertices_721, vertices_206, vertices_334, vertices_666, vertices_810, vertices_706, vertices_60, vertices_156, vertices_300] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_49, vertices_145, vertices_529, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_78, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_148, vertices_292, vertices_196, vertices_324, vertices_56, vertices_152, vertices_536, vertices_296, vertices_552, vertices_656, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_181), (false, vertices_805), (false, vertices_453), (false, vertices_569), (false, vertices_721), (true, vertices_78), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_152), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (true, vertices_78) then 13 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_296) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 2 4 7 8 810 266 2
cert_rows_3
cert_pivot_3 3 1 0
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 6 138 666 2
cert_coverFacet 3 810
cert_cover_5 3 2 0 2 4 7 266 810 2
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0611

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0612.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0612

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 405, 197, 837, 665, 617, 201, 182, 310, 682, 658, 866, 236, 356, 69, 133, 261, 73, 137, 521, 145, 273, 529, 193, 577, 769, 54, 146, 274, 530, 162, 290, 546, 642, 770, 148, 276, 100, 164, 292, 196, 324, 104, 168, 552, 200, 648, 656, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_405, vertices_197, vertices_837, vertices_665, vertices_617, vertices_201, vertices_182, vertices_310, vertices_682, vertices_658, vertices_866, vertices_236, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_769, vertices_54, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_656, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_405), (false, vertices_197), (false, vertices_837), (false, vertices_665), (false, vertices_617), (false, vertices_201), (true, vertices_54), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_168), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 13 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 197 1 201 146 162 290 546 642 100 164 292 168 352 787 54 405 837 665 617
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 1 2 4 5 6 236 100 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 7 54 310 3
cert_coverFacet 2 682
cert_cover_5 2 2 0 2 4 6 162 682 1
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 290 866 2
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 100 236 1
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0612

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0613.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0613

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 421, 837, 601, 681, 182, 310, 666, 850, 674, 212, 340, 216, 69, 133, 261, 73, 137, 521, 161, 289, 545, 577, 769, 54, 146, 274, 530, 162, 290, 546, 642, 770, 84, 148, 276, 164, 292, 196, 324, 88, 152, 536, 200, 648, 208, 336, 592, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_421, vertices_837, vertices_601, vertices_681, vertices_182, vertices_310, vertices_666, vertices_850, vertices_674, vertices_212, vertices_340, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_577, vertices_769, vertices_54, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_88, vertices_152, vertices_536, vertices_200, vertices_648, vertices_208, vertices_336, vertices_592, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_421), (false, vertices_837), (false, vertices_601), (false, vertices_681), (true, vertices_54), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_152), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 12 else
  if p.val = (false, vertices_205) then 15 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (true, vertices_54) then 13 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_rows_3
cert_pivot_3 2 1 0
cert_heightProof 3
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 7 54 310 3
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 6 146 666 1
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 274 850 2
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0613

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0614.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0614

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 29, 77, 789, 357, 665, 617, 230, 422, 714, 914, 610, 220, 404, 13, 21, 69, 261, 25, 73, 521, 529, 97, 289, 545, 769, 166, 98, 290, 546, 194, 578, 386, 642, 770, 28, 76, 148, 276, 100, 292, 196, 388, 152, 200, 584, 648, 400, 656, 784, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_29, vertices_77, vertices_789, vertices_357, vertices_665, vertices_617, vertices_230, vertices_422, vertices_714, vertices_914, vertices_610, vertices_220, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_261, vertices_25, vertices_73, vertices_521, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_166, vertices_98, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_388, vertices_152, vertices_200, vertices_584, vertices_648, vertices_400, vertices_656, vertices_784, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_29), (false, vertices_77), (false, vertices_789), (false, vertices_357), (false, vertices_665), (false, vertices_617), (true, vertices_166), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_200), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_77) then 1 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (true, vertices_166) then 14 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 29 1 77 98 194 578 386 642 148 196 388 200 400 803 166 789 357 665 617
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 6 166
cert_row_4 1 0 3 6 7 8 914 386 1
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 1 2 3 5 6 220 28 3
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 5 166 230 3
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 7 166 422 3
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 194 714 1
cert_coverFacet 3 914
cert_cover_5 3 1 0 3 6 7 386 914 1
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 220
cert_cover_5 5 3 1 2 3 5 28 220 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0614

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0615.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0615

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 181, 277, 617, 169, 817, 214, 342, 646, 714, 866, 232, 496, 21, 133, 261, 517, 41, 137, 521, 49, 273, 161, 545, 769, 86, 134, 262, 518, 194, 322, 578, 642, 770, 148, 276, 644, 104, 168, 200, 584, 648, 176, 304, 208, 336, 224, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_181, vertices_277, vertices_617, vertices_169, vertices_817, vertices_214, vertices_342, vertices_646, vertices_714, vertices_866, vertices_232, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_521, vertices_49, vertices_273, vertices_161, vertices_545, vertices_769, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_148, vertices_276, vertices_644, vertices_104, vertices_168, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_181), (false, vertices_277), (false, vertices_617), (false, vertices_169), (false, vertices_817), (true, vertices_86), (true, vertices_134), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_200), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 277 1 169 134 194 322 578 642 200 208 336 224 352 775 86 653 181 617 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 194 714 1
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 176 496 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0615

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0617.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0617

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 557, 269, 421, 665, 241, 561, 334, 590, 650, 722, 482, 628, 356, 13, 37, 261, 137, 265, 521, 49, 145, 529, 161, 545, 385, 78, 138, 266, 522, 194, 322, 578, 386, 642, 268, 524, 100, 292, 548, 324, 580, 648, 112, 560, 208, 592, 656, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_557, vertices_269, vertices_421, vertices_665, vertices_241, vertices_561, vertices_334, vertices_590, vertices_650, vertices_722, vertices_482, vertices_628, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_545, vertices_385, vertices_78, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_648, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_557), (false, vertices_269), (false, vertices_421), (false, vertices_665), (false, vertices_241), (false, vertices_561), (true, vertices_78), (true, vertices_522), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_100), (true, vertices_324), (true, vertices_580), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (true, vertices_78) then 14 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 269 1 561 522 194 322 578 642 100 324 580 592 352 395 78 557 421 665 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 3 5 6 8 722 194 1
cert_row_4 3 1 3 4 5 8 628 100 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 194 722 1
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 194 482 1
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 100 628 1
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0617

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0620.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0620

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 213, 613, 153, 281, 849, 678, 186, 314, 650, 866, 372, 180, 69, 133, 517, 25, 137, 265, 521, 81, 145, 273, 577, 769, 58, 138, 266, 522, 162, 290, 546, 642, 770, 52, 84, 148, 100, 164, 548, 644, 152, 280, 648, 176, 304, 336, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_213, vertices_613, vertices_153, vertices_281, vertices_849, vertices_678, vertices_186, vertices_314, vertices_650, vertices_866, vertices_372, vertices_180] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_769, vertices_58, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_100, vertices_164, vertices_548, vertices_644, vertices_152, vertices_280, vertices_648, vertices_176, vertices_304, vertices_336, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_213), (false, vertices_613), (false, vertices_153), (false, vertices_281), (false, vertices_849), (true, vertices_58), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_164), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 6 58 186 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 7 58 314 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 290 866 2
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 52 372 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0620

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0621.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0621

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 541, 409, 297, 689, 481, 110, 526, 598, 738, 284, 364, 340, 976, 25, 41, 265, 521, 145, 529, 161, 289, 545, 385, 14, 70, 518, 42, 522, 98, 546, 578, 28, 108, 268, 524, 84, 276, 532, 324, 280, 296, 336, 592, 400, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_541, vertices_409, vertices_297, vertices_689, vertices_481, vertices_110, vertices_526, vertices_598, vertices_738, vertices_284, vertices_364, vertices_340, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_14, vertices_70, vertices_518, vertices_42, vertices_522, vertices_98, vertices_546, vertices_578, vertices_28, vertices_108, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_280, vertices_296, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_541), (false, vertices_409), (false, vertices_297), (false, vertices_689), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_98), (true, vertices_578), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_336), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 70 598 2
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 98 738 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 364
cert_cover_5 5 0 1 2 4 7 108 364 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 336 976 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0621

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0622.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0622

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 333, 85, 149, 901, 601, 809, 118, 182, 618, 594, 930, 484, 360, 21, 69, 133, 261, 73, 265, 521, 81, 145, 529, 641, 769, 54, 82, 146, 530, 98, 162, 546, 578, 642, 84, 148, 100, 164, 324, 388, 104, 296, 552, 328, 584, 592, 352, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_333, vertices_85, vertices_149, vertices_901, vertices_601, vertices_809, vertices_118, vertices_182, vertices_618, vertices_594, vertices_930, vertices_484, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_261, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_641, vertices_769, vertices_54, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_84, vertices_148, vertices_100, vertices_164, vertices_324, vertices_388, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_592, vertices_352, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_333), (false, vertices_85), (false, vertices_149), (false, vertices_901), (false, vertices_601), (false, vertices_809), (true, vertices_54), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_100), (true, vertices_164), (true, vertices_104), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_333) then 16 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 85 1 149 82 98 162 546 578 100 164 104 352 416 659 54 333 901 601 809
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 4 5 8 618 98 1
cert_row_4 2 0 4 6 7 8 930 162 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 5 54 118 3
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 6 54 182 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 5 98 618 1
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 162 930 3
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 100 484 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0622

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0632.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0632

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 59, 531, 109, 205, 661, 409, 282, 298, 914, 866, 740, 360, 968, 19, 35, 515, 77, 37, 133, 517, 25, 41, 137, 145, 529, 26, 42, 266, 274, 530, 290, 546, 770, 100, 548, 196, 644, 280, 104, 296, 200, 328, 392, 400, 656, 352, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_59, vertices_531, vertices_109, vertices_205, vertices_661, vertices_409, vertices_282, vertices_298, vertices_914, vertices_866, vertices_740, vertices_360, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_77, vertices_37, vertices_133, vertices_517, vertices_25, vertices_41, vertices_137, vertices_145, vertices_529, vertices_26, vertices_42, vertices_266, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_100, vertices_548, vertices_196, vertices_644, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_400, vertices_656, vertices_352, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_59), (false, vertices_531), (false, vertices_109), (false, vertices_205), (false, vertices_661), (false, vertices_409), (true, vertices_266), (true, vertices_274), (true, vertices_290), (true, vertices_770), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_59) then 14 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_109) then 16 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 3 6 7 8 914 274 2
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 914
cert_cover_5 2 0 0 3 6 7 274 914 2
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 290 866 2
cert_coverFacet 4 740
cert_cover_5 4 2 1 4 5 6 100 740 3
cert_coverFacet 5 360
cert_cover_2 5 4 2 5 7 104 360 3
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 200 968 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0632

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0633.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0633

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 61, 341, 805, 601, 681, 454, 666, 210, 594, 930, 188, 212, 420, 21, 37, 261, 25, 41, 521, 81, 545, 321, 577, 769, 82, 146, 530, 194, 322, 578, 386, 642, 770, 60, 84, 148, 164, 292, 196, 324, 388, 152, 536, 168, 648, 208, 592, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_61, vertices_341, vertices_805, vertices_601, vertices_681, vertices_454, vertices_666, vertices_210, vertices_594, vertices_930, vertices_188, vertices_212, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_25, vertices_41, vertices_521, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_82, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_60, vertices_84, vertices_148, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_152, vertices_536, vertices_168, vertices_648, vertices_208, vertices_592, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_61), (false, vertices_341), (false, vertices_805), (false, vertices_601), (false, vertices_681), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_164), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 82 1 146 2 530 194 386 642 148 164 196 388 152 208 416 835 61 341 805 601 681
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 0 4 6 7 8 930 386 1
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 146 666 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 930
cert_cover_5 4 3 0 4 6 7 386 930 1
cert_coverFacet 5 188
cert_cover_5 5 1 1 2 3 6 60 188 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0633

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0634.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0634

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 583, 403, 707, 93, 281, 241, 902, 620, 780, 120, 440, 808, 992, 7, 579, 131, 259, 13, 69, 25, 265, 81, 145, 273, 193, 262, 518, 386, 642, 76, 268, 524, 580, 772, 56, 88, 280, 104, 296, 552, 776, 112, 176, 400, 224, 608, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_583, vertices_403, vertices_707, vertices_93, vertices_281, vertices_241, vertices_902, vertices_620, vertices_780, vertices_120, vertices_440, vertices_808, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_579, vertices_131, vertices_259, vertices_13, vertices_69, vertices_25, vertices_265, vertices_81, vertices_145, vertices_273, vertices_193, vertices_262, vertices_518, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_580, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_776, vertices_112, vertices_176, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_583), (false, vertices_403), (false, vertices_707), (false, vertices_93), (false, vertices_281), (false, vertices_241), (true, vertices_524), (true, vertices_772), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_608), (true, vertices_416), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 13 else
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_93) then 14 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 281 1 524 772 56 104 296 552 776 608 416 800 896 271 93 583 403 707 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 262 2
cert_row_4 1 1 2 4 5 8 620 76 2
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 262 902 2
cert_coverFacet 1 620
cert_cover_5 1 1 1 2 4 5 76 620 2
cert_coverFacet 2 780
cert_cover_2 2 2 1 7 8 268 780 3
cert_coverFacet 3 120
cert_cover_2 3 3 2 4 5 56 120 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0634

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0637.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0637

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 213, 613, 389, 481, 286, 122, 618, 778, 434, 604, 404, 240, 69, 133, 261, 517, 97, 289, 545, 193, 385, 769, 26, 106, 266, 522, 50, 274, 290, 546, 770, 28, 268, 524, 84, 148, 276, 580, 388, 88, 584, 776, 112, 176, 208, 400, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_213, vertices_613, vertices_389, vertices_481, vertices_286, vertices_122, vertices_618, vertices_778, vertices_434, vertices_604, vertices_404, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_26, vertices_106, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_580, vertices_388, vertices_88, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_213), (false, vertices_613), (false, vertices_389), (false, vertices_481), (true, vertices_26), (true, vertices_106), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_28), (true, vertices_276), (true, vertices_88), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 2 3 7 286 26 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 26 286 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 26 122 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 8 106 618 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 50 434 3
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 28 604 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0637

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0638.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0638

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 405, 357, 165, 681, 817, 214, 342, 714, 786, 866, 620, 172, 204, 37, 133, 261, 145, 273, 529, 161, 289, 545, 641, 86, 146, 274, 530, 194, 322, 578, 642, 770, 44, 76, 140, 148, 276, 100, 164, 196, 324, 168, 552, 200, 584, 648, 784, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_405, vertices_357, vertices_165, vertices_681, vertices_817, vertices_214, vertices_342, vertices_714, vertices_786, vertices_866, vertices_620, vertices_172, vertices_204] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_86, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_148, vertices_276, vertices_100, vertices_164, vertices_196, vertices_324, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_784, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_405), (false, vertices_357), (false, vertices_165), (false, vertices_681), (false, vertices_817), (true, vertices_86), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_200), (true, vertices_584), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 165 274 194 322 578 770 44 76 140 196 200 584 608 659 86 405 357 681 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 194 714 1
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 44 620 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0638

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0640.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0640

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [47, 519, 787, 419, 525, 233, 905, 118, 534, 370, 108, 716, 852, 992, 7, 35, 259, 515, 13, 517, 41, 137, 521, 161, 385, 769, 22, 38, 518, 114, 274, 530, 290, 44, 76, 524, 84, 532, 100, 580, 104, 200, 648, 336, 784, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_47, vertices_519, vertices_787, vertices_419, vertices_525, vertices_233, vertices_905, vertices_118, vertices_534, vertices_370, vertices_108, vertices_716, vertices_852, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_259, vertices_515, vertices_13, vertices_517, vertices_41, vertices_137, vertices_521, vertices_161, vertices_385, vertices_769, vertices_22, vertices_38, vertices_518, vertices_114, vertices_274, vertices_530, vertices_290, vertices_44, vertices_76, vertices_524, vertices_84, vertices_532, vertices_100, vertices_580, vertices_104, vertices_200, vertices_648, vertices_336, vertices_784, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_47), (false, vertices_519), (false, vertices_787), (false, vertices_419), (false, vertices_525), (false, vertices_233), (false, vertices_905), (true, vertices_22), (true, vertices_114), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_336), (true, vertices_352), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 12 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_47) then 13 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_47), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 0 0 3 4 5 114
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 7 114 370 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 76 716 3
cert_coverFacet 5 852
cert_cover_5 5 2 1 3 5 7 84 852 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0640

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0642.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0642

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 421, 837, 617, 225, 902, 570, 218, 234, 658, 418, 604, 660, 69, 133, 261, 97, 161, 289, 545, 193, 577, 769, 26, 42, 202, 146, 530, 162, 290, 546, 386, 642, 770, 84, 148, 532, 580, 388, 644, 772, 88, 536, 104, 552, 584, 208, 656, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_421, vertices_837, vertices_617, vertices_225, vertices_902, vertices_570, vertices_218, vertices_234, vertices_658, vertices_418, vertices_604, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_26, vertices_42, vertices_202, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_580, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_104, vertices_552, vertices_584, vertices_208, vertices_656, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_421), (false, vertices_837), (false, vertices_617), (false, vertices_225), (true, vertices_26), (true, vertices_42), (true, vertices_202), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_532), (true, vertices_644), (true, vertices_88), (true, vertices_536), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 15 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 26 218 3
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 5 42 234 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 84 604 1
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0642

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2433 : Certifies 2433 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0584.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2434 : Certifies 2434 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0585.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2435 : Certifies 2435 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0589.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2436 : Certifies 2436 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0593.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2437 : Certifies 2437 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0594.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2438 : Certifies 2438 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0595.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2439 : Certifies 2439 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0596.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2440 : Certifies 2440 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0599.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2441 : Certifies 2441 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0601.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2442 : Certifies 2442 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0602.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2443 : Certifies 2443 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0605.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2444 : Certifies 2444 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0606.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2445 : Certifies 2445 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0608.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2446 : Certifies 2446 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0610.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2447 : Certifies 2447 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0611.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2448 : Certifies 2448 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0612.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2449 : Certifies 2449 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0613.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2450 : Certifies 2450 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0614.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2451 : Certifies 2451 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0615.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2452 : Certifies 2452 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0617.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2453 : Certifies 2453 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0620.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2454 : Certifies 2454 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0621.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2455 : Certifies 2455 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0622.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2456 : Certifies 2456 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0632.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2457 : Certifies 2457 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0633.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2458 : Certifies 2458 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0634.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2459 : Certifies 2459 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0637.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2460 : Certifies 2460 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0638.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2461 : Certifies 2461 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0640.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2462 : Certifies 2462 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0642.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B080 (j : Fin 30) :
    Certifies (2433 + j.val) := by
  fin_cases j
  · exact projection_2433
  · exact projection_2434
  · exact projection_2435
  · exact projection_2436
  · exact projection_2437
  · exact projection_2438
  · exact projection_2439
  · exact projection_2440
  · exact projection_2441
  · exact projection_2442
  · exact projection_2443
  · exact projection_2444
  · exact projection_2445
  · exact projection_2446
  · exact projection_2447
  · exact projection_2448
  · exact projection_2449
  · exact projection_2450
  · exact projection_2451
  · exact projection_2452
  · exact projection_2453
  · exact projection_2454
  · exact projection_2455
  · exact projection_2456
  · exact projection_2457
  · exact projection_2458
  · exact projection_2459
  · exact projection_2460
  · exact projection_2461
  · exact projection_2462

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
