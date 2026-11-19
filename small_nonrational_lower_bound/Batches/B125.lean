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
/- Source: ProjectionCertificates/R_m15e10q1_1227.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1227

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 901, 345, 233, 393, 865, 94, 206, 662, 370, 562, 226, 284, 396, 820, 73, 137, 265, 97, 161, 545, 321, 385, 641, 769, 78, 22, 134, 50, 82, 530, 98, 162, 546, 194, 642, 28, 140, 268, 276, 532, 388, 644, 772, 88, 280, 200, 392, 304, 560, 336, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_901, vertices_345, vertices_233, vertices_393, vertices_865, vertices_94, vertices_206, vertices_662, vertices_370, vertices_562, vertices_226, vertices_284, vertices_396, vertices_820] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_78, vertices_22, vertices_134, vertices_50, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_28, vertices_140, vertices_268, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_200, vertices_392, vertices_304, vertices_560, vertices_336, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_901), (false, vertices_345), (false, vertices_233), (false, vertices_393), (false, vertices_865), (true, vertices_78), (true, vertices_22), (true, vertices_134), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_194), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_532), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 393 22 134 50 82 530 98 194 28 140 268 276 532 304 560 675 78 901 345 233 865
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
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 820
cert_cover_5 8 3 1 3 4 7 276 820 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1227

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_1228.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1228

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 29, 109, 661, 581, 345, 961, 286, 302, 566, 658, 738, 418, 612, 488, 13, 21, 69, 517, 25, 73, 145, 273, 321, 577, 385, 641, 270, 22, 38, 146, 274, 530, 162, 290, 546, 386, 642, 28, 44, 532, 100, 548, 580, 280, 104, 296, 328, 656, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_29, vertices_109, vertices_661, vertices_581, vertices_345, vertices_961, vertices_286, vertices_302, vertices_566, vertices_658, vertices_738, vertices_418, vertices_612, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_517, vertices_25, vertices_73, vertices_145, vertices_273, vertices_321, vertices_577, vertices_385, vertices_641, vertices_270, vertices_22, vertices_38, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_532, vertices_100, vertices_548, vertices_580, vertices_280, vertices_104, vertices_296, vertices_328, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_29), (false, vertices_109), (false, vertices_661), (false, vertices_581), (false, vertices_345), (false, vertices_961), (true, vertices_270), (true, vertices_22), (true, vertices_38), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_548), (true, vertices_296), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 0 1 2 7 270
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 1 0 1 2 4 270 302 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1228

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_1229.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1229

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 205, 589, 789, 421, 865, 286, 218, 394, 114, 818, 418, 540, 396, 632, 77, 133, 261, 517, 97, 161, 289, 193, 577, 769, 26, 138, 266, 50, 82, 274, 98, 162, 290, 194, 386, 28, 140, 268, 524, 276, 532, 388, 88, 536, 200, 584, 392, 112, 560, 784, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_205, vertices_589, vertices_789, vertices_421, vertices_865, vertices_286, vertices_218, vertices_394, vertices_114, vertices_818, vertices_418, vertices_540, vertices_396, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_50, vertices_82, vertices_274, vertices_98, vertices_162, vertices_290, vertices_194, vertices_386, vertices_28, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_388, vertices_88, vertices_536, vertices_200, vertices_584, vertices_392, vertices_112, vertices_560, vertices_784, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_205), (false, vertices_589), (false, vertices_789), (false, vertices_421), (false, vertices_865), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_268), (true, vertices_88), (true, vertices_536), (true, vertices_392), (true, vertices_112), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 0 2 3 5 6 218 26 3
cert_row_4 2 0 3 4 7 8 818 50 3
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 26 218 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 50 818 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 88 632 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1229

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_1230.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1230

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 659, 453, 569, 369, 737, 30, 398, 310, 538, 714, 60, 620, 204, 356, 147, 49, 273, 529, 97, 545, 193, 321, 385, 641, 14, 22, 262, 26, 138, 522, 274, 530, 386, 642, 28, 44, 76, 140, 52, 100, 292, 196, 324, 388, 56, 536, 552, 200, 584, 304, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_659, vertices_453, vertices_569, vertices_369, vertices_737, vertices_30, vertices_398, vertices_310, vertices_538, vertices_714, vertices_60, vertices_620, vertices_204, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_14, vertices_22, vertices_262, vertices_26, vertices_138, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_140, vertices_52, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_536, vertices_552, vertices_200, vertices_584, vertices_304, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_659), (false, vertices_453), (false, vertices_569), (false, vertices_369), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_52), (true, vertices_100), (true, vertices_292), (true, vertices_200), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 398
cert_cover_5 1 1 0 1 2 6 14 398 3
cert_coverFacet 2 310
cert_cover_5 2 0 0 1 3 4 22 310 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 714
cert_cover_5 4 2 0 2 5 6 138 714 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1230

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_1231.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1231

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 523, 51, 595, 653, 369, 737, 790, 314, 778, 236, 364, 780, 724, 340, 11, 19, 35, 515, 137, 521, 49, 81, 97, 161, 577, 641, 42, 266, 522, 50, 274, 530, 770, 108, 140, 268, 524, 84, 276, 532, 196, 324, 644, 772, 168, 296, 776, 304, 336, 592, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_523, vertices_51, vertices_595, vertices_653, vertices_369, vertices_737, vertices_790, vertices_314, vertices_778, vertices_236, vertices_364, vertices_780, vertices_724, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_515, vertices_137, vertices_521, vertices_49, vertices_81, vertices_97, vertices_161, vertices_577, vertices_641, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_108, vertices_140, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_644, vertices_772, vertices_168, vertices_296, vertices_776, vertices_304, vertices_336, vertices_592, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_523), (false, vertices_51), (false, vertices_595), (false, vertices_653), (false, vertices_369), (false, vertices_737), (true, vertices_266), (true, vertices_274), (true, vertices_770), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_772), (true, vertices_296), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 15 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_51) then 1 else
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 8 724 84 3
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 0 2 3 4 7 314 42 2
cert_rows
cert_pivot_2 6 5 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 314
cert_cover_5 1 3 0 2 3 4 42 314 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 236
cert_cover_5 3 1 1 2 4 6 108 236 3
cert_coverFacet 4 364
cert_cover_5 4 1 1 2 4 7 108 364 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 724
cert_cover_5 6 0 1 3 5 6 84 724 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1231

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_1232.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1232

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 295, 155, 163, 781, 681, 865, 30, 214, 102, 738, 284, 372, 472, 968, 7, 11, 35, 131, 13, 261, 137, 521, 161, 289, 545, 769, 14, 22, 38, 70, 26, 146, 98, 162, 194, 28, 268, 84, 276, 100, 292, 152, 280, 456, 648, 776, 208, 336, 352, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_295, vertices_155, vertices_163, vertices_781, vertices_681, vertices_865, vertices_30, vertices_214, vertices_102, vertices_738, vertices_284, vertices_372, vertices_472, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_35, vertices_131, vertices_13, vertices_261, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_769, vertices_14, vertices_22, vertices_38, vertices_70, vertices_26, vertices_146, vertices_98, vertices_162, vertices_194, vertices_28, vertices_268, vertices_84, vertices_276, vertices_100, vertices_292, vertices_152, vertices_280, vertices_456, vertices_648, vertices_776, vertices_208, vertices_336, vertices_352, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_295), (false, vertices_155), (false, vertices_163), (false, vertices_781), (false, vertices_681), (false, vertices_865), (true, vertices_22), (true, vertices_70), (true, vertices_98), (true, vertices_194), (true, vertices_28), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_280), (true, vertices_456), (true, vertices_208), (true, vertices_336), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_163) then 1 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_456) then 21 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 5 6 7 456
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_4 2 0 1 3 5 6 214 22 3
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 214
cert_cover_5 1 2 0 1 3 5 22 214 3
cert_coverFacet 2 102
cert_cover_2 2 1 0 4 5 38 102 3
cert_coverFacet 3 738
cert_cover_5 3 1 0 4 5 6 98 738 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 84 372 2
cert_coverFacet 6 472
cert_cover_5 6 0 2 3 5 6 152 472 2
cert_coverFacet 7 968
cert_cover_5 7 0 2 5 6 8 456 968 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1232

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_1233.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1233

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 157, 653, 309, 465, 929, 590, 270, 294, 346, 482, 610, 284, 216, 744, 141, 21, 37, 517, 145, 273, 289, 545, 385, 641, 14, 38, 262, 518, 74, 266, 98, 290, 546, 322, 578, 28, 268, 524, 276, 292, 88, 152, 280, 200, 584, 648, 208, 336, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_157, vertices_653, vertices_309, vertices_465, vertices_929, vertices_590, vertices_270, vertices_294, vertices_346, vertices_482, vertices_610, vertices_284, vertices_216, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_21, vertices_37, vertices_517, vertices_145, vertices_273, vertices_289, vertices_545, vertices_385, vertices_641, vertices_14, vertices_38, vertices_262, vertices_518, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_28, vertices_268, vertices_524, vertices_276, vertices_292, vertices_88, vertices_152, vertices_280, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_157), (false, vertices_653), (false, vertices_309), (false, vertices_465), (false, vertices_929), (true, vertices_14), (true, vertices_262), (true, vertices_74), (true, vertices_266), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_268), (true, vertices_88), (true, vertices_280), (true, vertices_200), (true, vertices_584), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 2 3 5 7 346 74 2
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 346
cert_cover_5 3 1 0 2 3 5 74 346 2
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 98 482 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 200 744 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1233

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_1234.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1234

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 707, 613, 409, 369, 689, 590, 270, 342, 682, 394, 188, 284, 556, 116, 195, 49, 145, 273, 97, 545, 321, 577, 385, 641, 14, 70, 262, 138, 266, 522, 322, 578, 386, 642, 28, 44, 268, 524, 52, 84, 276, 100, 548, 580, 152, 280, 168, 552, 392, 112, 176, 336, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_707, vertices_613, vertices_409, vertices_369, vertices_689, vertices_590, vertices_270, vertices_342, vertices_682, vertices_394, vertices_188, vertices_284, vertices_556, vertices_116] (by decide +kernel)
  polygons := literalFinset [vertices_195, vertices_49, vertices_145, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_70, vertices_262, vertices_138, vertices_266, vertices_522, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_100, vertices_548, vertices_580, vertices_152, vertices_280, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_336, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_707), (false, vertices_613), (false, vertices_409), (false, vertices_369), (false, vertices_689), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_168), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_552) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 70 2
cert_row_4 1 0 1 2 5 8 590 14 3
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 2 3 4 6 188 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 5 70 342 2
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 138 682 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 188
cert_cover_5 5 3 1 2 3 4 28 188 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 116
cert_cover_2 8 3 1 4 5 52 116 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1234

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_1235.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1235

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 171, 395, 563, 677, 453, 122, 282, 786, 716, 836, 472, 616, 680, 880, 139, 35, 259, 515, 133, 261, 517, 161, 545, 385, 26, 42, 266, 50, 274, 530, 770, 196, 324, 580, 644, 772, 88, 280, 104, 168, 552, 200, 584, 392, 648, 112, 560, 336, 784, 608, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_171, vertices_395, vertices_563, vertices_677, vertices_453, vertices_122, vertices_282, vertices_786, vertices_716, vertices_836, vertices_472, vertices_616, vertices_680, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_35, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_161, vertices_545, vertices_385, vertices_26, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_770, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_88, vertices_280, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_171), (false, vertices_395), (false, vertices_563), (false, vertices_677), (false, vertices_453), (true, vertices_26), (true, vertices_274), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_112), (true, vertices_336), (true, vertices_784), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_171) then 20 else
  if p.val = (false, vertices_395) then 21 else
  if p.val = (false, vertices_563) then 22 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 5 122 26 3
cert_row_4 1 1 2 5 6 8 716 196 1
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 122
cert_cover_5 0 0 0 2 3 4 26 122 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 196 716 1
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1235

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_1236.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1236

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 901, 569, 345, 425, 785, 710, 362, 618, 466, 418, 604, 212, 404, 788, 25, 41, 265, 273, 529, 161, 545, 385, 641, 769, 106, 162, 290, 546, 194, 322, 578, 386, 642, 84, 148, 276, 532, 196, 580, 388, 644, 772, 88, 536, 296, 552, 328, 584, 208, 336, 400, 784, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_901, vertices_569, vertices_345, vertices_425, vertices_785, vertices_710, vertices_362, vertices_618, vertices_466, vertices_418, vertices_604, vertices_212, vertices_404, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_106, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_208, vertices_336, vertices_400, vertices_784, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_901), (false, vertices_569), (false, vertices_345), (false, vertices_425), (false, vertices_785), (true, vertices_106), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_584), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 7 106 362 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 466
cert_cover_5 3 1 0 3 5 6 194 466 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 84 604 1
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1236

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_1238.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1238

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 299, 771, 681, 433, 961, 94, 710, 346, 834, 540, 692, 468, 312, 568, 11, 259, 515, 41, 521, 161, 289, 385, 641, 769, 14, 70, 518, 90, 266, 322, 578, 770, 28, 524, 84, 148, 532, 196, 644, 56, 280, 536, 296, 552, 176, 304, 560, 336, 400, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_299, vertices_771, vertices_681, vertices_433, vertices_961, vertices_94, vertices_710, vertices_346, vertices_834, vertices_540, vertices_692, vertices_468, vertices_312, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_41, vertices_521, vertices_161, vertices_289, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_518, vertices_90, vertices_266, vertices_322, vertices_578, vertices_770, vertices_28, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_176, vertices_304, vertices_560, vertices_336, vertices_400, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_299), (false, vertices_771), (false, vertices_681), (false, vertices_433), (false, vertices_961), (true, vertices_70), (true, vertices_90), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 15 20 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 16 else
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_90) then 19 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 0 4 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 710
cert_cover_5 1 1 0 1 5 6 70 710 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 148 692 2
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1238

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_1239.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1239

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 551, 835, 397, 181, 929, 526, 602, 458, 156, 540, 628, 248, 480, 864, 7, 259, 515, 269, 37, 133, 161, 545, 385, 769, 14, 518, 74, 266, 522, 322, 578, 28, 140, 524, 52, 148, 532, 548, 88, 152, 536, 200, 392, 112, 176, 592, 224, 352, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_551, vertices_835, vertices_397, vertices_181, vertices_929, vertices_526, vertices_602, vertices_458, vertices_156, vertices_540, vertices_628, vertices_248, vertices_480, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_259, vertices_515, vertices_269, vertices_37, vertices_133, vertices_161, vertices_545, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_266, vertices_522, vertices_322, vertices_578, vertices_28, vertices_140, vertices_524, vertices_52, vertices_148, vertices_532, vertices_548, vertices_88, vertices_152, vertices_536, vertices_200, vertices_392, vertices_112, vertices_176, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_551), (false, vertices_835), (false, vertices_397), (false, vertices_181), (false, vertices_929), (true, vertices_74), (true, vertices_522), (true, vertices_28), (true, vertices_524), (true, vertices_532), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_112), (true, vertices_592), (true, vertices_224), (true, vertices_352), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 19 else
  if p.val = (false, vertices_551) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 6 74 458 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 52 628 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1239

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_1240.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1240

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 453, 773, 809, 737, 94, 334, 314, 178, 722, 450, 572, 780, 688, 69, 261, 517, 161, 289, 545, 193, 577, 385, 769, 78, 26, 266, 50, 82, 146, 162, 290, 194, 322, 386, 28, 268, 524, 84, 532, 324, 772, 56, 296, 552, 776, 176, 560, 592, 656, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_453, vertices_773, vertices_809, vertices_737, vertices_94, vertices_334, vertices_314, vertices_178, vertices_722, vertices_450, vertices_572, vertices_780, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_78, vertices_26, vertices_266, vertices_50, vertices_82, vertices_146, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_268, vertices_524, vertices_84, vertices_532, vertices_324, vertices_772, vertices_56, vertices_296, vertices_552, vertices_776, vertices_176, vertices_560, vertices_592, vertices_656, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_453), (false, vertices_773), (false, vertices_809), (false, vertices_737), (true, vertices_78), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_56), (true, vertices_176), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 773 26 266 50 82 146 194 322 28 268 524 56 176 560 656 419 78 597 453 809 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_2 2 0 1 2 5 78
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 2 0 1 2 7 78 334 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 26 314 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1240

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_1241.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1241

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 659, 597, 617, 425, 241, 542, 302, 278, 394, 466, 556, 340, 484, 612, 643, 41, 137, 521, 81, 145, 529, 97, 161, 577, 14, 22, 262, 138, 266, 522, 146, 274, 530, 386, 44, 524, 84, 276, 532, 100, 292, 548, 324, 580, 296, 552, 392, 208, 336, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_659, vertices_597, vertices_617, vertices_425, vertices_241, vertices_542, vertices_302, vertices_278, vertices_394, vertices_466, vertices_556, vertices_340, vertices_484, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_643, vertices_41, vertices_137, vertices_521, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_577, vertices_14, vertices_22, vertices_262, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_44, vertices_524, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_296, vertices_552, vertices_392, vertices_208, vertices_336, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_659), (false, vertices_597), (false, vertices_617), (false, vertices_425), (false, vertices_241), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_266), (true, vertices_274), (true, vertices_386), (true, vertices_44), (true, vertices_524), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_4 1 0 1 2 4 7 302 14 3
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 302
cert_cover_5 1 1 0 1 2 4 14 302 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 146 466 2
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1241

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_1243.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1243

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 285, 541, 357, 709, 625, 654, 570, 282, 458, 418, 674, 204, 332, 992, 29, 69, 261, 517, 49, 273, 529, 97, 289, 577, 26, 138, 266, 522, 50, 274, 162, 290, 546, 386, 642, 76, 140, 268, 524, 196, 324, 644, 280, 536, 200, 328, 560, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_285, vertices_541, vertices_357, vertices_709, vertices_625, vertices_654, vertices_570, vertices_282, vertices_458, vertices_418, vertices_674, vertices_204, vertices_332, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_280, vertices_536, vertices_200, vertices_328, vertices_560, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_285), (false, vertices_541), (false, vertices_357), (false, vertices_709), (false, vertices_625), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_200), (true, vertices_328), (true, vertices_416), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 2 138 1 266 522 162 546 386 642 76 140 200 328 416 672 448 307 285 541 357 709 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 2 5 6 7 458 138 2
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 1 3 0 4
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 26 570 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 458
cert_cover_5 3 2 0 2 5 6 138 458 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 352 992 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1243

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_1244.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1244

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 563, 419, 677, 453, 602, 282, 306, 348, 204, 652, 744, 880, 480, 15, 35, 259, 515, 133, 261, 517, 161, 545, 385, 26, 266, 522, 50, 274, 530, 290, 76, 140, 268, 524, 196, 324, 644, 88, 280, 200, 584, 648, 304, 560, 336, 592, 224, 352, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_563, vertices_419, vertices_677, vertices_453, vertices_602, vertices_282, vertices_306, vertices_348, vertices_204, vertices_652, vertices_744, vertices_880, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_35, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_161, vertices_545, vertices_385, vertices_26, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_88, vertices_280, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_336, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_563), (false, vertices_419), (false, vertices_677), (false, vertices_453), (true, vertices_26), (true, vertices_274), (true, vertices_76), (true, vertices_140), (true, vertices_88), (true, vertices_280), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_304), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 15 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_563) then 19 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 1 2 3 5 7 348 76 2
cert_row_4 2 2 4 5 6 8 744 200 1
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 26 602 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 348
cert_cover_5 3 1 1 2 3 5 76 348 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 200 744 1
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 304 880 2
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1244

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_1245.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1245

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [75, 395, 115, 291, 309, 713, 465, 806, 618, 778, 244, 660, 788, 740, 920, 11, 35, 67, 259, 73, 137, 49, 81, 273, 289, 193, 385, 74, 266, 522, 98, 290, 546, 770, 52, 148, 276, 532, 228, 292, 548, 644, 772, 584, 392, 648, 776, 112, 208, 400, 656, 784, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_75, vertices_395, vertices_115, vertices_291, vertices_309, vertices_713, vertices_465, vertices_806, vertices_618, vertices_778, vertices_244, vertices_660, vertices_788, vertices_740, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_67, vertices_259, vertices_73, vertices_137, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_770, vertices_52, vertices_148, vertices_276, vertices_532, vertices_228, vertices_292, vertices_548, vertices_644, vertices_772, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_208, vertices_400, vertices_656, vertices_784, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_75), (false, vertices_395), (false, vertices_115), (false, vertices_291), (false, vertices_309), (false, vertices_713), (false, vertices_465), (true, vertices_522), (true, vertices_546), (true, vertices_770), (true, vertices_148), (true, vertices_532), (true, vertices_228), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_776), (true, vertices_656), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_291) then 1 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_228) then 19 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 75 291 522 546 770 148 532 548 644 772 776 656 784 608 395 115 309 228 713 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 6 7 8 920 392 1
cert_row_2 1 1 4 5 6 228
cert_row_4 2 0 1 4 7 8 806 290 1
cert_row_4 3 0 2 4 5 8 618 74 2
cert_rows
cert_pivot_2 3 6 1 0
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 290 806 1
cert_coverFacet 1 618
cert_cover_5 1 3 0 2 4 5 74 618 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 740
cert_cover_5 6 1 1 4 5 8 228 740 3
cert_coverFacet 7 920
cert_cover_5 7 0 2 3 6 7 392 920 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1245

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_1246.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1246

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 341, 709, 785, 929, 334, 590, 570, 426, 114, 354, 684, 368, 816, 69, 133, 261, 81, 273, 529, 577, 385, 641, 769, 78, 42, 266, 522, 50, 82, 530, 98, 290, 322, 578, 140, 268, 524, 324, 580, 644, 168, 552, 392, 112, 304, 560, 336, 784, 352, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_341, vertices_709, vertices_785, vertices_929, vertices_334, vertices_590, vertices_570, vertices_426, vertices_114, vertices_354, vertices_684, vertices_368, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_644, vertices_168, vertices_552, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_352, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_341), (false, vertices_709), (false, vertices_785), (false, vertices_929), (true, vertices_78), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_524), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 42 426 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1246

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_1249.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1249

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 397, 345, 665, 625, 833, 654, 614, 166, 370, 418, 834, 316, 572, 420, 25, 137, 265, 81, 529, 321, 577, 385, 641, 769, 38, 134, 518, 98, 162, 290, 322, 578, 386, 642, 770, 60, 140, 268, 524, 164, 292, 548, 388, 280, 536, 648, 112, 304, 560, 336, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_397, vertices_345, vertices_665, vertices_625, vertices_833, vertices_654, vertices_614, vertices_166, vertices_370, vertices_418, vertices_834, vertices_316, vertices_572, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_518, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_397), (false, vertices_345), (false, vertices_665), (false, vertices_625), (false, vertices_833), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_60), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 833 2 38 1 134 3 518 98 162 290 322 578 524 164 292 548 304 416 899 397 60 345 665 625
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
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1249

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_1251.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1251

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 651, 451, 357, 709, 570, 154, 402, 316, 628, 408, 360, 616, 968, 23, 131, 259, 515, 69, 261, 517, 193, 321, 641, 26, 138, 522, 146, 274, 530, 386, 52, 276, 532, 100, 292, 580, 56, 152, 280, 104, 296, 552, 328, 584, 392, 648, 560, 400, 352, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_651, vertices_451, vertices_357, vertices_709, vertices_570, vertices_154, vertices_402, vertices_316, vertices_628, vertices_408, vertices_360, vertices_616, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_193, vertices_321, vertices_641, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_580, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_560, vertices_400, vertices_352, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_651), (false, vertices_451), (false, vertices_357), (false, vertices_709), (true, vertices_26), (true, vertices_146), (true, vertices_52), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_560), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 15 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 18 else
  if p.val = (false, vertices_535) then 19 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 2 26 0 146 1 52 56 152 280 104 296 552 328 584 392 560 400 608 651 279 535 451 357 709
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 2 5 6 7 8 968 328 2
cert_row_4 2 1 2 3 4 7 316 52 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 0 0 2 3 4 26 570 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 316
cert_cover_5 3 2 1 2 3 4 52 316 1
cert_coverFacet 4 628
cert_cover_5 4 3 1 3 4 5 52 628 3
cert_coverFacet 5 408
cert_cover_2 5 3 2 6 7 152 408 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 968
cert_cover_5 8 1 2 5 6 7 328 968 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1251

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_1252.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1252

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 357, 709, 313, 625, 654, 454, 570, 154, 402, 408, 424, 680, 992, 23, 69, 261, 517, 49, 273, 529, 97, 289, 577, 134, 262, 518, 26, 138, 522, 146, 274, 530, 386, 196, 324, 644, 56, 152, 280, 168, 296, 552, 392, 648, 560, 400, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_357, vertices_709, vertices_313, vertices_625, vertices_654, vertices_454, vertices_570, vertices_154, vertices_402, vertices_408, vertices_424, vertices_680, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_196, vertices_324, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_560, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_357), (false, vertices_709), (false, vertices_313), (false, vertices_625), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_386), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 134 26 138 522 146 386 152 168 552 392 648 400 416 672 448 279 535 357 709 313 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 0 1 5 6 7 454 134 2
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 3 2 0 4
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 134 454 2
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 408
cert_cover_2 5 3 2 6 7 152 408 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 352 992 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1252

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_1253.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1253

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 357, 677, 345, 625, 654, 422, 602, 154, 402, 408, 872, 424, 680, 23, 37, 261, 517, 81, 273, 529, 97, 545, 321, 134, 262, 518, 26, 138, 522, 146, 274, 530, 386, 164, 292, 644, 88, 152, 280, 168, 296, 552, 328, 584, 392, 648, 592, 400, 352, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_357, vertices_677, vertices_345, vertices_625, vertices_654, vertices_422, vertices_602, vertices_154, vertices_402, vertices_408, vertices_872, vertices_424, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_164, vertices_292, vertices_644, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_357), (false, vertices_677), (false, vertices_345), (false, vertices_625), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_386), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 134 26 138 522 146 386 152 168 296 552 584 392 648 400 416 279 535 357 677 345 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 2 4 5 7 8 872 296 2
cert_row_4 2 0 1 2 6 8 654 134 2
cert_row_4 3 0 1 4 6 7 422 134 2
cert_rows
cert_pivot_2 3 5 2 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 422
cert_cover_5 1 3 0 1 4 6 134 422 2
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 408
cert_cover_2 5 3 2 6 7 152 408 3
cert_coverFacet 6 872
cert_cover_5 6 1 2 4 5 7 296 872 2
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1253

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_1254.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1254

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 775, 173, 333, 809, 689, 206, 342, 818, 722, 184, 312, 408, 456, 464, 519, 13, 133, 261, 41, 265, 161, 545, 641, 769, 70, 134, 262, 82, 274, 530, 194, 642, 770, 76, 140, 324, 56, 152, 280, 168, 296, 200, 328, 392, 176, 304, 560, 208, 336, 400, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_775, vertices_173, vertices_333, vertices_809, vertices_689, vertices_206, vertices_342, vertices_818, vertices_722, vertices_184, vertices_312, vertices_408, vertices_456, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_13, vertices_133, vertices_261, vertices_41, vertices_265, vertices_161, vertices_545, vertices_641, vertices_769, vertices_70, vertices_134, vertices_262, vertices_82, vertices_274, vertices_530, vertices_194, vertices_642, vertices_770, vertices_76, vertices_140, vertices_324, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_775), (false, vertices_173), (false, vertices_333), (false, vertices_809), (false, vertices_689), (true, vertices_70), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_392), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 70 82 274 530 194 56 152 280 200 392 304 208 336 400 448 647 775 173 333 809 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 70 2
cert_row_4 1 0 1 3 5 7 342 70 2
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 0 3 5 6 8 722 82 3
cert_rows
cert_pivot_2 2 1 4 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 70 206 2
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 70 342 2
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 274 818 2
cert_coverFacet 3 722
cert_cover_5 3 3 0 3 5 6 82 722 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1254

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e11q2_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 227, 547, 341, 817, 721, 353, 174, 302, 794, 802, 604, 284, 716, 484, 35, 131, 515, 81, 273, 529, 97, 289, 545, 193, 321, 641, 46, 138, 266, 522, 162, 290, 546, 770, 28, 588, 140, 268, 84, 276, 164, 292, 196, 324, 280, 536, 648, 592, 784, 224, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_227, vertices_547, vertices_341, vertices_817, vertices_721, vertices_353, vertices_174, vertices_302, vertices_794, vertices_802, vertices_604, vertices_284, vertices_716, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_46, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_770, vertices_28, vertices_588, vertices_140, vertices_268, vertices_84, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_280, vertices_536, vertices_648, vertices_592, vertices_784, vertices_224, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_227), (false, vertices_547), (false, vertices_341), (false, vertices_817), (false, vertices_721), (false, vertices_353), (true, vertices_46), (true, vertices_266), (true, vertices_290), (true, vertices_770), (true, vertices_28), (true, vertices_588), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_280), (true, vertices_536)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_588) then 19 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_2 1 1 2 5 8 588
cert_row_2 2 0 1 2 4 46
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 2 0 1 2 6 46 174 3
cert_coverFacet 1 302
cert_cover_5 1 2 0 1 2 7 46 302 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 266 794 2
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 604
cert_cover_5 4 1 1 2 3 5 28 604 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 716
cert_cover_5 6 1 1 2 5 6 588 716 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 164 484 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0000

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e11q2_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 779, 211, 403, 229, 901, 314, 538, 594, 124, 604, 556, 676, 936, 496, 147, 67, 259, 515, 69, 133, 517, 193, 385, 769, 26, 266, 522, 82, 274, 530, 578, 92, 44, 524, 100, 164, 548, 580, 644, 56, 536, 296, 552, 776, 112, 304, 208, 592, 400, 224, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_779, vertices_211, vertices_403, vertices_229, vertices_901, vertices_314, vertices_538, vertices_594, vertices_124, vertices_604, vertices_556, vertices_676, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_67, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_193, vertices_385, vertices_769, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_578, vertices_92, vertices_44, vertices_524, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_779), (false, vertices_211), (false, vertices_403), (false, vertices_229), (false, vertices_901), (true, vertices_26), (true, vertices_530), (true, vertices_92), (true, vertices_44), (true, vertices_524), (true, vertices_548), (true, vertices_56), (true, vertices_536), (true, vertices_296), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_592), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 14 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 18 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_211) then 19 else
  if p.val = (false, vertices_403) then 20 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_901) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_92) then 16 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 2 3 4 7 314 26 3
cert_row_4 2 2 4 6 7 8 936 296 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 314
cert_cover_5 0 1 0 2 3 4 26 314 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 4 92 124 3
cert_coverFacet 4 604
cert_cover_5 4 0 1 2 3 8 92 604 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 936
cert_cover_5 7 2 2 4 6 7 296 936 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0001

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e11q2_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 653, 181, 789, 841, 433, 118, 346, 618, 682, 306, 418, 596, 740, 848, 21, 133, 517, 137, 265, 521, 177, 273, 385, 769, 554, 74, 138, 266, 50, 82, 274, 98, 162, 290, 386, 52, 84, 532, 100, 164, 580, 644, 328, 584, 648, 304, 336, 592, 784, 608, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_653, vertices_181, vertices_789, vertices_841, vertices_433, vertices_118, vertices_346, vertices_618, vertices_682, vertices_306, vertices_418, vertices_596, vertices_740, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_177, vertices_273, vertices_385, vertices_769, vertices_554, vertices_74, vertices_138, vertices_266, vertices_50, vertices_82, vertices_274, vertices_98, vertices_162, vertices_290, vertices_386, vertices_52, vertices_84, vertices_532, vertices_100, vertices_164, vertices_580, vertices_644, vertices_328, vertices_584, vertices_648, vertices_304, vertices_336, vertices_592, vertices_784, vertices_608, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_653), (false, vertices_181), (false, vertices_789), (false, vertices_841), (false, vertices_433), (true, vertices_554), (true, vertices_74), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_84), (true, vertices_100), (true, vertices_580), (true, vertices_336), (true, vertices_592), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_181) then 23 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_554) then 16 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_554), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 74 2
cert_row_2 1 0 2 4 8 554
cert_row_4 2 0 1 3 4 5 118 50 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 50 118 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 74 346 2
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 5 554 618 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 554 682 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 100 740 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0002

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e11q2_0003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 563, 291, 451, 121, 721, 353, 398, 774, 802, 316, 604, 716, 820, 488, 35, 131, 259, 515, 49, 81, 529, 97, 289, 193, 321, 641, 134, 262, 518, 290, 546, 386, 770, 28, 588, 140, 268, 308, 532, 644, 772, 56, 88, 104, 296, 200, 392, 560, 592, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_563, vertices_291, vertices_451, vertices_121, vertices_721, vertices_353, vertices_398, vertices_774, vertices_802, vertices_316, vertices_604, vertices_716, vertices_820, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_97, vertices_289, vertices_193, vertices_321, vertices_641, vertices_134, vertices_262, vertices_518, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_588, vertices_140, vertices_268, vertices_308, vertices_532, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_296, vertices_200, vertices_392, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_563), (false, vertices_291), (false, vertices_451), (false, vertices_121), (false, vertices_721), (false, vertices_353), (true, vertices_262), (true, vertices_770), (true, vertices_28), (true, vertices_588), (true, vertices_140), (true, vertices_268), (true, vertices_308), (true, vertices_532), (true, vertices_772), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 20 17 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_588) then 19 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_308) then 21 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 1 2 6 7 398 134 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 3 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 134 398 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 316
cert_cover_5 3 1 1 2 3 4 28 316 3
cert_coverFacet 4 604
cert_cover_5 4 0 1 2 3 5 28 604 3
cert_coverFacet 5 716
cert_cover_5 5 0 1 2 5 6 588 716 3
cert_coverFacet 6 820
cert_cover_5 6 1 1 3 4 8 308 820 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0003

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e11q2_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 653, 409, 841, 689, 593, 174, 782, 118, 838, 426, 306, 740, 624, 432, 137, 265, 521, 81, 145, 273, 529, 321, 577, 641, 14, 38, 70, 774, 170, 266, 50, 82, 274, 290, 322, 140, 524, 100, 164, 580, 644, 392, 776, 112, 176, 304, 560, 592, 400, 608, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_653, vertices_409, vertices_841, vertices_689, vertices_593, vertices_174, vertices_782, vertices_118, vertices_838, vertices_426, vertices_306, vertices_740, vertices_624, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_641, vertices_14, vertices_38, vertices_70, vertices_774, vertices_170, vertices_266, vertices_50, vertices_82, vertices_274, vertices_290, vertices_322, vertices_140, vertices_524, vertices_100, vertices_164, vertices_580, vertices_644, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_608, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_653), (false, vertices_409), (false, vertices_841), (false, vertices_689), (false, vertices_593), (true, vertices_14), (true, vertices_38), (true, vertices_70), (true, vertices_774), (true, vertices_170), (true, vertices_266), (true, vertices_50), (true, vertices_290), (true, vertices_100), (true, vertices_164), (true, vertices_580), (true, vertices_112), (true, vertices_304), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_170) then 19 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 1 3 4 5 118 38 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 14 174 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 14 782 3
cert_coverFacet 2 118
cert_cover_5 2 2 0 1 3 4 38 118 2
cert_coverFacet 3 838
cert_cover_5 3 0 0 1 5 7 70 838 3
cert_coverFacet 4 426
cert_cover_5 4 1 0 2 4 7 170 426 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0004

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e11q2_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 397, 185, 537, 841, 593, 481, 782, 230, 550, 454, 562, 850, 668, 692, 25, 137, 265, 521, 49, 81, 529, 97, 161, 321, 577, 385, 38, 198, 262, 518, 50, 82, 530, 98, 546, 322, 770, 140, 268, 524, 660, 164, 548, 388, 152, 536, 776, 176, 560, 592, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_397, vertices_185, vertices_537, vertices_841, vertices_593, vertices_481, vertices_782, vertices_230, vertices_550, vertices_454, vertices_562, vertices_850, vertices_668, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_81, vertices_529, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_38, vertices_198, vertices_262, vertices_518, vertices_50, vertices_82, vertices_530, vertices_98, vertices_546, vertices_322, vertices_770, vertices_140, vertices_268, vertices_524, vertices_660, vertices_164, vertices_548, vertices_388, vertices_152, vertices_536, vertices_776, vertices_176, vertices_560, vertices_592, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_397), (false, vertices_185), (false, vertices_537), (false, vertices_841), (false, vertices_593), (false, vertices_481), (true, vertices_38), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_530), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_524), (true, vertices_660), (true, vertices_164), (true, vertices_548), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_198) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_660) then 18 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_2 2 0 1 5 6 198
cert_row_2 3 1 3 6 8 660
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 230
cert_cover_5 1 2 0 1 4 5 38 230 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 454
cert_cover_5 3 2 0 1 5 7 198 454 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 850
cert_cover_5 5 1 0 3 5 7 82 850 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 140 668 2
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 660 692 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0005

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e11q2_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 357, 713, 817, 465, 609, 30, 110, 790, 806, 154, 682, 412, 460, 616, 145, 273, 529, 97, 289, 545, 193, 321, 577, 641, 14, 22, 38, 774, 26, 42, 138, 146, 530, 546, 642, 28, 76, 396, 276, 100, 292, 324, 152, 104, 552, 200, 584, 648, 400, 784, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_357, vertices_713, vertices_817, vertices_465, vertices_609, vertices_30, vertices_110, vertices_790, vertices_806, vertices_154, vertices_682, vertices_412, vertices_460, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_22, vertices_38, vertices_774, vertices_26, vertices_42, vertices_138, vertices_146, vertices_530, vertices_546, vertices_642, vertices_28, vertices_76, vertices_396, vertices_276, vertices_100, vertices_292, vertices_324, vertices_152, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_400, vertices_784, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_357), (false, vertices_713), (false, vertices_817), (false, vertices_465), (false, vertices_609), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_774), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_546), (true, vertices_28), (true, vertices_76), (true, vertices_396), (true, vertices_276), (true, vertices_152), (true, vertices_104), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_396) then 19 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_552) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 5 110 14 3
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_2 2 0 1 7 8 774
cert_row_2 3 1 2 6 7 396
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 110
cert_cover_5 1 0 0 1 2 4 14 110 3
cert_coverFacet 2 790
cert_cover_5 2 2 0 1 3 7 22 790 3
cert_coverFacet 3 806
cert_cover_5 3 2 0 1 4 7 38 806 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 682
cert_cover_5 5 1 0 2 4 6 42 682 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 460
cert_cover_5 7 3 1 2 5 6 76 460 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0006

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3783 : Certifies 3783 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1227.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3784 : Certifies 3784 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1228.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3785 : Certifies 3785 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1229.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3786 : Certifies 3786 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1230.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3787 : Certifies 3787 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1231.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3788 : Certifies 3788 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1232.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3789 : Certifies 3789 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1233.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3790 : Certifies 3790 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1234.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3791 : Certifies 3791 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1235.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3792 : Certifies 3792 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1236.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3793 : Certifies 3793 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1238.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3794 : Certifies 3794 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1239.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3795 : Certifies 3795 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1240.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3796 : Certifies 3796 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1241.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3797 : Certifies 3797 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1243.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3798 : Certifies 3798 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1244.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3799 : Certifies 3799 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1245.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3800 : Certifies 3800 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1246.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3801 : Certifies 3801 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1249.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3802 : Certifies 3802 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1251.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3803 : Certifies 3803 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1252.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3804 : Certifies 3804 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1253.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3805 : Certifies 3805 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1254.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3806 : Certifies 3806 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3807 : Certifies 3807 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3808 : Certifies 3808 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3809 : Certifies 3809 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3810 : Certifies 3810 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3811 : Certifies 3811 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3812 : Certifies 3812 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B125 (j : Fin 30) :
    Certifies (3783 + j.val) := by
  fin_cases j
  · exact projection_3783
  · exact projection_3784
  · exact projection_3785
  · exact projection_3786
  · exact projection_3787
  · exact projection_3788
  · exact projection_3789
  · exact projection_3790
  · exact projection_3791
  · exact projection_3792
  · exact projection_3793
  · exact projection_3794
  · exact projection_3795
  · exact projection_3796
  · exact projection_3797
  · exact projection_3798
  · exact projection_3799
  · exact projection_3800
  · exact projection_3801
  · exact projection_3802
  · exact projection_3803
  · exact projection_3804
  · exact projection_3805
  · exact projection_3806
  · exact projection_3807
  · exact projection_3808
  · exact projection_3809
  · exact projection_3810
  · exact projection_3811
  · exact projection_3812

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
