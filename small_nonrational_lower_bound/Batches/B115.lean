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
/- Source: ProjectionCertificates/R_m15e10q1_0911.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0911

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 307, 611, 643, 229, 293, 713, 666, 562, 402, 412, 204, 844, 868, 824, 35, 131, 259, 515, 37, 133, 261, 97, 289, 193, 577, 641, 50, 146, 274, 530, 546, 386, 642, 76, 140, 268, 100, 292, 196, 836, 388, 152, 280, 536, 200, 584, 648, 776, 304, 560, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_307, vertices_611, vertices_643, vertices_229, vertices_293, vertices_713, vertices_666, vertices_562, vertices_402, vertices_412, vertices_204, vertices_844, vertices_868, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_37, vertices_133, vertices_261, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_100, vertices_292, vertices_196, vertices_836, vertices_388, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_648, vertices_776, vertices_304, vertices_560, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_307), (false, vertices_611), (false, vertices_643), (false, vertices_229), (false, vertices_293), (false, vertices_713), (true, vertices_146), (true, vertices_530), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_836), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_560), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_836) then 20 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 5 7 8 836
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 1 2 3 6 7 412 140 2
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 1 0 2 3 6 146 666 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 412
cert_cover_5 3 2 1 2 3 6 140 412 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 844
cert_cover_5 5 0 1 2 5 7 76 844 3
cert_coverFacet 6 868
cert_cover_5 6 0 1 4 5 7 100 868 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 280 824 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0911

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0912.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0912

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 57, 665, 241, 929, 110, 270, 598, 774, 482, 834, 124, 540, 976, 25, 41, 265, 521, 49, 145, 161, 289, 641, 769, 14, 70, 262, 518, 42, 266, 98, 290, 322, 578, 770, 28, 108, 268, 524, 84, 532, 772, 56, 536, 112, 208, 592, 656, 224, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_57, vertices_665, vertices_241, vertices_929, vertices_110, vertices_270, vertices_598, vertices_774, vertices_482, vertices_834, vertices_124, vertices_540, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_161, vertices_289, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_42, vertices_266, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_108, vertices_268, vertices_524, vertices_84, vertices_532, vertices_772, vertices_56, vertices_536, vertices_112, vertices_208, vertices_592, vertices_656, vertices_224, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_57), (false, vertices_665), (false, vertices_241), (false, vertices_929), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_28), (true, vertices_108), (true, vertices_84), (true, vertices_532), (true, vertices_592), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 57 1 14 70 262 518 98 322 578 770 28 84 532 592 448 832 299 781 108 665 241 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 70 598 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 98 482 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 124
cert_cover_5 6 0 1 2 3 4 28 124 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 976
cert_cover_5 8 3 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0912

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0913.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0913

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 233, 585, 721, 929, 110, 270, 118, 534, 774, 306, 914, 604, 496, 41, 73, 265, 521, 161, 289, 193, 577, 641, 769, 14, 22, 102, 262, 518, 42, 266, 50, 274, 530, 290, 770, 76, 268, 524, 84, 532, 772, 104, 584, 112, 304, 208, 592, 400, 656, 224, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_233, vertices_585, vertices_721, vertices_929, vertices_110, vertices_270, vertices_118, vertices_534, vertices_774, vertices_306, vertices_914, vertices_604, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_532, vertices_772, vertices_104, vertices_584, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_233), (false, vertices_585), (false, vertices_721), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 585 14 22 262 518 50 274 530 770 76 84 532 112 304 400 299 102 781 233 721 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 76 2
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 774
cert_cover_2 4 1 0 7 8 262 774 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 914
cert_cover_5 6 2 0 3 6 7 274 914 2
cert_coverFacet 7 604
cert_cover_5 7 0 1 2 3 5 76 604 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0913

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0914.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0914

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 779, 275, 675, 557, 77, 85, 345, 306, 418, 962, 844, 692, 724, 496, 19, 35, 259, 515, 13, 21, 37, 69, 73, 265, 521, 81, 273, 545, 50, 274, 162, 290, 386, 642, 770, 76, 524, 52, 84, 660, 548, 580, 328, 776, 176, 304, 208, 336, 416, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_779, vertices_275, vertices_675, vertices_557, vertices_77, vertices_85, vertices_345, vertices_306, vertices_418, vertices_962, vertices_844, vertices_692, vertices_724, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_13, vertices_21, vertices_37, vertices_69, vertices_73, vertices_265, vertices_521, vertices_81, vertices_273, vertices_545, vertices_50, vertices_274, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_52, vertices_84, vertices_660, vertices_548, vertices_580, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_416, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_779), (false, vertices_275), (false, vertices_675), (false, vertices_557), (false, vertices_77), (false, vertices_85), (false, vertices_345), (true, vertices_290), (true, vertices_386), (true, vertices_660), (true, vertices_580), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_77) then 1 else
  if p.val = (false, vertices_85) then 2 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_660) then 19 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
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
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_2 2 1 3 6 8 660
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 306
cert_cover_2 0 3 0 4 7 50 306 3
cert_coverFacet 1 418
cert_cover_2 1 4 0 6 7 162 418 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 386 962 1
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 76 844 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 84 724 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 176 496 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0914

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0915.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0915

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 301, 677, 409, 617, 649, 662, 838, 602, 370, 402, 868, 120, 312, 664, 37, 133, 261, 41, 137, 265, 521, 545, 385, 641, 134, 262, 518, 82, 146, 274, 530, 322, 578, 386, 292, 548, 836, 644, 56, 88, 152, 280, 536, 104, 296, 584, 648, 112, 304, 400, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_301, vertices_677, vertices_409, vertices_617, vertices_649, vertices_662, vertices_838, vertices_602, vertices_370, vertices_402, vertices_868, vertices_120, vertices_312, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_41, vertices_137, vertices_265, vertices_521, vertices_545, vertices_385, vertices_641, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_386, vertices_292, vertices_548, vertices_836, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_296, vertices_584, vertices_648, vertices_112, vertices_304, vertices_400, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_301), (false, vertices_677), (false, vertices_409), (false, vertices_617), (false, vertices_649), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_836), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_112), (true, vertices_304), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_836) then 20 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_2 1 1 5 7 8 836
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 0 3 4 5 7 370 82 2
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 262 838 2
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 82 602 1
cert_coverFacet 3 370
cert_cover_5 3 3 0 3 4 5 82 370 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 868
cert_cover_5 5 1 1 4 5 7 292 868 2
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0915

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0917.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0917

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 557, 397, 789, 361, 849, 406, 682, 370, 210, 418, 706, 652, 724, 424, 13, 261, 517, 41, 265, 785, 97, 545, 321, 577, 82, 146, 274, 98, 162, 290, 546, 194, 578, 386, 642, 140, 524, 148, 276, 532, 388, 644, 168, 296, 552, 392, 648, 208, 336, 592, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_557, vertices_397, vertices_789, vertices_361, vertices_849, vertices_406, vertices_682, vertices_370, vertices_210, vertices_418, vertices_706, vertices_652, vertices_724, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_41, vertices_265, vertices_785, vertices_97, vertices_545, vertices_321, vertices_577, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_557), (false, vertices_397), (false, vertices_789), (false, vertices_361), (false, vertices_849), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_644), (true, vertices_168), (true, vertices_648), (true, vertices_208), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_789) then 23 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_4 1 0 3 4 5 7 370 82 2
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 162 682 1
cert_coverFacet 2 370
cert_cover_5 2 1 0 3 4 5 82 370 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 724
cert_cover_5 7 3 1 3 5 6 148 724 2
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0917

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0918.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0918

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 173, 805, 793, 617, 393, 790, 710, 602, 242, 402, 740, 120, 184, 408, 37, 133, 261, 41, 137, 265, 521, 545, 385, 769, 134, 262, 518, 82, 146, 274, 530, 194, 578, 386, 164, 548, 708, 772, 56, 88, 152, 280, 536, 104, 168, 584, 392, 112, 176, 400, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_173, vertices_805, vertices_793, vertices_617, vertices_393, vertices_790, vertices_710, vertices_602, vertices_242, vertices_402, vertices_740, vertices_120, vertices_184, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_41, vertices_137, vertices_265, vertices_521, vertices_545, vertices_385, vertices_769, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_164, vertices_548, vertices_708, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_584, vertices_392, vertices_112, vertices_176, vertices_400, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_173), (false, vertices_805), (false, vertices_793), (false, vertices_617), (false, vertices_393), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_708), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_112), (true, vertices_176), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_708) then 20 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_708), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 262 2
cert_row_2 1 1 5 6 8 708
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 0 3 4 5 6 242 82 2
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 262 790 2
cert_coverFacet 1 710
cert_cover_5 1 1 0 1 5 6 134 710 2
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 82 602 1
cert_coverFacet 3 242
cert_cover_5 3 3 0 3 4 5 82 242 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 164 740 2
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0918

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0919.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0919

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 173, 589, 453, 569, 929, 214, 598, 410, 818, 450, 156, 540, 312, 424, 13, 69, 133, 41, 521, 161, 545, 321, 577, 385, 769, 86, 146, 274, 530, 194, 322, 578, 386, 770, 28, 140, 524, 148, 532, 196, 580, 56, 152, 280, 536, 168, 296, 392, 304, 560, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_173, vertices_589, vertices_453, vertices_569, vertices_929, vertices_214, vertices_598, vertices_410, vertices_818, vertices_450, vertices_156, vertices_540, vertices_312, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_41, vertices_521, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_86, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_140, vertices_524, vertices_148, vertices_532, vertices_196, vertices_580, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_304, vertices_560, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_173), (false, vertices_589), (false, vertices_453), (false, vertices_569), (false, vertices_929), (true, vertices_86), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_28), (true, vertices_148), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 3 6 7 410 146 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_rows_3
cert_pivot_3 2 1 0
cert_heightProof 3
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 146 410 1
cert_coverFacet 3 818
cert_cover_5 3 2 0 3 4 7 274 818 2
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0919

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0920.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0920

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 659, 195, 557, 565, 233, 433, 902, 482, 834, 316, 844, 404, 660, 360, 67, 131, 515, 549, 41, 73, 521, 49, 145, 529, 161, 193, 194, 322, 578, 386, 642, 770, 44, 268, 524, 52, 148, 276, 532, 388, 644, 772, 104, 296, 328, 584, 304, 400, 656, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_659, vertices_195, vertices_557, vertices_565, vertices_233, vertices_433, vertices_902, vertices_482, vertices_834, vertices_316, vertices_844, vertices_404, vertices_660, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_549, vertices_41, vertices_73, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_193, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_328, vertices_584, vertices_304, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_659), (false, vertices_195), (false, vertices_557), (false, vertices_565), (false, vertices_233), (false, vertices_433), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 7 316 44 2
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 482
cert_cover_5 1 1 0 4 5 6 194 482 1
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 316
cert_cover_5 3 0 1 2 3 4 44 316 2
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 268 844 2
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0920

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0921.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0921

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 451, 579, 597, 345, 153, 425, 614, 682, 226, 316, 572, 340, 484, 664, 67, 131, 515, 25, 137, 265, 81, 145, 529, 321, 577, 385, 98, 162, 546, 194, 578, 642, 60, 84, 276, 532, 100, 292, 548, 324, 580, 152, 280, 536, 168, 296, 552, 648, 336, 656, 224, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_451, vertices_579, vertices_597, vertices_345, vertices_153, vertices_425, vertices_614, vertices_682, vertices_226, vertices_316, vertices_572, vertices_340, vertices_484, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_25, vertices_137, vertices_265, vertices_81, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_60, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_336, vertices_656, vertices_224, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_451), (false, vertices_579), (false, vertices_597), (false, vertices_345), (false, vertices_153), (false, vertices_425), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_60), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_536), (true, vertices_552), (true, vertices_648), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 162 682 1
cert_coverFacet 2 226
cert_cover_2 2 4 0 5 6 98 226 3
cert_coverFacet 3 316
cert_cover_5 3 0 1 2 3 7 60 316 3
cert_coverFacet 4 572
cert_cover_5 4 0 1 2 3 8 60 572 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0921

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0922.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0922

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 451, 643, 653, 217, 281, 369, 678, 818, 418, 620, 204, 484, 632, 792, 131, 259, 515, 25, 137, 265, 521, 81, 273, 193, 321, 641, 162, 290, 546, 386, 642, 770, 76, 140, 524, 100, 164, 548, 196, 644, 88, 280, 536, 616, 200, 776, 112, 304, 560, 784, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_451, vertices_643, vertices_653, vertices_217, vertices_281, vertices_369, vertices_678, vertices_818, vertices_418, vertices_620, vertices_204, vertices_484, vertices_632, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_321, vertices_641, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_88, vertices_280, vertices_536, vertices_616, vertices_200, vertices_776, vertices_112, vertices_304, vertices_560, vertices_784, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_451), (false, vertices_643), (false, vertices_653), (false, vertices_217), (false, vertices_281), (false, vertices_369), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_76), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_536), (true, vertices_616), (true, vertices_560), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_616) then 21 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_616), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 5 8 616
cert_row_4 1 0 3 4 7 8 818 290 1
cert_row_4 2 0 1 4 6 8 678 162 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 162 678 1
cert_coverFacet 1 818
cert_cover_5 1 1 0 3 4 7 290 818 1
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 620
cert_cover_5 3 0 1 2 4 5 76 620 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 100 484 3
cert_coverFacet 6 632
cert_cover_5 6 0 2 3 4 5 88 632 2
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0922

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0923.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0923

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 301, 781, 101, 709, 121, 665, 838, 906, 434, 338, 706, 372, 184, 424, 269, 37, 69, 517, 25, 41, 521, 81, 145, 97, 193, 641, 82, 146, 274, 194, 322, 578, 386, 642, 770, 100, 292, 324, 580, 772, 56, 152, 168, 296, 392, 648, 776, 112, 176, 304, 336, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_301, vertices_781, vertices_101, vertices_709, vertices_121, vertices_665, vertices_838, vertices_906, vertices_434, vertices_338, vertices_706, vertices_372, vertices_184, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_69, vertices_517, vertices_25, vertices_41, vertices_521, vertices_81, vertices_145, vertices_97, vertices_193, vertices_641, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_301), (false, vertices_781), (false, vertices_101), (false, vertices_709), (false, vertices_121), (false, vertices_665), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_324), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 386 1
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 386 906 1
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 146 434 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 100 372 1
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0923

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0924.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0924

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 453, 793, 433, 737, 833, 94, 54, 678, 710, 538, 842, 316, 332, 420, 49, 273, 529, 161, 545, 193, 321, 577, 385, 769, 22, 38, 70, 646, 26, 74, 522, 50, 530, 546, 578, 28, 76, 268, 52, 164, 292, 196, 324, 388, 280, 536, 328, 776, 304, 416, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_453, vertices_793, vertices_433, vertices_737, vertices_833, vertices_94, vertices_54, vertices_678, vertices_710, vertices_538, vertices_842, vertices_316, vertices_332, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_38, vertices_70, vertices_646, vertices_26, vertices_74, vertices_522, vertices_50, vertices_530, vertices_546, vertices_578, vertices_28, vertices_76, vertices_268, vertices_52, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_280, vertices_536, vertices_328, vertices_776, vertices_304, vertices_416, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_453), (false, vertices_793), (false, vertices_433), (false, vertices_737), (false, vertices_833), (true, vertices_22), (true, vertices_38), (true, vertices_70), (true, vertices_646), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_164), (true, vertices_292), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_646) then 17 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 833 22 38 70 26 74 522 578 28 76 268 52 164 292 328 563 646 453 793 433 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 0 1 2 3 5 94 22 2
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 3 22 94 2
cert_coverFacet 1 54
cert_cover_2 1 1 0 3 4 22 54 3
cert_coverFacet 2 678
cert_cover_5 2 0 0 1 4 6 38 678 3
cert_coverFacet 3 710
cert_cover_5 3 0 0 1 5 6 70 710 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 842
cert_cover_5 5 1 0 2 5 7 74 842 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 28 316 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0924

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0925.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0925

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 339, 579, 117, 817, 737, 398, 682, 450, 706, 572, 796, 236, 340, 452, 67, 259, 515, 49, 81, 273, 97, 545, 577, 769, 138, 266, 522, 194, 322, 578, 386, 642, 540, 44, 140, 268, 52, 84, 276, 100, 196, 324, 388, 168, 552, 776, 560, 336, 784, 224, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_339, vertices_579, vertices_117, vertices_817, vertices_737, vertices_398, vertices_682, vertices_450, vertices_706, vertices_572, vertices_796, vertices_236, vertices_340, vertices_452] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_49, vertices_81, vertices_273, vertices_97, vertices_545, vertices_577, vertices_769, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_540, vertices_44, vertices_140, vertices_268, vertices_52, vertices_84, vertices_276, vertices_100, vertices_196, vertices_324, vertices_388, vertices_168, vertices_552, vertices_776, vertices_560, vertices_336, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_339), (false, vertices_579), (false, vertices_117), (false, vertices_817), (false, vertices_737), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_540), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_168), (true, vertices_552), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_540) then 20 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 8 540
cert_row_4 1 0 1 2 6 7 398 138 1
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 138 398 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 138 682 2
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 572
cert_cover_5 4 0 1 2 3 4 540 572 3
cert_coverFacet 5 796
cert_cover_5 5 0 1 2 3 7 540 796 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 44 236 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 452
cert_cover_2 8 5 1 6 7 196 452 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0925

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0926.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0926

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 661, 453, 361, 713, 777, 542, 182, 422, 122, 298, 778, 600, 496, 720, 133, 261, 517, 73, 265, 521, 193, 321, 641, 769, 22, 166, 262, 518, 26, 42, 266, 522, 50, 290, 770, 148, 532, 388, 88, 536, 104, 296, 584, 776, 112, 176, 208, 592, 656, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_661, vertices_453, vertices_361, vertices_713, vertices_777, vertices_542, vertices_182, vertices_422, vertices_122, vertices_298, vertices_778, vertices_600, vertices_496, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_166, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_290, vertices_770, vertices_148, vertices_532, vertices_388, vertices_88, vertices_536, vertices_104, vertices_296, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_661), (false, vertices_453), (false, vertices_361), (false, vertices_713), (false, vertices_777), (true, vertices_22), (true, vertices_166), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_88), (true, vertices_536), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_166) then 17 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_2 1 0 1 4 6 166
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 4 22 182 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 7 166 422 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 26 122 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0926

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0927.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0927

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 357, 773, 457, 913, 737, 30, 46, 662, 410, 618, 714, 316, 788, 360, 37, 261, 517, 97, 545, 193, 321, 385, 641, 769, 14, 22, 38, 518, 26, 42, 586, 138, 146, 546, 642, 28, 44, 276, 532, 292, 772, 280, 104, 296, 200, 328, 392, 400, 656, 784, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_357, vertices_773, vertices_457, vertices_913, vertices_737, vertices_30, vertices_46, vertices_662, vertices_410, vertices_618, vertices_714, vertices_316, vertices_788, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_42, vertices_586, vertices_138, vertices_146, vertices_546, vertices_642, vertices_28, vertices_44, vertices_276, vertices_532, vertices_292, vertices_772, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_357), (false, vertices_773), (false, vertices_457), (false, vertices_913), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_26), (true, vertices_42), (true, vertices_586), (true, vertices_138), (true, vertices_146), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_276), (true, vertices_532), (true, vertices_280), (true, vertices_104), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_586) then 17 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 773 14 22 26 42 138 146 642 28 44 276 532 280 104 296 551 586 357 457 913 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 8 586
cert_row_4 1 0 1 3 6 8 662 22 3
cert_row_4 2 0 2 3 6 7 410 26 3
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 662
cert_cover_5 2 1 0 1 3 6 22 662 3
cert_coverFacet 3 410
cert_cover_5 3 2 0 2 3 6 26 410 3
cert_coverFacet 4 618
cert_cover_5 4 0 0 2 4 5 42 618 3
cert_coverFacet 5 714
cert_cover_5 5 0 0 2 5 6 586 714 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 28 316 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0927

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0928.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0928

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 519, 395, 803, 589, 217, 961, 286, 310, 614, 92, 244, 440, 736, 928, 7, 11, 259, 515, 13, 517, 73, 137, 193, 577, 385, 769, 14, 278, 38, 518, 266, 290, 546, 28, 76, 52, 84, 100, 580, 88, 152, 280, 392, 176, 304, 208, 224, 608, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_519, vertices_395, vertices_803, vertices_589, vertices_217, vertices_961, vertices_286, vertices_310, vertices_614, vertices_92, vertices_244, vertices_440, vertices_736, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_13, vertices_517, vertices_73, vertices_137, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_278, vertices_38, vertices_518, vertices_266, vertices_290, vertices_546, vertices_28, vertices_76, vertices_52, vertices_84, vertices_100, vertices_580, vertices_88, vertices_152, vertices_280, vertices_392, vertices_176, vertices_304, vertices_208, vertices_224, vertices_608, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_519), (false, vertices_395), (false, vertices_803), (false, vertices_589), (false, vertices_217), (false, vertices_961), (true, vertices_278), (true, vertices_38), (true, vertices_28), (true, vertices_52), (true, vertices_84), (true, vertices_100), (true, vertices_280), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_608), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_519) then 1 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_278) then 16 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_278), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 0 1 4 5 8 614 38 3
cert_row_2 1 0 1 3 7 278
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 310
cert_cover_5 1 1 0 1 3 4 278 310 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 38 614 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 152 440 2
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0928

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0929.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0929

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 453, 841, 433, 785, 737, 94, 54, 678, 710, 794, 586, 316, 332, 420, 49, 273, 529, 161, 545, 193, 321, 577, 385, 769, 22, 38, 70, 646, 26, 74, 522, 50, 530, 546, 578, 28, 76, 268, 52, 164, 292, 196, 324, 388, 280, 328, 584, 776, 304, 784, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_453, vertices_841, vertices_433, vertices_785, vertices_737, vertices_94, vertices_54, vertices_678, vertices_710, vertices_794, vertices_586, vertices_316, vertices_332, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_38, vertices_70, vertices_646, vertices_26, vertices_74, vertices_522, vertices_50, vertices_530, vertices_546, vertices_578, vertices_28, vertices_76, vertices_268, vertices_52, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_280, vertices_328, vertices_584, vertices_776, vertices_304, vertices_784, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_453), (false, vertices_841), (false, vertices_433), (false, vertices_785), (false, vertices_737), (true, vertices_22), (true, vertices_38), (true, vertices_70), (true, vertices_646), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_164), (true, vertices_292), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_646) then 17 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_280) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 785 22 38 70 26 74 522 578 28 76 268 52 164 292 280 563 646 453 841 433 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 1 2 3 5 94 22 2
cert_row_4 2 0 2 3 7 8 794 26 3
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 22 94 2
cert_coverFacet 1 54
cert_cover_2 1 1 0 3 4 22 54 3
cert_coverFacet 2 678
cert_cover_5 2 0 0 1 4 6 38 678 3
cert_coverFacet 3 710
cert_cover_5 3 0 0 1 5 6 70 710 3
cert_coverFacet 4 794
cert_cover_5 4 2 0 2 3 7 26 794 3
cert_coverFacet 5 586
cert_cover_2 5 2 0 5 8 74 586 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 28 316 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0929

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0930.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0930

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 181, 357, 773, 313, 153, 838, 218, 346, 650, 738, 612, 676, 496, 37, 133, 261, 517, 25, 137, 265, 521, 49, 145, 289, 769, 90, 138, 266, 522, 194, 322, 578, 642, 770, 100, 164, 548, 324, 580, 644, 772, 152, 280, 648, 176, 304, 208, 336, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_181, vertices_357, vertices_773, vertices_313, vertices_153, vertices_838, vertices_218, vertices_346, vertices_650, vertices_738, vertices_612, vertices_676, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_181), (false, vertices_357), (false, vertices_773), (false, vertices_313), (false, vertices_153), (true, vertices_90), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_548), (true, vertices_580), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 773 1 153 138 194 322 578 642 548 580 208 336 224 608 672 779 90 653 181 357 313
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0930

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0931.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0931

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 333, 525, 565, 405, 713, 657, 782, 806, 618, 330, 434, 226, 308, 752, 13, 21, 261, 517, 73, 521, 145, 529, 193, 321, 385, 641, 774, 74, 266, 522, 98, 162, 290, 546, 194, 322, 386, 268, 524, 52, 276, 292, 548, 328, 584, 176, 304, 560, 400, 656, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_333, vertices_525, vertices_565, vertices_405, vertices_713, vertices_657, vertices_782, vertices_806, vertices_618, vertices_330, vertices_434, vertices_226, vertices_308, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_73, vertices_521, vertices_145, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_774, vertices_74, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_333), (false, vertices_525), (false, vertices_565), (false, vertices_405), (false, vertices_713), (false, vertices_657), (true, vertices_774), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_292), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 525 1 657 74 266 522 98 162 290 546 292 176 304 224 608 451 774 333 565 405 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 774 782 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 774 806 2
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 5 74 618 2
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 162 434 1
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 176 752 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0931

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0932.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0932

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 333, 525, 309, 661, 713, 401, 782, 806, 618, 330, 434, 226, 564, 752, 13, 21, 261, 517, 73, 521, 145, 273, 193, 321, 385, 641, 774, 74, 266, 522, 98, 162, 290, 546, 194, 322, 386, 268, 524, 52, 532, 292, 548, 328, 584, 176, 304, 560, 400, 656, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_333, vertices_525, vertices_309, vertices_661, vertices_713, vertices_401, vertices_782, vertices_806, vertices_618, vertices_330, vertices_434, vertices_226, vertices_564, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_73, vertices_521, vertices_145, vertices_273, vertices_193, vertices_321, vertices_385, vertices_641, vertices_774, vertices_74, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_268, vertices_524, vertices_52, vertices_532, vertices_292, vertices_548, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_333), (false, vertices_525), (false, vertices_309), (false, vertices_661), (false, vertices_713), (false, vertices_401), (true, vertices_774), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_548), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 525 1 401 74 266 522 98 162 290 546 548 176 560 224 608 451 774 333 309 661 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 774 782 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 774 806 2
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 5 74 618 2
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 162 434 1
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 176 752 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0932

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0933.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0933

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 171, 211, 275, 45, 341, 677, 709, 394, 914, 364, 612, 936, 880, 720, 11, 19, 131, 259, 13, 37, 69, 645, 261, 41, 81, 273, 161, 193, 138, 266, 146, 274, 386, 44, 268, 100, 548, 324, 580, 168, 296, 392, 208, 336, 592, 656, 784, 352, 608, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_171, vertices_211, vertices_275, vertices_45, vertices_341, vertices_677, vertices_709, vertices_394, vertices_914, vertices_364, vertices_612, vertices_936, vertices_880, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_131, vertices_259, vertices_13, vertices_37, vertices_69, vertices_645, vertices_261, vertices_41, vertices_81, vertices_273, vertices_161, vertices_193, vertices_138, vertices_266, vertices_146, vertices_274, vertices_386, vertices_44, vertices_268, vertices_100, vertices_548, vertices_324, vertices_580, vertices_168, vertices_296, vertices_392, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_352, vertices_608, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_171), (false, vertices_211), (false, vertices_275), (false, vertices_45), (false, vertices_341), (false, vertices_677), (false, vertices_709), (true, vertices_386), (true, vertices_100), (true, vertices_296), (true, vertices_392), (true, vertices_592), (true, vertices_656), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 14 else
  if p.val = (false, vertices_171) then 15 else
  if p.val = (false, vertices_211) then 16 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_row_4 0 0 3 6 7 8 914 146 3
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_4 2 2 4 6 7 8 936 168 3
cert_row_4 3 3 4 5 7 8 880 336 1
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 394
cert_cover_2 0 2 0 6 7 138 394 3
cert_coverFacet 1 914
cert_cover_5 1 0 0 3 6 7 146 914 3
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 5 44 364 3
cert_coverFacet 3 612
cert_cover_2 3 4 1 5 8 100 612 3
cert_coverFacet 4 936
cert_cover_5 4 2 2 4 6 7 168 936 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 336 880 1
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0933

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0934.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0934

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 309, 149, 569, 361, 657, 214, 342, 774, 842, 738, 616, 496, 688, 21, 133, 261, 517, 41, 265, 521, 49, 145, 529, 289, 641, 86, 134, 262, 518, 194, 322, 578, 642, 770, 148, 276, 772, 104, 552, 328, 584, 776, 176, 304, 560, 208, 336, 656, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_309, vertices_149, vertices_569, vertices_361, vertices_657, vertices_214, vertices_342, vertices_774, vertices_842, vertices_738, vertices_616, vertices_496, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_289, vertices_641, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_148, vertices_276, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_309), (false, vertices_149), (false, vertices_569), (false, vertices_361), (false, vertices_657), (true, vertices_86), (true, vertices_262), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_584), (true, vertices_176), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_86) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 149 1 657 262 194 322 578 770 584 176 208 336 224 608 672 647 86 781 309 569 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 322 842 1
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 176 496 2
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0934

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0935.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0935

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 595, 771, 397, 713, 929, 566, 434, 338, 802, 348, 604, 684, 180, 404, 67, 259, 515, 73, 137, 265, 577, 385, 641, 769, 50, 82, 274, 530, 290, 546, 322, 770, 92, 140, 268, 524, 52, 148, 276, 532, 164, 548, 388, 328, 584, 648, 176, 336, 592, 400, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_595, vertices_771, vertices_397, vertices_713, vertices_929, vertices_566, vertices_434, vertices_338, vertices_802, vertices_348, vertices_604, vertices_684, vertices_180, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_577, vertices_385, vertices_641, vertices_769, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_770, vertices_92, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_388, vertices_328, vertices_584, vertices_648, vertices_176, vertices_336, vertices_592, vertices_400, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_595), (false, vertices_771), (false, vertices_397), (false, vertices_713), (false, vertices_929), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_92), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_176), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_92) then 20 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 3 4 6 7 434 50 3
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 434
cert_cover_5 1 1 0 3 4 6 50 434 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 348
cert_cover_5 4 0 1 2 3 7 92 348 3
cert_coverFacet 5 604
cert_cover_5 5 0 1 2 3 8 92 604 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0935

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0936.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0936

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 357, 409, 625, 337, 929, 302, 654, 342, 598, 154, 282, 620, 424, 680, 81, 145, 273, 529, 97, 289, 545, 321, 385, 641, 14, 86, 262, 518, 26, 138, 266, 146, 274, 530, 642, 44, 524, 100, 292, 324, 580, 152, 280, 168, 296, 552, 392, 648, 336, 592, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_357, vertices_409, vertices_625, vertices_337, vertices_929, vertices_302, vertices_654, vertices_342, vertices_598, vertices_154, vertices_282, vertices_620, vertices_424, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_14, vertices_86, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_44, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_336, vertices_592, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_357), (false, vertices_409), (false, vertices_625), (false, vertices_337), (false, vertices_929), (true, vertices_14), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_44), (true, vertices_524), (true, vertices_580), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 337 14 262 518 26 138 266 274 44 524 580 168 296 552 648 659 86 357 409 625 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 2 4 7 302 14 3
cert_row_4 2 0 1 2 6 8 654 14 3
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 14 302 3
cert_coverFacet 1 654
cert_cover_5 1 2 0 1 2 6 14 654 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 7 86 342 3
cert_coverFacet 3 598
cert_cover_5 3 0 0 1 3 8 86 598 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 282
cert_cover_2 5 2 0 3 7 26 282 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0936

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0937.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0937

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 77, 837, 217, 537, 913, 174, 206, 550, 582, 434, 866, 184, 824, 13, 69, 517, 25, 73, 521, 145, 529, 193, 321, 385, 769, 142, 38, 70, 518, 162, 290, 546, 194, 322, 578, 386, 44, 76, 548, 580, 56, 152, 536, 168, 552, 200, 176, 304, 400, 784, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_77, vertices_837, vertices_217, vertices_537, vertices_913, vertices_174, vertices_206, vertices_550, vertices_582, vertices_434, vertices_866, vertices_184, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_73, vertices_521, vertices_145, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_142, vertices_38, vertices_70, vertices_518, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_44, vertices_76, vertices_548, vertices_580, vertices_56, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_176, vertices_304, vertices_400, vertices_784, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_77), (false, vertices_837), (false, vertices_217), (false, vertices_537), (false, vertices_913), (true, vertices_142), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_56), (true, vertices_168), (true, vertices_176), (true, vertices_304), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 77 1 537 38 70 518 162 290 546 578 56 168 176 304 800 451 142 557 837 217 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 4 6 7 434 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 142 174 3
cert_coverFacet 1 206
cert_cover_5 1 0 0 1 2 5 142 206 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 434
cert_cover_5 4 1 0 3 4 6 162 434 1
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 290 866 2
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0937

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0938.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0938

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 675, 771, 333, 233, 625, 833, 406, 662, 850, 108, 684, 396, 372, 564, 131, 259, 515, 73, 137, 265, 97, 161, 545, 321, 577, 769, 150, 274, 530, 386, 642, 770, 44, 76, 140, 268, 52, 276, 532, 100, 548, 324, 388, 644, 104, 168, 392, 112, 560, 336, 592, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_675, vertices_771, vertices_333, vertices_233, vertices_625, vertices_833, vertices_406, vertices_662, vertices_850, vertices_108, vertices_684, vertices_396, vertices_372, vertices_564] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_769, vertices_150, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_268, vertices_52, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_388, vertices_644, vertices_104, vertices_168, vertices_392, vertices_112, vertices_560, vertices_336, vertices_592, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_675), (false, vertices_771), (false, vertices_333), (false, vertices_233), (false, vertices_625), (false, vertices_833), (true, vertices_150), (true, vertices_274), (true, vertices_530), (true, vertices_44), (true, vertices_140), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_333) then 15 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_150) then 16 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 1 771 0 833 274 530 44 140 52 276 532 100 548 388 644 336 333 150 395 675 233 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 6 8 684 44 3
cert_row_2 1 0 1 3 6 150
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 7 150 406 3
cert_coverFacet 1 662
cert_cover_5 1 1 0 1 3 8 150 662 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 274 850 2
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 684
cert_cover_5 4 0 1 2 4 6 44 684 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 52 372 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0938

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0939.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0939

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 229, 569, 169, 457, 865, 62, 174, 278, 390, 538, 394, 850, 628, 468, 41, 137, 265, 521, 97, 161, 545, 193, 321, 769, 46, 22, 134, 262, 26, 138, 266, 522, 274, 530, 386, 770, 52, 84, 276, 100, 164, 196, 388, 56, 536, 168, 392, 560, 336, 592, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_229, vertices_569, vertices_169, vertices_457, vertices_865, vertices_62, vertices_174, vertices_278, vertices_390, vertices_538, vertices_394, vertices_850, vertices_628, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_769, vertices_46, vertices_22, vertices_134, vertices_262, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_770, vertices_52, vertices_84, vertices_276, vertices_100, vertices_164, vertices_196, vertices_388, vertices_56, vertices_536, vertices_168, vertices_392, vertices_560, vertices_336, vertices_592, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_229), (false, vertices_569), (false, vertices_169), (false, vertices_457), (false, vertices_865), (true, vertices_46), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_388), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 169 22 134 262 26 138 274 530 386 52 84 276 388 336 592 779 46 229 569 457 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 5 7 8 850 274 2
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 0 4 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 46 62 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 6 46 174 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 850
cert_cover_5 6 1 0 3 5 7 274 850 2
cert_coverFacet 7 628
cert_cover_5 7 2 1 3 4 5 52 628 3
cert_coverFacet 8 468
cert_cover_5 8 3 1 3 5 6 84 468 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0939

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0940.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0940

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 285, 569, 457, 585, 369, 206, 590, 662, 482, 674, 540, 396, 436, 688, 25, 73, 265, 521, 49, 273, 97, 545, 321, 577, 78, 134, 518, 98, 162, 546, 194, 578, 642, 28, 140, 268, 524, 148, 276, 532, 388, 536, 200, 584, 392, 176, 304, 560, 656, 352, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_285, vertices_569, vertices_457, vertices_585, vertices_369, vertices_206, vertices_590, vertices_662, vertices_482, vertices_674, vertices_540, vertices_396, vertices_436, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_49, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_78, vertices_134, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_536, vertices_200, vertices_584, vertices_392, vertices_176, vertices_304, vertices_560, vertices_656, vertices_352, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_285), (false, vertices_569), (false, vertices_457), (false, vertices_585), (false, vertices_369), (true, vertices_78), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_388), (true, vertices_176), (true, vertices_656), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 585 134 518 162 194 642 140 524 148 532 388 176 656 416 672 611 78 285 569 457 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 662
cert_cover_5 2 1 0 1 3 6 134 662 2
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 98 482 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 148 436 2
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0940

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0941.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0941

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 653, 269, 341, 613, 361, 169, 598, 666, 466, 482, 610, 284, 540, 440, 13, 69, 261, 517, 41, 137, 265, 97, 161, 545, 321, 641, 82, 146, 530, 98, 162, 546, 450, 578, 642, 28, 268, 524, 84, 276, 532, 580, 152, 280, 536, 168, 296, 648, 336, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_653, vertices_269, vertices_341, vertices_613, vertices_361, vertices_169, vertices_598, vertices_666, vertices_466, vertices_482, vertices_610, vertices_284, vertices_540, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_450, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_648, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_653), (false, vertices_269), (false, vertices_341), (false, vertices_613), (false, vertices_361), (false, vertices_169), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_450), (true, vertices_578), (true, vertices_28), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_450) then 16 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 269 1 169 82 146 530 98 578 28 532 152 280 536 400 416 675 450 653 341 613 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 146 666 1
cert_coverFacet 2 466
cert_cover_5 2 1 0 3 5 6 82 466 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 152 440 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0941

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3483 : Certifies 3483 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0911.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3484 : Certifies 3484 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0912.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3485 : Certifies 3485 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0913.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3486 : Certifies 3486 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0914.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3487 : Certifies 3487 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0915.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3488 : Certifies 3488 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0917.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3489 : Certifies 3489 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0918.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3490 : Certifies 3490 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0919.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3491 : Certifies 3491 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0920.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3492 : Certifies 3492 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0921.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3493 : Certifies 3493 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0922.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3494 : Certifies 3494 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0923.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3495 : Certifies 3495 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0924.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3496 : Certifies 3496 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0925.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3497 : Certifies 3497 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0926.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3498 : Certifies 3498 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0927.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3499 : Certifies 3499 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0928.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3500 : Certifies 3500 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0929.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3501 : Certifies 3501 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0930.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3502 : Certifies 3502 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0931.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3503 : Certifies 3503 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0932.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3504 : Certifies 3504 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0933.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3505 : Certifies 3505 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0934.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3506 : Certifies 3506 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0935.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3507 : Certifies 3507 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0936.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3508 : Certifies 3508 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0937.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3509 : Certifies 3509 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0938.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3510 : Certifies 3510 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0939.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3511 : Certifies 3511 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0940.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3512 : Certifies 3512 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0941.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B115 (j : Fin 30) :
    Certifies (3483 + j.val) := by
  fin_cases j
  · exact projection_3483
  · exact projection_3484
  · exact projection_3485
  · exact projection_3486
  · exact projection_3487
  · exact projection_3488
  · exact projection_3489
  · exact projection_3490
  · exact projection_3491
  · exact projection_3492
  · exact projection_3493
  · exact projection_3494
  · exact projection_3495
  · exact projection_3496
  · exact projection_3497
  · exact projection_3498
  · exact projection_3499
  · exact projection_3500
  · exact projection_3501
  · exact projection_3502
  · exact projection_3503
  · exact projection_3504
  · exact projection_3505
  · exact projection_3506
  · exact projection_3507
  · exact projection_3508
  · exact projection_3509
  · exact projection_3510
  · exact projection_3511
  · exact projection_3512

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
