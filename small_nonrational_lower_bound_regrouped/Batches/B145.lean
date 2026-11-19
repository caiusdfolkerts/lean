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
/- Source: ProjectionCertificates/R_m16e10q1_0498.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0498

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 779, 611, 181, 805, 197, 225, 666, 202, 330, 706, 412, 460, 308, 824, 752, 67, 259, 515, 37, 69, 133, 261, 97, 161, 545, 193, 769, 74, 138, 266, 522, 194, 322, 578, 642, 396, 52, 148, 276, 292, 196, 324, 152, 280, 536, 200, 328, 776, 176, 304, 560, 656, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_779, vertices_611, vertices_181, vertices_805, vertices_197, vertices_225, vertices_666, vertices_202, vertices_330, vertices_706, vertices_412, vertices_460, vertices_308, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_545, vertices_193, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_396, vertices_52, vertices_148, vertices_276, vertices_292, vertices_196, vertices_324, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_776, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_779), (false, vertices_611), (false, vertices_181), (false, vertices_805), (false, vertices_197), (false, vertices_225), (true, vertices_74), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_396), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_304), (true, vertices_560), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 17 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_396) then 23 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 197 225 74 138 194 642 276 152 280 536 200 328 304 560 656 704 327 779 611 181 805 396
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 2 3 4 7 8 824 280 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 1 0 2 3 6 138 666 2
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 412
cert_cover_5 4 0 1 2 3 6 396 412 2
cert_coverFacet 5 460
cert_cover_5 5 0 1 2 5 6 396 460 2
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 824
cert_cover_5 7 2 2 3 4 7 280 824 2
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0498

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0499.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0499

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 901, 601, 809, 457, 62, 598, 422, 646, 242, 540, 556, 804, 312, 344, 496, 73, 265, 521, 193, 577, 385, 641, 769, 22, 38, 134, 518, 50, 82, 162, 194, 578, 642, 28, 44, 524, 532, 292, 548, 388, 644, 772, 56, 88, 280, 536, 296, 552, 328, 240, 304, 336, 592, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_901, vertices_601, vertices_809, vertices_457, vertices_62, vertices_598, vertices_422, vertices_646, vertices_242, vertices_540, vertices_556, vertices_804, vertices_312, vertices_344, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_134, vertices_518, vertices_50, vertices_82, vertices_162, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_524, vertices_532, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_240, vertices_304, vertices_336, vertices_592, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_901), (false, vertices_601), (false, vertices_809), (false, vertices_457), (true, vertices_22), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_162), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_280), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 22 26 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_240) then 27 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_336) then 16 else
  if p.val = (true, vertices_416) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 62 22 2
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_2 2 3 4 5 6 240
cert_row_4 3 0 1 4 6 7 422 38 3
cert_rows
cert_pivot_2 2 8 3 0
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 22 62 2
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 422
cert_cover_5 2 3 0 1 4 6 38 422 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 50 242 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coverFacet 10 496
cert_cover_5 10 2 3 4 5 7 240 496 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0499

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0500.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0500

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 901, 681, 625, 481, 62, 398, 598, 774, 282, 338, 556, 652, 564, 248, 472, 97, 161, 545, 321, 577, 385, 641, 769, 14, 22, 262, 518, 26, 266, 82, 274, 322, 578, 770, 44, 140, 524, 52, 532, 548, 388, 644, 772, 56, 216, 280, 168, 552, 392, 648, 112, 560, 336, 592, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_901, vertices_681, vertices_625, vertices_481, vertices_62, vertices_398, vertices_598, vertices_774, vertices_282, vertices_338, vertices_556, vertices_652, vertices_564, vertices_248, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_524, vertices_52, vertices_532, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_216, vertices_280, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_901), (false, vertices_681), (false, vertices_625), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_548), (true, vertices_56), (true, vertices_216), (true, vertices_280), (true, vertices_392), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 22 25 27 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (false, vertices_481) then 28 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_56) then 14 else
  if p.val = (true, vertices_216) then 24 else
  if p.val = (true, vertices_280) then 15 else
  if p.val = (true, vertices_392) then 16 else
  if p.val = (true, vertices_336) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 62 14 3
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_2 2 2 3 5 6 216
cert_row_4 3 0 1 3 5 8 598 22 3
cert_rows
cert_pivot_2 4 7 2 0
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 398
cert_cover_5 1 1 0 1 2 6 14 398 3
cert_coverFacet 2 598
cert_cover_5 2 3 0 1 3 5 22 598 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 564
cert_cover_2 8 3 1 4 8 52 564 3
cert_coverFacet 9 248
cert_cover_5 9 2 2 3 4 5 56 248 3
cert_coverFacet 10 472
cert_cover_5 10 2 2 3 5 7 216 472 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0500

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0501.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0501

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 357, 549, 709, 457, 433, 782, 806, 314, 538, 178, 722, 604, 332, 216, 408, 37, 69, 517, 161, 289, 545, 193, 321, 385, 641, 774, 26, 266, 522, 50, 146, 530, 162, 290, 546, 642, 76, 268, 524, 292, 548, 324, 580, 88, 152, 280, 536, 200, 328, 392, 176, 304, 208, 592, 400, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_357, vertices_549, vertices_709, vertices_457, vertices_433, vertices_782, vertices_806, vertices_314, vertices_538, vertices_178, vertices_722, vertices_604, vertices_332, vertices_216, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_774, vertices_26, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_76, vertices_268, vertices_524, vertices_292, vertices_548, vertices_324, vertices_580, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_357), (false, vertices_549), (false, vertices_709), (false, vertices_457), (false, vertices_433), (true, vertices_774), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_774) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_536) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_592) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 549 26 266 522 50 146 530 290 76 268 524 88 152 280 536 208 592 675 774 357 709 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_2 1 0 1 7 8 774
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 774 782 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 774 806 2
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 26 314 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 146 722 2
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0501

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0502.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0502

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 779, 789, 569, 233, 433, 342, 198, 646, 774, 650, 482, 716, 628, 616, 368, 267, 41, 137, 521, 49, 273, 529, 161, 385, 769, 70, 134, 262, 518, 138, 522, 194, 322, 386, 642, 770, 84, 276, 532, 196, 580, 644, 772, 104, 552, 200, 584, 648, 112, 304, 560, 336, 224, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_779, vertices_789, vertices_569, vertices_233, vertices_433, vertices_342, vertices_198, vertices_646, vertices_774, vertices_650, vertices_482, vertices_716, vertices_628, vertices_616, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_267, vertices_41, vertices_137, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_385, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_138, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_644, vertices_772, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_224, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_779), (false, vertices_789), (false, vertices_569), (false, vertices_233), (false, vertices_433), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_84), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_584), (true, vertices_648), (true, vertices_112), (true, vertices_336), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 1 2 5 6 8 716 196 1
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 3 5 7 342 70 2
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 2 0 1 3 5 70 342 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 194 482 1
cert_coverFacet 6 716
cert_cover_5 6 0 1 2 5 6 196 716 1
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 84 628 2
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0502

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0503.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0503

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 787, 781, 341, 613, 241, 654, 314, 170, 778, 738, 460, 708, 184, 408, 464, 531, 69, 261, 517, 49, 81, 273, 97, 545, 769, 42, 138, 266, 522, 50, 274, 162, 546, 642, 770, 140, 268, 524, 196, 324, 580, 644, 56, 152, 280, 168, 392, 776, 176, 208, 336, 400, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_787, vertices_781, vertices_341, vertices_613, vertices_241, vertices_654, vertices_314, vertices_170, vertices_778, vertices_738, vertices_460, vertices_708, vertices_184, vertices_408, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_531, vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_97, vertices_545, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_546, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_787), (false, vertices_781), (false, vertices_341), (false, vertices_613), (false, vertices_241), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_642), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_400), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_613) then 23 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_448) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 42 314 2
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 162 738 2
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 140 460 2
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0503

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0504.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0504

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 659, 803, 597, 613, 361, 654, 394, 778, 402, 172, 812, 244, 660, 472, 232, 19, 259, 515, 581, 81, 529, 97, 289, 545, 321, 138, 266, 522, 146, 274, 386, 642, 770, 44, 140, 524, 84, 148, 532, 100, 164, 548, 644, 104, 168, 296, 200, 328, 392, 776, 208, 336, 400, 656, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_659, vertices_803, vertices_597, vertices_613, vertices_361, vertices_654, vertices_394, vertices_778, vertices_402, vertices_172, vertices_812, vertices_244, vertices_660, vertices_472, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_581, vertices_81, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_644, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_659), (false, vertices_803), (false, vertices_597), (false, vertices_613), (false, vertices_361), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_164), (true, vertices_644), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_597) then 22 else
  if p.val = (false, vertices_613) then 23 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 24 => Sum.inl 2
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
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 812
cert_cover_5 5 1 1 2 4 7 44 812 3
cert_coverFacet 6 244
cert_cover_5 6 2 1 3 4 5 84 244 2
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 200 472 1
cert_coverFacet 9 232
cert_cover_2 9 4 2 5 6 104 232 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0504

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0505.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0505

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 803, 643, 653, 361, 585, 849, 902, 370, 178, 402, 604, 236, 244, 404, 788, 35, 131, 515, 41, 73, 137, 521, 289, 321, 577, 641, 769, 50, 146, 274, 162, 290, 386, 642, 770, 76, 140, 524, 84, 148, 276, 532, 228, 388, 644, 772, 104, 168, 584, 112, 176, 336, 592, 400, 784, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_803, vertices_643, vertices_653, vertices_361, vertices_585, vertices_849, vertices_902, vertices_370, vertices_178, vertices_402, vertices_604, vertices_236, vertices_244, vertices_404, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_41, vertices_73, vertices_137, vertices_521, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_228, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_584, vertices_112, vertices_176, vertices_336, vertices_592, vertices_400, vertices_784, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_803), (false, vertices_643), (false, vertices_653), (false, vertices_361), (false, vertices_585), (false, vertices_849), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_228), (true, vertices_388), (true, vertices_772), (true, vertices_112), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_228) then 21 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 643 1 585 50 146 274 386 76 84 148 276 532 388 772 112 176 400 171 803 653 228 361 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 76 2
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_2 2 1 4 5 6 228
cert_row_4 3 0 3 4 5 7 370 50 3
cert_rows
cert_pivot_2 2 8 1 0
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 370
cert_cover_5 1 3 0 3 4 5 50 370 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 604
cert_cover_5 4 0 1 2 3 5 76 604 2
cert_coverFacet 5 236
cert_cover_5 5 2 1 2 4 5 76 236 2
cert_coverFacet 6 244
cert_cover_5 6 2 1 3 4 5 84 244 2
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0505

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0506.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0506

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 93, 533, 677, 453, 593, 865, 174, 570, 410, 850, 802, 540, 556, 204, 472, 21, 69, 133, 517, 81, 529, 161, 289, 545, 321, 577, 385, 26, 42, 138, 274, 530, 162, 290, 546, 386, 770, 28, 44, 76, 140, 524, 532, 164, 548, 196, 88, 408, 536, 552, 200, 336, 592, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_93, vertices_533, vertices_677, vertices_453, vertices_593, vertices_865, vertices_174, vertices_570, vertices_410, vertices_850, vertices_802, vertices_540, vertices_556, vertices_204, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_517, vertices_81, vertices_529, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_26, vertices_42, vertices_138, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_524, vertices_532, vertices_164, vertices_548, vertices_196, vertices_88, vertices_408, vertices_536, vertices_552, vertices_200, vertices_336, vertices_592, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_93), (false, vertices_533), (false, vertices_677), (false, vertices_453), (false, vertices_593), (false, vertices_865), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_408), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 6 174 42 1
cert_row_2 1 2 3 6 7 408
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 0 3 5 7 8 850 274 2
cert_rows
cert_pivot_2 1 6 2 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 42 174 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 26 410 3
cert_coverFacet 3 850
cert_cover_5 3 3 0 3 5 7 274 850 2
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0506

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0507.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0507

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 781, 309, 85, 617, 297, 241, 454, 774, 410, 650, 778, 738, 468, 696, 312, 21, 69, 261, 517, 41, 265, 521, 49, 81, 97, 289, 577, 70, 262, 518, 138, 266, 522, 194, 578, 386, 642, 770, 84, 276, 452, 772, 56, 152, 280, 296, 552, 648, 776, 176, 304, 208, 400, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_781, vertices_309, vertices_85, vertices_617, vertices_297, vertices_241, vertices_454, vertices_774, vertices_410, vertices_650, vertices_778, vertices_738, vertices_468, vertices_696, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_49, vertices_81, vertices_97, vertices_289, vertices_577, vertices_70, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_452, vertices_772, vertices_56, vertices_152, vertices_280, vertices_296, vertices_552, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_781), (false, vertices_309), (false, vertices_85), (false, vertices_617), (false, vertices_297), (false, vertices_241), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_452), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_648), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 18 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_309) then 22 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_452) then 23 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_452), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 5 6 7 452
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 70 454 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 138 410 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 194 738 1
cert_coverFacet 6 468
cert_cover_5 6 0 1 3 5 6 84 468 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 56 696 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0507

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0508.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0508

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 285, 661, 837, 369, 689, 782, 170, 554, 458, 242, 834, 156, 684, 408, 464, 21, 261, 517, 49, 657, 273, 97, 545, 321, 577, 42, 138, 266, 522, 98, 162, 546, 194, 322, 578, 770, 28, 140, 268, 524, 148, 644, 772, 152, 280, 168, 552, 392, 112, 176, 208, 336, 400, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_285, vertices_661, vertices_837, vertices_369, vertices_689, vertices_782, vertices_170, vertices_554, vertices_458, vertices_242, vertices_834, vertices_156, vertices_684, vertices_408, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_49, vertices_657, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_42, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_644, vertices_772, vertices_152, vertices_280, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_208, vertices_336, vertices_400, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_285), (false, vertices_661), (false, vertices_837), (false, vertices_369), (false, vertices_689), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_770), (true, vertices_140), (true, vertices_524), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 23 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_661) then 24 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 6 242 98 1
cert_row_4 1 0 2 5 6 7 458 138 2
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 6 138 458 2
cert_coverFacet 4 242
cert_cover_5 4 0 0 3 4 5 98 242 1
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 684
cert_cover_5 7 3 1 2 4 6 140 684 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0508

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0509.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0509

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 541, 173, 149, 601, 361, 433, 678, 842, 210, 402, 418, 802, 706, 812, 724, 13, 21, 133, 537, 41, 73, 81, 145, 273, 161, 289, 321, 82, 146, 274, 162, 290, 546, 194, 322, 578, 386, 642, 770, 44, 524, 148, 532, 164, 548, 644, 296, 328, 584, 776, 208, 592, 400, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_541, vertices_173, vertices_149, vertices_601, vertices_361, vertices_433, vertices_678, vertices_842, vertices_210, vertices_402, vertices_418, vertices_802, vertices_706, vertices_812, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_537, vertices_41, vertices_73, vertices_81, vertices_145, vertices_273, vertices_161, vertices_289, vertices_321, vertices_82, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_148, vertices_532, vertices_164, vertices_548, vertices_644, vertices_296, vertices_328, vertices_584, vertices_776, vertices_208, vertices_592, vertices_400, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_541), (false, vertices_173), (false, vertices_149), (false, vertices_601), (false, vertices_361), (false, vertices_433), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_548), (true, vertices_644), (true, vertices_776), (true, vertices_208), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 20 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_800) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 1 3 5 6 8 724 148 2
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 322 842 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 706
cert_cover_2 6 5 0 6 8 194 706 3
cert_coverFacet 7 812
cert_cover_5 7 3 1 2 4 7 44 812 3
cert_coverFacet 8 724
cert_cover_5 8 0 1 3 5 6 148 724 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0509

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0511.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0511

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 611, 163, 589, 361, 393, 433, 662, 178, 818, 220, 652, 340, 788, 868, 472, 35, 131, 515, 73, 137, 265, 521, 97, 161, 289, 577, 385, 50, 146, 530, 162, 546, 642, 76, 140, 524, 84, 148, 276, 532, 324, 580, 644, 772, 216, 328, 392, 648, 176, 304, 336, 400, 784, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_611, vertices_163, vertices_589, vertices_361, vertices_393, vertices_433, vertices_662, vertices_178, vertices_818, vertices_220, vertices_652, vertices_340, vertices_788, vertices_868, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_772, vertices_216, vertices_328, vertices_392, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_784, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_611), (false, vertices_163), (false, vertices_589), (false, vertices_361), (false, vertices_393), (false, vertices_433), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_140), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_216), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_216) then 23 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 3 4 7 8 818 50 3
cert_row_4 3 1 4 5 7 8 868 324 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 50 818 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 76 220 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 324 868 1
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 7 216 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0511

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0512.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0512

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 173, 781, 597, 197, 345, 233, 678, 810, 434, 722, 556, 708, 360, 464, 480, 13, 69, 133, 517, 169, 73, 265, 81, 273, 529, 193, 769, 146, 274, 530, 162, 290, 546, 642, 770, 44, 524, 164, 548, 196, 580, 644, 104, 296, 552, 328, 776, 208, 336, 592, 400, 224, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_173, vertices_781, vertices_597, vertices_197, vertices_345, vertices_233, vertices_678, vertices_810, vertices_434, vertices_722, vertices_556, vertices_708, vertices_360, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_517, vertices_169, vertices_73, vertices_265, vertices_81, vertices_273, vertices_529, vertices_193, vertices_769, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_44, vertices_524, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_173), (false, vertices_781), (false, vertices_597), (false, vertices_197), (false, vertices_345), (false, vertices_233), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_208), (true, vertices_400), (true, vertices_352), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_173) then 22 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 1 2 4 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 146 434 2
cert_coverFacet 3 722
cert_cover_5 3 3 0 3 5 6 146 722 2
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0512

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0513.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0513

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 677, 837, 465, 417, 62, 566, 90, 234, 850, 674, 796, 216, 408, 424, 37, 261, 517, 161, 289, 193, 321, 577, 385, 641, 54, 26, 42, 74, 82, 530, 162, 546, 194, 578, 642, 28, 44, 268, 532, 548, 772, 88, 152, 280, 168, 296, 200, 392, 208, 336, 400, 784, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_677, vertices_837, vertices_465, vertices_417, vertices_62, vertices_566, vertices_90, vertices_234, vertices_850, vertices_674, vertices_796, vertices_216, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_26, vertices_42, vertices_74, vertices_82, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_268, vertices_532, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_392, vertices_208, vertices_336, vertices_400, vertices_784, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_677), (false, vertices_837), (false, vertices_465), (false, vertices_417), (true, vertices_54), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_82), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_28), (true, vertices_532), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_301) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_54) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 417 26 42 74 82 530 162 546 28 532 88 152 280 168 200 392 784 707 54 301 677 837 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 6 234 42 3
cert_row_2 1 0 1 3 4 54
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 3 54 62 2
cert_coverFacet 1 566
cert_cover_5 1 1 0 1 3 8 54 566 3
cert_coverFacet 2 90
cert_cover_2 2 2 0 3 5 26 90 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 5 42 234 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 28 796 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0513

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0514.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0514

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [139, 779, 611, 195, 805, 457, 369, 158, 542, 722, 428, 780, 628, 180, 432, 464, 11, 67, 131, 515, 137, 265, 97, 289, 545, 193, 321, 769, 30, 138, 522, 146, 530, 194, 578, 140, 268, 524, 52, 148, 532, 164, 292, 548, 772, 392, 776, 112, 176, 304, 208, 336, 592, 400, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_139, vertices_779, vertices_611, vertices_195, vertices_805, vertices_457, vertices_369, vertices_158, vertices_542, vertices_722, vertices_428, vertices_780, vertices_628, vertices_180, vertices_432, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_131, vertices_515, vertices_137, vertices_265, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_30, vertices_138, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_772, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_400, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_139), (false, vertices_779), (false, vertices_611), (false, vertices_195), (false, vertices_805), (false, vertices_457), (false, vertices_369), (true, vertices_30), (true, vertices_146), (true, vertices_530), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 1 2 4 6 7 428 140 2
cert_row_2 1 0 1 2 3 30
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 6 30 158 3
cert_coverFacet 1 542
cert_cover_5 1 1 0 1 2 8 30 542 3
cert_coverFacet 2 722
cert_cover_5 2 2 0 3 5 6 146 722 2
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 140 428 2
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0514

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0515.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0515

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 173, 333, 293, 665, 585, 737, 790, 842, 242, 306, 722, 156, 540, 780, 436, 13, 37, 261, 73, 137, 521, 97, 161, 289, 321, 577, 641, 50, 210, 274, 530, 98, 290, 322, 578, 770, 28, 140, 268, 524, 148, 276, 532, 164, 292, 772, 152, 536, 328, 584, 776, 176, 304, 656, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_173, vertices_333, vertices_293, vertices_665, vertices_585, vertices_737, vertices_790, vertices_842, vertices_242, vertices_306, vertices_722, vertices_156, vertices_540, vertices_780, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_772, vertices_152, vertices_536, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_173), (false, vertices_333), (false, vertices_293), (false, vertices_665), (false, vertices_585), (false, vertices_737), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_28), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_776), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_173) then 20 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_210) then 18 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 293 0 585 50 274 530 578 770 28 524 148 276 532 772 776 176 304 355 210 173 333 665 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 242
cert_cover_5 2 1 0 3 4 5 50 242 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 8 210 722 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 436
cert_cover_5 8 3 1 3 4 6 148 436 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0515

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0516.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0516

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 451, 643, 77, 653, 837, 217, 566, 666, 434, 60, 540, 364, 804, 120, 496, 131, 259, 515, 13, 69, 517, 73, 137, 193, 321, 641, 769, 50, 146, 530, 290, 546, 386, 642, 28, 44, 76, 524, 52, 532, 292, 548, 324, 772, 56, 88, 152, 536, 104, 648, 112, 432, 208, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_451, vertices_643, vertices_77, vertices_653, vertices_837, vertices_217, vertices_566, vertices_666, vertices_434, vertices_60, vertices_540, vertices_364, vertices_804, vertices_120, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_13, vertices_69, vertices_517, vertices_73, vertices_137, vertices_193, vertices_321, vertices_641, vertices_769, vertices_50, vertices_146, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_532, vertices_292, vertices_548, vertices_324, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_648, vertices_112, vertices_432, vertices_208, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_451), (false, vertices_643), (false, vertices_77), (false, vertices_653), (false, vertices_837), (false, vertices_217), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_112), (true, vertices_432), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_77) then 1 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_432) then 25 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 1 2 4 5 7 364 44 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 0 2 3 6 8 666 146 1
cert_rows
cert_pivot_2 5 7 1 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 666
cert_cover_5 1 3 0 2 3 6 146 666 1
cert_coverFacet 2 434
cert_cover_5 2 1 0 3 4 6 50 434 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 364
cert_cover_5 5 0 1 2 4 5 44 364 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 496
cert_cover_5 8 1 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0516

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0517.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0517

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 355, 707, 653, 217, 345, 806, 626, 428, 780, 180, 564, 724, 408, 368, 432, 67, 259, 515, 89, 137, 265, 521, 193, 321, 641, 98, 290, 546, 578, 770, 140, 268, 524, 52, 148, 532, 164, 292, 548, 644, 772, 152, 280, 392, 776, 112, 176, 304, 560, 208, 336, 592, 400, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_355, vertices_707, vertices_653, vertices_217, vertices_345, vertices_806, vertices_626, vertices_428, vertices_780, vertices_180, vertices_564, vertices_724, vertices_408, vertices_368, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_89, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_152, vertices_280, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_355), (false, vertices_707), (false, vertices_653), (false, vertices_217), (false, vertices_345), (true, vertices_546), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_392), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_653) then 22 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_345) then 25 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 6 7 428 140 2
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 3 4 5 8 626 98 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 626
cert_cover_5 1 2 0 3 4 5 98 626 1
cert_coverFacet 2 428
cert_cover_5 2 0 1 2 4 6 140 428 2
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0517

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0518.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0518

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 611, 451, 557, 121, 345, 902, 722, 172, 396, 780, 628, 180, 660, 440, 464, 67, 259, 515, 89, 41, 265, 521, 97, 545, 321, 194, 578, 386, 642, 770, 44, 140, 268, 524, 52, 148, 532, 164, 548, 388, 644, 772, 56, 280, 168, 392, 776, 112, 176, 208, 336, 592, 400, 656, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_611, vertices_451, vertices_557, vertices_121, vertices_345, vertices_902, vertices_722, vertices_172, vertices_396, vertices_780, vertices_628, vertices_180, vertices_660, vertices_440, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_89, vertices_41, vertices_265, vertices_521, vertices_97, vertices_545, vertices_321, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_168, vertices_392, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_611), (false, vertices_451), (false, vertices_557), (false, vertices_121), (false, vertices_345), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_557) then 22 else
  if p.val = (false, vertices_121) then 24 else
  if p.val = (false, vertices_345) then 25 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 6 7 440 56 3
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 3 5 6 8 722 194 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 722
cert_cover_5 1 2 0 3 5 6 194 722 1
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 396
cert_cover_2 3 2 1 6 7 140 396 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 440
cert_cover_5 8 0 2 3 4 6 56 440 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0518

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0519.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0519

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 595, 323, 653, 457, 737, 790, 114, 306, 482, 188, 284, 780, 628, 676, 440, 67, 259, 515, 137, 265, 521, 193, 321, 577, 641, 50, 82, 274, 530, 98, 290, 322, 770, 28, 140, 268, 524, 52, 276, 532, 164, 548, 644, 772, 184, 280, 392, 776, 112, 304, 592, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_595, vertices_323, vertices_653, vertices_457, vertices_737, vertices_790, vertices_114, vertices_306, vertices_482, vertices_188, vertices_284, vertices_780, vertices_628, vertices_676, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_548, vertices_644, vertices_772, vertices_184, vertices_280, vertices_392, vertices_776, vertices_112, vertices_304, vertices_592, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_595), (false, vertices_323), (false, vertices_653), (false, vertices_457), (false, vertices_737), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_28), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_184), (true, vertices_280), (true, vertices_112), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_184) then 24 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_184), by decide +kernel⟩
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
cert_row_2 0 2 3 4 6 184
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 114
cert_cover_2 1 3 0 4 5 50 114 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 188
cert_cover_5 4 0 1 2 3 4 28 188 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coverFacet 9 440
cert_cover_5 9 0 2 3 4 7 184 440 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0519

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0520.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0520

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 565, 277, 709, 113, 465, 782, 106, 298, 714, 818, 652, 788, 248, 440, 21, 133, 261, 517, 49, 81, 273, 97, 545, 193, 577, 385, 42, 74, 266, 522, 98, 290, 546, 578, 770, 140, 268, 524, 276, 532, 644, 772, 184, 104, 296, 200, 392, 648, 112, 304, 560, 208, 400, 784, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_565, vertices_277, vertices_709, vertices_113, vertices_465, vertices_782, vertices_106, vertices_298, vertices_714, vertices_818, vertices_652, vertices_788, vertices_248, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_644, vertices_772, vertices_184, vertices_104, vertices_296, vertices_200, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_784, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_565), (false, vertices_277), (false, vertices_709), (false, vertices_113), (false, vertices_465), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_770), (true, vertices_524), (true, vertices_772), (true, vertices_184), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_648), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_184) then 23 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_184), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_2 2 2 3 4 6 184
cert_row_4 3 0 3 4 7 8 818 290 1
cert_rows
cert_pivot_2 1 5 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 106
cert_cover_2 1 2 0 4 5 42 106 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 74 714 3
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 290 818 1
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 5 184 248 3
cert_coverFacet 8 440
cert_cover_5 8 2 2 3 4 7 184 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0520

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0521.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0521

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 267, 835, 613, 169, 457, 241, 790, 410, 666, 684, 372, 180, 660, 836, 464, 11, 259, 515, 41, 137, 265, 97, 161, 545, 193, 321, 577, 154, 266, 522, 274, 530, 770, 52, 148, 276, 532, 100, 164, 548, 324, 580, 644, 772, 168, 552, 392, 648, 112, 176, 208, 336, 400, 656, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_267, vertices_835, vertices_613, vertices_169, vertices_457, vertices_241, vertices_790, vertices_410, vertices_666, vertices_684, vertices_372, vertices_180, vertices_660, vertices_836, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_41, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_154, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_52, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_644, vertices_772, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_208, vertices_336, vertices_400, vertices_656, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_267), (false, vertices_835), (false, vertices_613), (false, vertices_169), (false, vertices_457), (false, vertices_241), (true, vertices_154), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_648), (true, vertices_336), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_154) then 19 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 7 372 52 3
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_2 2 0 2 3 6 154
cert_row_4 3 1 2 4 6 8 684 164 1
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 7 154 410 3
cert_coverFacet 2 666
cert_cover_5 2 2 0 2 3 8 154 666 3
cert_coverFacet 3 684
cert_cover_5 3 3 1 2 4 6 164 684 1
cert_coverFacet 4 372
cert_cover_5 4 0 1 3 4 5 52 372 3
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0521

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0522.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0522

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 787, 451, 77, 525, 837, 233, 566, 434, 674, 60, 348, 684, 788, 120, 496, 131, 259, 515, 13, 69, 517, 73, 137, 521, 193, 321, 769, 50, 274, 530, 162, 546, 386, 642, 28, 44, 76, 524, 52, 276, 532, 548, 324, 772, 56, 88, 104, 168, 648, 112, 432, 336, 784, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_787, vertices_451, vertices_77, vertices_525, vertices_837, vertices_233, vertices_566, vertices_434, vertices_674, vertices_60, vertices_348, vertices_684, vertices_788, vertices_120, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_13, vertices_69, vertices_517, vertices_73, vertices_137, vertices_521, vertices_193, vertices_321, vertices_769, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_276, vertices_532, vertices_548, vertices_324, vertices_772, vertices_56, vertices_88, vertices_104, vertices_168, vertices_648, vertices_112, vertices_432, vertices_336, vertices_784, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_787), (false, vertices_451), (false, vertices_77), (false, vertices_525), (false, vertices_837), (false, vertices_233), (true, vertices_50), (true, vertices_162), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_112), (true, vertices_432), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_432) then 25 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 1 2 3 5 7 348 28 3
cert_row_2 2 3 4 6 7 432
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 0 5 3 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 434
cert_cover_5 1 2 0 3 4 6 50 434 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 348
cert_cover_5 4 1 1 2 3 5 28 348 3
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 44 684 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 496
cert_cover_5 8 2 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0522

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0523.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0523

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 557, 421, 709, 465, 801, 542, 90, 362, 554, 722, 802, 188, 660, 440, 344, 37, 133, 517, 289, 545, 193, 321, 577, 385, 769, 26, 42, 74, 522, 82, 530, 290, 546, 322, 578, 770, 28, 44, 524, 148, 532, 164, 644, 184, 88, 280, 296, 552, 328, 208, 336, 400, 656, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_557, vertices_421, vertices_709, vertices_465, vertices_801, vertices_542, vertices_90, vertices_362, vertices_554, vertices_722, vertices_802, vertices_188, vertices_660, vertices_440, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_26, vertices_42, vertices_74, vertices_522, vertices_82, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_524, vertices_148, vertices_532, vertices_164, vertices_644, vertices_184, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_557), (false, vertices_421), (false, vertices_709), (false, vertices_465), (false, vertices_801), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_28), (true, vertices_148), (true, vertices_532), (true, vertices_184), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_184) then 24 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_328) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(true, vertices_184), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 4 5 7 362 42 3
cert_row_2 2 2 3 4 6 184
cert_row_4 3 0 3 5 6 8 722 82 3
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 42 362 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 82 722 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 188
cert_cover_5 6 2 1 2 3 4 28 188 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 440
cert_cover_5 8 2 2 3 4 7 184 440 3
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0523

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0524.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0524

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 275, 355, 681, 241, 913, 801, 30, 782, 326, 410, 220, 236, 556, 868, 904, 19, 67, 259, 81, 145, 273, 97, 161, 289, 545, 641, 769, 14, 22, 70, 262, 26, 266, 274, 322, 28, 44, 204, 524, 84, 100, 548, 324, 772, 152, 168, 552, 392, 648, 776, 208, 400, 224, 352, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_275, vertices_355, vertices_681, vertices_241, vertices_913, vertices_801, vertices_30, vertices_782, vertices_326, vertices_410, vertices_220, vertices_236, vertices_556, vertices_868, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_262, vertices_26, vertices_266, vertices_274, vertices_322, vertices_28, vertices_44, vertices_204, vertices_524, vertices_84, vertices_100, vertices_548, vertices_324, vertices_772, vertices_152, vertices_168, vertices_552, vertices_392, vertices_648, vertices_776, vertices_208, vertices_400, vertices_224, vertices_352, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_275), (false, vertices_355), (false, vertices_681), (false, vertices_241), (false, vertices_913), (false, vertices_801), (true, vertices_14), (true, vertices_262), (true, vertices_26), (true, vertices_266), (true, vertices_28), (true, vertices_44), (true, vertices_204), (true, vertices_524), (true, vertices_100), (true, vertices_548), (true, vertices_324), (true, vertices_772), (true, vertices_152), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 17 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_913) then 25 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_204) then 20 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_776) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 7 14 782 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 410
cert_cover_5 3 0 0 2 3 6 26 410 3
cert_coverFacet 4 220
cert_cover_5 4 1 1 2 3 5 28 220 3
cert_coverFacet 5 236
cert_cover_5 5 1 1 2 4 5 44 236 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 100 868 3
cert_coverFacet 8 904
cert_cover_2 8 6 2 7 8 392 904 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0524

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0525.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0525

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 333, 789, 101, 677, 369, 177, 590, 410, 794, 202, 738, 780, 612, 488, 432, 37, 69, 261, 517, 49, 145, 273, 529, 97, 161, 321, 641, 282, 74, 138, 522, 146, 530, 194, 578, 642, 76, 268, 524, 100, 548, 580, 772, 200, 328, 392, 776, 176, 304, 400, 784, 224, 352, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_333, vertices_789, vertices_101, vertices_677, vertices_369, vertices_177, vertices_590, vertices_410, vertices_794, vertices_202, vertices_738, vertices_780, vertices_612, vertices_488, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_321, vertices_641, vertices_282, vertices_74, vertices_138, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_76, vertices_268, vertices_524, vertices_100, vertices_548, vertices_580, vertices_772, vertices_200, vertices_328, vertices_392, vertices_776, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_333), (false, vertices_789), (false, vertices_101), (false, vertices_677), (false, vertices_369), (false, vertices_177), (true, vertices_282), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_524), (true, vertices_580), (true, vertices_200), (true, vertices_392), (true, vertices_776), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (true, vertices_282) then 18 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 101 1 177 74 138 522 194 578 524 580 200 392 776 400 224 608 416 659 282 333 789 677 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 282 410 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 8 282 794 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 200 488 1
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0525

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0526.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0526

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 211, 675, 323, 301, 549, 481, 842, 594, 658, 60, 604, 780, 692, 440, 472, 67, 131, 259, 515, 37, 261, 517, 161, 289, 545, 193, 321, 82, 146, 530, 322, 578, 642, 770, 28, 44, 268, 524, 52, 532, 548, 772, 56, 88, 408, 296, 328, 584, 776, 176, 208, 592, 656, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_211, vertices_675, vertices_323, vertices_301, vertices_549, vertices_481, vertices_842, vertices_594, vertices_658, vertices_60, vertices_604, vertices_780, vertices_692, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_56, vertices_88, vertices_408, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_211), (false, vertices_675), (false, vertices_323), (false, vertices_301), (false, vertices_549), (false, vertices_481), (true, vertices_530), (true, vertices_578), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_176), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_301) then 21 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
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
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_2 1 2 3 6 7 408
cert_row_4 2 1 2 3 5 8 604 28 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 0 0 2 5 7 322 842 1
cert_coverFacet 1 594
cert_cover_2 1 3 0 5 8 82 594 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 604
cert_cover_5 4 2 1 2 3 5 28 604 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 440
cert_cover_5 7 1 2 3 4 6 56 440 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0526

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0527.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0527

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 117, 789, 177, 657, 865, 398, 618, 170, 778, 914, 220, 404, 248, 840, 21, 69, 261, 49, 145, 529, 97, 161, 545, 321, 641, 769, 42, 138, 266, 522, 162, 546, 386, 642, 770, 76, 140, 268, 84, 148, 276, 388, 216, 104, 168, 328, 584, 776, 112, 176, 400, 656, 784, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_117, vertices_789, vertices_177, vertices_657, vertices_865, vertices_398, vertices_618, vertices_170, vertices_778, vertices_914, vertices_220, vertices_404, vertices_248, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_49, vertices_145, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_388, vertices_216, vertices_104, vertices_168, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_400, vertices_656, vertices_784, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_117), (false, vertices_789), (false, vertices_177), (false, vertices_657), (false, vertices_865), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_148), (true, vertices_388), (true, vertices_216), (true, vertices_104), (true, vertices_168), (true, vertices_584), (true, vertices_776), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_216) then 23 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_2 2 2 3 5 6 216
cert_row_4 3 0 3 6 7 8 914 386 1
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 42 618 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 914
cert_cover_5 4 3 0 3 6 7 386 914 1
cert_coverFacet 5 220
cert_cover_5 5 2 1 2 3 5 76 220 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 5 216 248 2
cert_coverFacet 8 840
cert_cover_2 8 5 2 7 8 328 840 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0527

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0528.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0528

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 211, 275, 675, 617, 849, 225, 654, 150, 278, 428, 844, 436, 376, 680, 240, 19, 131, 259, 515, 81, 273, 97, 161, 545, 193, 577, 769, 22, 134, 262, 518, 146, 274, 642, 140, 268, 524, 148, 276, 420, 772, 104, 168, 296, 552, 328, 584, 648, 112, 176, 304, 208, 336, 224, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_211, vertices_275, vertices_675, vertices_617, vertices_849, vertices_225, vertices_654, vertices_150, vertices_278, vertices_428, vertices_844, vertices_436, vertices_376, vertices_680, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_81, vertices_273, vertices_97, vertices_161, vertices_545, vertices_193, vertices_577, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_642, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_420, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_211), (false, vertices_275), (false, vertices_675), (false, vertices_617), (false, vertices_849), (false, vertices_225), (true, vertices_22), (true, vertices_134), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_420), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_648), (true, vertices_112), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_420) then 21 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 4 6 7 420
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 3 4 5 7 376 104 1
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 140 428 2
cert_coverFacet 4 844
cert_cover_5 4 2 1 2 5 7 268 844 2
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 148 436 2
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 104 376 1
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0528

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4383 : Certifies 4383 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0498.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4384 : Certifies 4384 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0499.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4385 : Certifies 4385 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0500.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4386 : Certifies 4386 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0501.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4387 : Certifies 4387 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0502.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4388 : Certifies 4388 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0503.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4389 : Certifies 4389 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0504.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4390 : Certifies 4390 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0505.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4391 : Certifies 4391 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0506.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4392 : Certifies 4392 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0507.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4393 : Certifies 4393 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0508.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4394 : Certifies 4394 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0509.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4395 : Certifies 4395 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0511.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4396 : Certifies 4396 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0512.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4397 : Certifies 4397 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0513.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4398 : Certifies 4398 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0514.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4399 : Certifies 4399 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0515.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4400 : Certifies 4400 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0516.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4401 : Certifies 4401 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0517.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4402 : Certifies 4402 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0518.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4403 : Certifies 4403 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0519.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4404 : Certifies 4404 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0520.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4405 : Certifies 4405 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0521.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4406 : Certifies 4406 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0522.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4407 : Certifies 4407 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0523.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4408 : Certifies 4408 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0524.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4409 : Certifies 4409 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0525.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4410 : Certifies 4410 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0526.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4411 : Certifies 4411 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0527.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4412 : Certifies 4412 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0528.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B145 (j : Fin 30) :
    Certifies (4383 + j.val) := by
  fin_cases j
  · exact projection_4383
  · exact projection_4384
  · exact projection_4385
  · exact projection_4386
  · exact projection_4387
  · exact projection_4388
  · exact projection_4389
  · exact projection_4390
  · exact projection_4391
  · exact projection_4392
  · exact projection_4393
  · exact projection_4394
  · exact projection_4395
  · exact projection_4396
  · exact projection_4397
  · exact projection_4398
  · exact projection_4399
  · exact projection_4400
  · exact projection_4401
  · exact projection_4402
  · exact projection_4403
  · exact projection_4404
  · exact projection_4405
  · exact projection_4406
  · exact projection_4407
  · exact projection_4408
  · exact projection_4409
  · exact projection_4410
  · exact projection_4411
  · exact projection_4412

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
