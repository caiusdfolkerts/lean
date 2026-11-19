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
/- Source: ProjectionCertificates/R_m16e10q1_0529.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0529

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 121, 281, 433, 865, 270, 526, 422, 710, 690, 802, 220, 412, 624, 720, 25, 73, 265, 521, 49, 273, 97, 289, 577, 769, 14, 134, 262, 518, 266, 522, 162, 290, 546, 642, 770, 156, 76, 268, 524, 196, 580, 388, 88, 280, 112, 176, 560, 208, 592, 400, 656, 608, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_121, vertices_281, vertices_433, vertices_865, vertices_270, vertices_526, vertices_422, vertices_710, vertices_690, vertices_802, vertices_220, vertices_412, vertices_624, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_49, vertices_273, vertices_97, vertices_289, vertices_577, vertices_769, vertices_14, vertices_134, vertices_262, vertices_518, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_156, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_88, vertices_280, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_400, vertices_656, vertices_608, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_121), (false, vertices_281), (false, vertices_433), (false, vertices_865), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_156), (true, vertices_268), (true, vertices_196), (true, vertices_388), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_156) then 21 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 0 3 4 6 8 690 162 1
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 134 422 2
cert_coverFacet 3 710
cert_cover_5 3 2 0 1 5 6 134 710 2
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 162 690 1
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 220
cert_cover_5 6 0 1 2 3 5 156 220 3
cert_coverFacet 7 412
cert_cover_5 7 0 1 2 3 7 156 412 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0529

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0530.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0530

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 661, 313, 409, 233, 625, 310, 150, 838, 646, 458, 402, 812, 564, 616, 840, 281, 41, 137, 49, 145, 529, 97, 193, 577, 641, 22, 134, 262, 518, 146, 274, 194, 322, 578, 386, 642, 52, 148, 532, 292, 548, 644, 772, 104, 296, 552, 200, 328, 584, 392, 776, 304, 560, 400, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_661, vertices_313, vertices_409, vertices_233, vertices_625, vertices_310, vertices_150, vertices_838, vertices_646, vertices_458, vertices_402, vertices_812, vertices_564, vertices_616, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_281, vertices_41, vertices_137, vertices_49, vertices_145, vertices_529, vertices_97, vertices_193, vertices_577, vertices_641, vertices_22, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_52, vertices_148, vertices_532, vertices_292, vertices_548, vertices_644, vertices_772, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_304, vertices_560, vertices_400, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_661), (false, vertices_313), (false, vertices_409), (false, vertices_233), (false, vertices_625), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_386), (true, vertices_52), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 21 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_776) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 2 4 7 8 812 292 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 262 838 2
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 458
cert_cover_5 4 1 0 2 5 6 194 458 1
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 292 812 1
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coverFacet 9 840
cert_cover_2 9 5 2 7 8 328 840 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0530

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0531.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0531

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 147, 547, 707, 613, 361, 465, 662, 810, 786, 412, 796, 236, 556, 708, 456, 19, 35, 131, 515, 145, 273, 97, 289, 545, 193, 321, 577, 146, 274, 530, 290, 546, 642, 770, 284, 44, 140, 524, 148, 532, 100, 548, 196, 580, 644, 104, 296, 552, 200, 328, 392, 776, 400, 784, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_147, vertices_547, vertices_707, vertices_613, vertices_361, vertices_465, vertices_662, vertices_810, vertices_786, vertices_412, vertices_796, vertices_236, vertices_556, vertices_708, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_284, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_400, vertices_784, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_147), (false, vertices_547), (false, vertices_707), (false, vertices_613), (false, vertices_361), (false, vertices_465), (true, vertices_530), (true, vertices_770), (true, vertices_284), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_552), (true, vertices_200), (true, vertices_392), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_547) then 1 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_284) then 21 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 147 1 547 530 770 44 140 524 148 532 196 644 552 200 392 776 784 307 707 613 284 361 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 6 236 44 3
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_2 2 1 2 3 7 284
cert_row_4 3 0 2 4 7 8 810 290 1
cert_rows
cert_pivot_2 5 6 1 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 290 810 1
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 412
cert_cover_5 3 2 1 2 3 6 284 412 3
cert_coverFacet 4 796
cert_cover_5 4 2 1 2 3 8 284 796 3
cert_coverFacet 5 236
cert_cover_5 5 0 1 2 4 5 44 236 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0531

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0532.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0532

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 595, 355, 809, 113, 689, 398, 198, 582, 450, 684, 780, 724, 376, 184, 472, 67, 259, 515, 49, 81, 529, 97, 289, 545, 769, 70, 134, 262, 518, 194, 322, 578, 386, 140, 268, 524, 196, 580, 644, 772, 56, 344, 152, 168, 296, 552, 392, 776, 112, 176, 208, 592, 656, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_595, vertices_355, vertices_809, vertices_113, vertices_689, vertices_398, vertices_198, vertices_582, vertices_450, vertices_684, vertices_780, vertices_724, vertices_376, vertices_184, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_644, vertices_772, vertices_56, vertices_344, vertices_152, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_595), (false, vertices_355), (false, vertices_809), (false, vertices_113), (false, vertices_689), (true, vertices_70), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_56), (true, vertices_344), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_355) then 20 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_344) then 24 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 2 3 5 7 344
cert_row_4 2 1 2 4 6 8 684 140 2
cert_row_4 3 1 3 5 6 8 724 196 1
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 140 684 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 196 724 1
cert_coverFacet 7 376
cert_cover_5 7 1 2 3 4 5 56 376 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coverFacet 9 472
cert_cover_5 9 1 2 3 5 6 344 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0532

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0533.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0533

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 451, 601, 329, 737, 310, 166, 774, 418, 796, 628, 676, 248, 440, 456, 131, 259, 515, 73, 265, 521, 193, 321, 577, 641, 38, 134, 262, 518, 162, 290, 386, 770, 52, 276, 532, 164, 548, 644, 772, 184, 88, 280, 536, 200, 328, 392, 776, 112, 304, 592, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_451, vertices_601, vertices_329, vertices_737, vertices_310, vertices_166, vertices_774, vertices_418, vertices_796, vertices_628, vertices_676, vertices_248, vertices_440, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_38, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_386, vertices_770, vertices_52, vertices_276, vertices_532, vertices_164, vertices_548, vertices_644, vertices_772, vertices_184, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_304, vertices_592, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_451), (false, vertices_601), (false, vertices_329), (false, vertices_737), (true, vertices_38), (true, vertices_262), (true, vertices_162), (true, vertices_290), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_184), (true, vertices_280), (true, vertices_200), (true, vertices_392), (true, vertices_112), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_184) then 24 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_4 1 0 1 3 4 7 310 38 2
cert_row_4 2 1 2 3 7 8 796 276 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 38 310 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 796
cert_cover_5 4 2 1 2 3 7 276 796 1
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 184 248 3
cert_coverFacet 8 440
cert_cover_5 8 0 2 3 4 7 184 440 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0533

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0534.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0534

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 837, 409, 361, 201, 721, 158, 174, 534, 358, 774, 282, 298, 692, 612, 744, 73, 137, 265, 145, 273, 529, 193, 321, 577, 769, 142, 22, 38, 262, 518, 26, 42, 266, 274, 530, 290, 770, 148, 532, 100, 164, 548, 324, 580, 772, 152, 280, 104, 168, 296, 200, 656, 352, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_837, vertices_409, vertices_361, vertices_201, vertices_721, vertices_158, vertices_174, vertices_534, vertices_358, vertices_774, vertices_282, vertices_298, vertices_692, vertices_612, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_142, vertices_22, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_274, vertices_530, vertices_290, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_656, vertices_352, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_837), (false, vertices_409), (false, vertices_361), (false, vertices_201), (false, vertices_721), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_290), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_168), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_142) then 19 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_42) then 6 else
  if p.val = (true, vertices_266) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 201 22 38 262 518 26 42 266 290 148 532 100 164 548 168 608 672 787 142 837 409 361 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 7 358 38 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 1 0 1 2 4 142 174 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 358
cert_cover_5 3 0 0 1 4 5 38 358 3
cert_coverFacet 4 774
cert_cover_2 4 1 0 7 8 262 774 3
cert_coverFacet 5 282
cert_cover_2 5 2 0 3 7 26 282 3
cert_coverFacet 6 298
cert_cover_2 6 2 0 4 7 42 298 3
cert_coverFacet 7 692
cert_cover_5 7 2 1 3 4 6 148 692 2
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coverFacet 9 744
cert_cover_5 9 3 2 4 5 6 104 744 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0534

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0535.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0535

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 653, 213, 357, 773, 737, 158, 58, 298, 906, 626, 722, 284, 780, 340, 376, 69, 133, 261, 517, 97, 289, 545, 193, 641, 769, 26, 42, 138, 266, 50, 594, 146, 290, 546, 642, 770, 28, 140, 268, 524, 84, 148, 276, 324, 772, 56, 280, 296, 648, 776, 112, 208, 336, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_653, vertices_213, vertices_357, vertices_773, vertices_737, vertices_158, vertices_58, vertices_298, vertices_906, vertices_626, vertices_722, vertices_284, vertices_780, vertices_340, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_50, vertices_594, vertices_146, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_324, vertices_772, vertices_56, vertices_280, vertices_296, vertices_648, vertices_776, vertices_112, vertices_208, vertices_336, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_653), (false, vertices_213), (false, vertices_357), (false, vertices_773), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_594), (true, vertices_146), (true, vertices_642), (true, vertices_28), (true, vertices_268), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_213) then 22 else
  if p.val = (false, vertices_357) then 23 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_594) then 19 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_112) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_594), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 6 158 26 1
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_2 2 0 3 5 8 594
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 26 158 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 138 906 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 594 722 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 376
cert_cover_5 9 3 2 3 4 5 56 376 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0535

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0536.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0536

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 275, 611, 899, 677, 241, 401, 286, 586, 778, 220, 236, 300, 916, 804, 872, 19, 67, 259, 515, 81, 145, 273, 97, 161, 545, 385, 641, 26, 74, 266, 522, 274, 578, 770, 28, 44, 204, 268, 148, 276, 164, 292, 548, 644, 772, 88, 104, 296, 584, 776, 208, 400, 224, 608, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_275, vertices_611, vertices_899, vertices_677, vertices_241, vertices_401, vertices_286, vertices_586, vertices_778, vertices_220, vertices_236, vertices_300, vertices_916, vertices_804, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_385, vertices_641, vertices_26, vertices_74, vertices_266, vertices_522, vertices_274, vertices_578, vertices_770, vertices_28, vertices_44, vertices_204, vertices_268, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_104, vertices_296, vertices_584, vertices_776, vertices_208, vertices_400, vertices_224, vertices_608, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_275), (false, vertices_611), (false, vertices_899), (false, vertices_677), (false, vertices_241), (false, vertices_401), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_204), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_899) then 19 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_204) then 22 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_2 2 1 2 5 6 204
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 28 220 3
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 44 236 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 916
cert_cover_5 6 1 1 3 6 7 148 916 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0536

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0537.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0537

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 589, 677, 569, 297, 457, 417, 150, 790, 838, 314, 178, 482, 660, 856, 688, 69, 133, 517, 41, 73, 265, 521, 161, 289, 545, 193, 385, 22, 70, 134, 774, 50, 146, 274, 162, 290, 194, 322, 148, 532, 580, 644, 56, 280, 536, 296, 328, 584, 176, 560, 656, 784, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_589, vertices_677, vertices_569, vertices_297, vertices_457, vertices_417, vertices_150, vertices_790, vertices_838, vertices_314, vertices_178, vertices_482, vertices_660, vertices_856, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_22, vertices_70, vertices_134, vertices_774, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_148, vertices_532, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_328, vertices_584, vertices_176, vertices_560, vertices_656, vertices_784, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_589), (false, vertices_677), (false, vertices_569), (false, vertices_297), (false, vertices_457), (false, vertices_417), (true, vertices_22), (true, vertices_774), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_148), (true, vertices_532), (true, vertices_280), (true, vertices_176), (true, vertices_656), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_774) then 18 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 297 1 417 22 50 146 274 162 290 322 148 532 280 176 656 784 832 199 774 589 677 569 457
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_4 2 0 2 3 4 7 314 50 1
cert_row_4 3 2 3 5 7 8 856 280 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 7 70 838 3
cert_coverFacet 3 314
cert_cover_5 3 2 0 2 3 4 50 314 1
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 162 482 2
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 280 856 2
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0537

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0538.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0538

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 309, 837, 361, 561, 737, 398, 526, 406, 234, 586, 722, 780, 440, 840, 688, 21, 261, 517, 49, 529, 97, 289, 545, 321, 577, 14, 22, 390, 518, 74, 138, 522, 146, 530, 194, 578, 268, 524, 276, 772, 104, 168, 296, 328, 584, 392, 776, 176, 304, 560, 400, 656, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_309, vertices_837, vertices_361, vertices_561, vertices_737, vertices_398, vertices_526, vertices_406, vertices_234, vertices_586, vertices_722, vertices_780, vertices_440, vertices_840, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_49, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_14, vertices_22, vertices_390, vertices_518, vertices_74, vertices_138, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_268, vertices_524, vertices_276, vertices_772, vertices_104, vertices_168, vertices_296, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_309), (false, vertices_837), (false, vertices_361), (false, vertices_561), (false, vertices_737), (true, vertices_14), (true, vertices_390), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_268), (true, vertices_524), (true, vertices_168), (true, vertices_584), (true, vertices_392), (true, vertices_776), (true, vertices_176), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 18 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_390) then 19 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 2 4 5 6 234 74 2
cert_row_4 3 2 3 4 6 7 440 168 1
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 22 406 3
cert_coverFacet 3 234
cert_cover_5 3 2 0 2 4 5 74 234 2
cert_coverFacet 4 586
cert_cover_2 4 2 0 5 8 74 586 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 6 146 722 2
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 168 440 1
cert_coverFacet 8 840
cert_cover_2 8 5 2 7 8 328 840 3
cert_coverFacet 9 688
cert_cover_2 9 4 3 6 8 176 688 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0538

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0539.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0539

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 43, 587, 419, 121, 225, 961, 286, 526, 314, 92, 716, 244, 660, 788, 944, 11, 35, 259, 515, 41, 73, 97, 161, 193, 577, 385, 769, 14, 262, 518, 282, 42, 522, 290, 28, 76, 524, 84, 148, 276, 532, 196, 644, 772, 56, 88, 584, 112, 176, 304, 656, 784, 224, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_43, vertices_587, vertices_419, vertices_121, vertices_225, vertices_961, vertices_286, vertices_526, vertices_314, vertices_92, vertices_716, vertices_244, vertices_660, vertices_788, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_41, vertices_73, vertices_97, vertices_161, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_518, vertices_282, vertices_42, vertices_522, vertices_290, vertices_28, vertices_76, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_56, vertices_88, vertices_584, vertices_112, vertices_176, vertices_304, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_43), (false, vertices_587), (false, vertices_419), (false, vertices_121), (false, vertices_225), (false, vertices_961), (true, vertices_14), (true, vertices_282), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_176), (true, vertices_304), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 16 22 24 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_587) then 19 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_282) then 21 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 282 314 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 76 716 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 84 244 2
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 944
cert_cover_5 8 3 3 4 6 7 176 944 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0539

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0540.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0540

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 613, 409, 689, 481, 833, 30, 46, 278, 550, 838, 666, 682, 348, 236, 456, 145, 273, 529, 97, 161, 545, 321, 577, 385, 769, 14, 22, 38, 262, 518, 26, 42, 650, 274, 530, 546, 770, 28, 44, 76, 276, 100, 548, 324, 580, 152, 280, 168, 200, 328, 392, 656, 224, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_613, vertices_409, vertices_689, vertices_481, vertices_833, vertices_30, vertices_46, vertices_278, vertices_550, vertices_838, vertices_666, vertices_682, vertices_348, vertices_236, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_650, vertices_274, vertices_530, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_276, vertices_100, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_168, vertices_200, vertices_328, vertices_392, vertices_656, vertices_224, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_613), (false, vertices_409), (false, vertices_689), (false, vertices_481), (false, vertices_833), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_650), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_276), (true, vertices_324), (true, vertices_168), (true, vertices_200), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_481) then 27 else
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
  if p.val = (true, vertices_76) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_324) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_200) then 15 else
  if p.val = (true, vertices_328) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 833 14 22 38 262 518 26 42 546 28 44 76 276 324 168 200 328 787 650 613 409 689 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 7 348 28 3
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_2 2 0 2 6 8 650
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
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
cert_cover_5 4 1 0 1 5 7 262 838 2
cert_coverFacet 5 666
cert_cover_5 5 2 0 2 3 6 26 666 3
cert_coverFacet 6 682
cert_cover_5 6 2 0 2 4 6 42 682 3
cert_coverFacet 7 348
cert_cover_5 7 0 1 2 3 5 28 348 3
cert_coverFacet 8 236
cert_cover_5 8 3 1 2 4 5 44 236 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0540

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0541.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0541

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 781, 613, 453, 409, 705, 566, 790, 58, 282, 170, 778, 738, 372, 248, 464, 69, 261, 517, 137, 265, 521, 193, 577, 385, 641, 534, 26, 42, 138, 266, 522, 50, 274, 162, 546, 642, 770, 52, 276, 100, 548, 324, 772, 56, 152, 280, 168, 776, 112, 208, 336, 400, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_781, vertices_613, vertices_453, vertices_409, vertices_705, vertices_566, vertices_790, vertices_58, vertices_282, vertices_170, vertices_778, vertices_738, vertices_372, vertices_248, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_641, vertices_534, vertices_26, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_546, vertices_642, vertices_770, vertices_52, vertices_276, vertices_100, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_781), (false, vertices_613), (false, vertices_453), (false, vertices_409), (false, vertices_705), (true, vertices_534), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_52), (true, vertices_276), (true, vertices_56), (true, vertices_168), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_409) then 25 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_534) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 705 26 42 266 50 274 162 546 770 52 276 56 168 112 208 336 224 651 534 781 613 453 409
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 7 372 52 3
cert_row_2 1 0 1 3 8 534
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 534 566 3
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 7 534 790 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 738
cert_cover_5 6 2 0 4 5 6 162 738 2
cert_coverFacet 7 372
cert_cover_5 7 0 1 3 4 5 52 372 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0541

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0542.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0542

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 659, 803, 901, 425, 241, 598, 618, 812, 332, 588, 340, 404, 660, 472, 232, 19, 35, 515, 113, 145, 161, 289, 385, 641, 769, 82, 530, 98, 546, 578, 76, 268, 524, 84, 148, 276, 532, 324, 580, 388, 644, 772, 104, 168, 296, 552, 200, 328, 584, 392, 208, 336, 400, 656, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_659, vertices_803, vertices_901, vertices_425, vertices_241, vertices_598, vertices_618, vertices_812, vertices_332, vertices_588, vertices_340, vertices_404, vertices_660, vertices_472, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_113, vertices_145, vertices_161, vertices_289, vertices_385, vertices_641, vertices_769, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_659), (false, vertices_803), (false, vertices_901), (false, vertices_425), (false, vertices_241), (true, vertices_578), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_580), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 25 else
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 6 7 472 200 1
cert_row_4 1 0 1 3 5 8 598 82 1
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 82 598 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 98 618 1
cert_coverFacet 2 812
cert_cover_5 2 3 1 2 4 7 268 812 2
cert_coverFacet 3 332
cert_cover_2 3 2 1 5 7 76 332 3
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 6 200 472 1
cert_coverFacet 9 232
cert_cover_2 9 4 2 5 6 104 232 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0542

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0543.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0543

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 653, 309, 597, 389, 217, 401, 806, 362, 906, 626, 564, 900, 488, 240, 432, 21, 133, 261, 517, 73, 137, 521, 81, 145, 273, 577, 385, 74, 266, 522, 98, 290, 546, 578, 770, 52, 532, 292, 548, 388, 644, 772, 360, 200, 392, 648, 112, 176, 304, 560, 208, 592, 400, 224, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_653, vertices_309, vertices_597, vertices_389, vertices_217, vertices_401, vertices_806, vertices_362, vertices_906, vertices_626, vertices_564, vertices_900, vertices_488, vertices_240, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_385, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_52, vertices_532, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_360, vertices_200, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_653), (false, vertices_309), (false, vertices_597), (false, vertices_389), (false, vertices_217), (false, vertices_401), (true, vertices_266), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_548), (true, vertices_772), (true, vertices_360), (true, vertices_392), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_360) then 24 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 6 7 8 906 266 2
cert_row_2 2 2 4 5 7 360
cert_row_4 3 0 3 4 5 8 626 98 1
cert_rows
cert_pivot_2 1 6 2 0
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 362
cert_cover_5 1 2 0 2 4 5 74 362 2
cert_coverFacet 2 906
cert_cover_5 2 1 0 2 6 7 266 906 2
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 98 626 1
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 6 360 488 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0543

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0544.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0544

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 565, 597, 229, 217, 281, 425, 678, 906, 562, 850, 418, 204, 844, 652, 344, 533, 37, 69, 25, 137, 265, 49, 81, 273, 161, 289, 193, 50, 274, 530, 162, 290, 546, 386, 642, 770, 76, 140, 524, 164, 548, 196, 580, 644, 88, 280, 200, 328, 392, 648, 776, 560, 336, 592, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_565, vertices_597, vertices_229, vertices_217, vertices_281, vertices_425, vertices_678, vertices_906, vertices_562, vertices_850, vertices_418, vertices_204, vertices_844, vertices_652, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_37, vertices_69, vertices_25, vertices_137, vertices_265, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_560, vertices_336, vertices_592, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_565), (false, vertices_597), (false, vertices_229), (false, vertices_217), (false, vertices_281), (false, vertices_425), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_328), (true, vertices_648), (true, vertices_776), (true, vertices_336), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 386 906 1
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 274 850 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 76 844 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0544

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0545.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0545

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 157, 269, 229, 837, 681, 777, 286, 538, 842, 690, 306, 354, 468, 664, 496, 13, 69, 133, 261, 137, 265, 521, 97, 161, 545, 577, 769, 26, 266, 522, 50, 274, 530, 98, 290, 546, 322, 578, 28, 268, 148, 276, 196, 324, 152, 536, 648, 776, 176, 304, 464, 656, 224, 352, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_157, vertices_269, vertices_229, vertices_837, vertices_681, vertices_777, vertices_286, vertices_538, vertices_842, vertices_690, vertices_306, vertices_354, vertices_468, vertices_664, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_577, vertices_769, vertices_26, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_28, vertices_268, vertices_148, vertices_276, vertices_196, vertices_324, vertices_152, vertices_536, vertices_648, vertices_776, vertices_176, vertices_304, vertices_464, vertices_656, vertices_224, vertices_352, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_157), (false, vertices_269), (false, vertices_229), (false, vertices_837), (false, vertices_681), (false, vertices_777), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_322), (true, vertices_276), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_464), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_322) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_464) then 25 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_2 2 3 5 6 7 464
cert_row_4 3 0 3 4 6 8 690 50 3
cert_rows
cert_pivot_2 1 2 5 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 266 842 2
cert_coverFacet 3 690
cert_cover_5 3 3 0 3 4 6 50 690 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 468
cert_cover_5 6 2 1 3 5 6 148 468 2
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 496
cert_cover_5 8 2 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0545

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0546.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0546

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 421, 645, 713, 465, 865, 46, 590, 58, 218, 818, 594, 316, 412, 652, 848, 37, 133, 517, 289, 545, 193, 321, 577, 385, 641, 14, 38, 518, 26, 42, 74, 50, 82, 530, 546, 578, 284, 44, 140, 524, 292, 388, 644, 56, 152, 200, 584, 648, 304, 208, 336, 592, 400, 784, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_421, vertices_645, vertices_713, vertices_465, vertices_865, vertices_46, vertices_590, vertices_58, vertices_218, vertices_818, vertices_594, vertices_316, vertices_412, vertices_652, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_38, vertices_518, vertices_26, vertices_42, vertices_74, vertices_50, vertices_82, vertices_530, vertices_546, vertices_578, vertices_284, vertices_44, vertices_140, vertices_524, vertices_292, vertices_388, vertices_644, vertices_56, vertices_152, vertices_200, vertices_584, vertices_648, vertices_304, vertices_208, vertices_336, vertices_592, vertices_400, vertices_784, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_421), (false, vertices_645), (false, vertices_713), (false, vertices_465), (false, vertices_865), (true, vertices_14), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_578), (true, vertices_284), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_56), (true, vertices_152), (true, vertices_304), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_284) then 21 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 6 218 26 3
cert_row_4 1 0 1 2 5 8 590 14 3
cert_row_2 2 1 2 3 7 284
cert_row_4 3 0 3 4 7 8 818 50 3
cert_rows
cert_pivot_2 6 5 1 0
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 5 14 590 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 218
cert_cover_5 3 0 0 2 3 5 26 218 3
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 50 818 3
cert_coverFacet 5 594
cert_cover_2 5 3 0 5 8 82 594 3
cert_coverFacet 6 316
cert_cover_5 6 2 1 2 3 4 284 316 3
cert_coverFacet 7 412
cert_cover_5 7 2 1 2 3 6 284 412 3
cert_coverFacet 8 652
cert_cover_2 8 2 1 6 8 140 652 3
cert_coverFacet 9 848
cert_cover_2 9 5 3 7 8 336 848 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0546

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0547.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0547

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 551, 587, 293, 457, 625, 353, 902, 282, 538, 914, 692, 484, 248, 600, 408, 7, 11, 515, 37, 261, 73, 265, 97, 289, 545, 321, 577, 262, 518, 26, 266, 522, 274, 530, 898, 164, 292, 548, 388, 644, 88, 152, 280, 536, 200, 584, 392, 112, 176, 560, 592, 400, 656, 224, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_551, vertices_587, vertices_293, vertices_457, vertices_625, vertices_353, vertices_902, vertices_282, vertices_538, vertices_914, vertices_692, vertices_484, vertices_248, vertices_600, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_37, vertices_261, vertices_73, vertices_265, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_898, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_392, vertices_112, vertices_176, vertices_560, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_551), (false, vertices_587), (false, vertices_293), (false, vertices_457), (false, vertices_625), (false, vertices_353), (true, vertices_26), (true, vertices_274), (true, vertices_530), (true, vertices_898), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_587) then 20 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_898) then 21 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 1 293 0 353 26 274 530 164 388 644 88 152 280 536 176 400 656 224 271 551 587 898 457 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 6 7 8 898
cert_row_4 1 1 3 4 6 8 692 164 1
cert_row_4 2 1 4 5 6 7 484 164 2
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 262 902 2
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 914
cert_cover_5 3 0 0 3 6 7 274 914 2
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 164 692 1
cert_coverFacet 5 484
cert_cover_5 5 2 1 4 5 6 164 484 2
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0547

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0548.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0548

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 179, 787, 781, 421, 369, 58, 538, 618, 738, 348, 716, 452, 120, 792, 480, 19, 131, 515, 133, 261, 517, 49, 273, 161, 289, 769, 26, 42, 522, 50, 530, 610, 162, 642, 76, 268, 524, 196, 324, 388, 644, 56, 88, 280, 536, 104, 584, 776, 112, 336, 784, 224, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_179, vertices_787, vertices_781, vertices_421, vertices_369, vertices_58, vertices_538, vertices_618, vertices_738, vertices_348, vertices_716, vertices_452, vertices_120, vertices_792, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_161, vertices_289, vertices_769, vertices_26, vertices_42, vertices_522, vertices_50, vertices_530, vertices_610, vertices_162, vertices_642, vertices_76, vertices_268, vertices_524, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_584, vertices_776, vertices_112, vertices_336, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_179), (false, vertices_787), (false, vertices_781), (false, vertices_421), (false, vertices_369), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_610), (true, vertices_76), (true, vertices_196), (true, vertices_324), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_584), (true, vertices_224), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_787) then 21 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_610) then 22 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_610), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_2 0 0 4 5 8 610
cert_row_4 1 1 2 3 5 7 348 76 2
cert_row_4 2 1 2 5 6 8 716 76 3
cert_rows_3
cert_pivot_3 3 0 1
cert_heightProof 3
cert_coverFacet 0 58
cert_cover_2 0 2 0 3 4 26 58 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 5 42 618 3
cert_coverFacet 3 738
cert_cover_5 3 0 0 4 5 6 610 738 3
cert_coverFacet 4 348
cert_cover_5 4 1 1 2 3 5 76 348 2
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 76 716 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 3 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0548

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0549.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0549

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 213, 789, 613, 809, 465, 158, 314, 170, 402, 738, 450, 540, 716, 792, 680, 21, 69, 517, 209, 273, 97, 289, 545, 321, 769, 26, 42, 138, 146, 274, 98, 162, 290, 194, 322, 386, 28, 140, 524, 148, 532, 196, 580, 280, 536, 168, 296, 552, 648, 776, 400, 784, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_213, vertices_789, vertices_613, vertices_809, vertices_465, vertices_158, vertices_314, vertices_170, vertices_402, vertices_738, vertices_450, vertices_540, vertices_716, vertices_792, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_209, vertices_273, vertices_97, vertices_289, vertices_545, vertices_321, vertices_769, vertices_26, vertices_42, vertices_138, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_140, vertices_524, vertices_148, vertices_532, vertices_196, vertices_580, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_400, vertices_784, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_213), (false, vertices_789), (false, vertices_613), (false, vertices_809), (false, vertices_465), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_194), (true, vertices_386), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_648), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_213) then 25 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_4 1 0 1 2 3 6 158 26 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 26 158 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 716
cert_cover_5 7 3 1 2 5 6 140 716 2
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coverFacet 9 680
cert_cover_2 9 4 2 6 8 168 680 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0549

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0550.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0550

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 285, 901, 537, 425, 713, 118, 806, 234, 722, 674, 372, 344, 600, 360, 928, 21, 261, 517, 25, 137, 265, 521, 529, 385, 641, 22, 38, 518, 82, 530, 98, 162, 546, 194, 642, 116, 276, 292, 772, 88, 280, 536, 104, 168, 296, 200, 328, 584, 336, 592, 352, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_285, vertices_901, vertices_537, vertices_425, vertices_713, vertices_118, vertices_806, vertices_234, vertices_722, vertices_674, vertices_372, vertices_344, vertices_600, vertices_360, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_529, vertices_385, vertices_641, vertices_22, vertices_38, vertices_518, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_116, vertices_276, vertices_292, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_336, vertices_592, vertices_352, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_285), (false, vertices_901), (false, vertices_537), (false, vertices_425), (false, vertices_713), (true, vertices_38), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_116), (true, vertices_292), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_336), (true, vertices_592), (true, vertices_352), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 18 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_116) then 22 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 4 7 8 806 38 3
cert_row_2 1 1 3 4 5 116
cert_row_4 2 0 2 4 5 6 234 98 1
cert_row_4 3 0 3 5 6 8 722 82 3
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 22 118 3
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 38 806 3
cert_coverFacet 2 234
cert_cover_5 2 2 0 2 4 5 98 234 1
cert_coverFacet 3 722
cert_cover_5 3 3 0 3 5 6 82 722 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 372
cert_cover_5 5 1 1 3 4 7 116 372 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coverFacet 9 928
cert_cover_2 9 6 4 7 8 416 928 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0550

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0551.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0551

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 555, 291, 613, 601, 465, 353, 678, 778, 482, 898, 412, 540, 908, 244, 596, 11, 35, 259, 25, 521, 81, 273, 97, 289, 545, 321, 577, 266, 522, 162, 290, 546, 386, 642, 770, 28, 396, 524, 84, 148, 532, 100, 164, 548, 580, 644, 280, 536, 776, 208, 592, 400, 224, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_555, vertices_291, vertices_613, vertices_601, vertices_465, vertices_353, vertices_678, vertices_778, vertices_482, vertices_898, vertices_412, vertices_540, vertices_908, vertices_244, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_25, vertices_521, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_396, vertices_524, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_280, vertices_536, vertices_776, vertices_208, vertices_592, vertices_400, vertices_224, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_555), (false, vertices_291), (false, vertices_613), (false, vertices_601), (false, vertices_465), (false, vertices_353), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_28), (true, vertices_396), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_776), (true, vertices_224), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 17 else
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_396) then 21 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 291 1 353 162 386 642 770 28 524 84 148 532 164 644 776 224 896 283 555 613 396 601 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 482
cert_cover_5 2 2 0 4 5 6 162 482 2
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 412
cert_cover_5 4 0 1 2 3 6 28 412 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 908
cert_cover_5 6 0 1 2 6 8 396 908 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 84 244 2
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0551

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0552.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0552

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 541, 341, 901, 281, 425, 118, 566, 582, 234, 554, 962, 836, 312, 568, 496, 21, 261, 517, 25, 137, 265, 521, 273, 385, 641, 54, 70, 518, 42, 138, 522, 98, 546, 194, 578, 642, 84, 532, 324, 580, 772, 56, 280, 536, 168, 296, 552, 112, 304, 560, 336, 224, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_541, vertices_341, vertices_901, vertices_281, vertices_425, vertices_118, vertices_566, vertices_582, vertices_234, vertices_554, vertices_962, vertices_836, vertices_312, vertices_568, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_273, vertices_385, vertices_641, vertices_54, vertices_70, vertices_518, vertices_42, vertices_138, vertices_522, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_112, vertices_304, vertices_560, vertices_336, vertices_224, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_541), (false, vertices_341), (false, vertices_901), (false, vertices_281), (false, vertices_425), (true, vertices_54), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_580), (true, vertices_56), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_224), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_901) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (true, vertices_54) then 19 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_448) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 281 70 518 42 98 546 194 578 580 56 552 112 304 560 224 448 832 651 54 541 341 901 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 4 5 6 234 42 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 5 54 118 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 5 42 234 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 194 962 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0552

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0553.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0553

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 781, 661, 389, 457, 737, 182, 122, 794, 658, 610, 674, 308, 788, 484, 376, 133, 261, 517, 73, 265, 521, 193, 577, 385, 641, 26, 74, 522, 50, 146, 530, 98, 162, 546, 578, 642, 52, 148, 276, 532, 164, 292, 388, 772, 120, 280, 328, 776, 304, 656, 784, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_781, vertices_661, vertices_389, vertices_457, vertices_737, vertices_182, vertices_122, vertices_794, vertices_658, vertices_610, vertices_674, vertices_308, vertices_788, vertices_484, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_74, vertices_522, vertices_50, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_388, vertices_772, vertices_120, vertices_280, vertices_328, vertices_776, vertices_304, vertices_656, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_781), (false, vertices_661), (false, vertices_389), (false, vertices_457), (false, vertices_737), (true, vertices_26), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_120), (true, vertices_280), (true, vertices_304), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_120) then 24 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
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
cert_row_4 0 0 2 3 7 8 794 26 3
cert_row_2 1 2 3 4 5 120
cert_row_4 2 0 1 3 4 6 182 50 1
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 2 0 1 3 4 50 182 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 26 122 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 26 794 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 164 484 2
cert_coverFacet 9 376
cert_cover_5 9 1 2 3 4 7 120 376 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0553

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0554.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0554

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 285, 301, 181, 233, 585, 721, 790, 282, 618, 298, 482, 834, 660, 420, 964, 269, 21, 37, 25, 41, 73, 521, 145, 529, 161, 193, 577, 26, 42, 266, 522, 274, 530, 98, 290, 322, 578, 770, 148, 276, 532, 164, 292, 388, 644, 772, 280, 104, 296, 584, 656, 224, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_285, vertices_301, vertices_181, vertices_233, vertices_585, vertices_721, vertices_790, vertices_282, vertices_618, vertices_298, vertices_482, vertices_834, vertices_660, vertices_420, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_21, vertices_37, vertices_25, vertices_41, vertices_73, vertices_521, vertices_145, vertices_529, vertices_161, vertices_193, vertices_577, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_280, vertices_104, vertices_296, vertices_584, vertices_656, vertices_224, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_285), (false, vertices_301), (false, vertices_181), (false, vertices_233), (false, vertices_585), (false, vertices_721), (true, vertices_42), (true, vertices_266), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 5 6 7 8 964 388 1
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 5 42 618 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 98 482 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 964
cert_cover_5 8 3 1 5 6 7 388 964 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0554

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0555.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0555

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 781, 341, 149, 677, 329, 721, 806, 186, 218, 298, 778, 738, 436, 312, 344, 21, 133, 261, 517, 73, 265, 521, 81, 145, 321, 577, 641, 154, 42, 74, 266, 522, 162, 290, 546, 194, 578, 770, 148, 276, 164, 292, 548, 772, 56, 88, 280, 296, 328, 776, 176, 304, 208, 336, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_781, vertices_341, vertices_149, vertices_677, vertices_329, vertices_721, vertices_806, vertices_186, vertices_218, vertices_298, vertices_778, vertices_738, vertices_436, vertices_312, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_154, vertices_42, vertices_74, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_770, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_781), (false, vertices_341), (false, vertices_149), (false, vertices_677), (false, vertices_329), (false, vertices_721), (true, vertices_154), (true, vertices_42), (true, vertices_266), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_770), (true, vertices_292), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 149 1 329 42 266 162 290 546 194 770 292 56 88 280 296 176 304 587 154 781 341 677 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 1 4 7 8 806 290 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 290 806 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 154 186 3
cert_coverFacet 2 218
cert_cover_5 2 0 0 2 3 5 154 218 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 148 436 2
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0555

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0556.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0556

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 171, 299, 787, 421, 837, 602, 282, 650, 716, 244, 356, 184, 312, 216, 880, 43, 131, 259, 515, 133, 261, 517, 161, 289, 769, 26, 138, 266, 522, 274, 530, 642, 100, 164, 292, 196, 324, 580, 644, 56, 88, 152, 280, 168, 296, 200, 584, 648, 112, 176, 304, 208, 592, 784, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_171, vertices_299, vertices_787, vertices_421, vertices_837, vertices_602, vertices_282, vertices_650, vertices_716, vertices_244, vertices_356, vertices_184, vertices_312, vertices_216, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_131, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_642, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_784, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_171), (false, vertices_299), (false, vertices_787), (false, vertices_421), (false, vertices_837), (true, vertices_26), (true, vertices_522), (true, vertices_100), (true, vertices_196), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 21 17 25 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_171) then 22 else
  if p.val = (false, vertices_299) then 23 else
  if p.val = (false, vertices_787) then 24 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 0
  | 22 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 25 => Sum.inl 2
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 1 2 5 6 8 716 196 1
cert_row_4 2 1 3 4 5 6 244 100 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 26 602 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 196 716 1
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 100 244 1
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 880
cert_cover_5 9 3 3 4 5 7 112 880 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0556

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0557.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0557

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 93, 405, 325, 713, 657, 481, 286, 302, 554, 434, 658, 738, 556, 588, 868, 21, 69, 261, 25, 73, 521, 145, 529, 193, 321, 385, 641, 270, 26, 42, 522, 146, 274, 530, 162, 290, 546, 642, 28, 44, 76, 524, 276, 292, 548, 324, 580, 552, 584, 400, 656, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_93, vertices_405, vertices_325, vertices_713, vertices_657, vertices_481, vertices_286, vertices_302, vertices_554, vertices_434, vertices_658, vertices_738, vertices_556, vertices_588, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_25, vertices_73, vertices_521, vertices_145, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_270, vertices_26, vertices_42, vertices_522, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_276, vertices_292, vertices_548, vertices_324, vertices_580, vertices_552, vertices_584, vertices_400, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_93), (false, vertices_405), (false, vertices_325), (false, vertices_713), (false, vertices_657), (false, vertices_481), (true, vertices_270), (true, vertices_42), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_270) then 18 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 325 0 657 42 146 274 162 290 546 642 44 524 292 548 580 552 608 539 270 93 405 713 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 3 4 6 7 434 146 2
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 270 302 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 6 146 434 2
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 292 868 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0557

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0558.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0558

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 29, 781, 217, 361, 657, 961, 182, 550, 810, 914, 482, 92, 108, 556, 244, 13, 21, 517, 25, 73, 265, 145, 529, 193, 321, 641, 769, 22, 38, 518, 146, 530, 162, 290, 546, 386, 770, 28, 44, 76, 524, 180, 84, 100, 548, 88, 104, 296, 552, 776, 208, 656, 224, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_29, vertices_781, vertices_217, vertices_361, vertices_657, vertices_961, vertices_182, vertices_550, vertices_810, vertices_914, vertices_482, vertices_92, vertices_108, vertices_556, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_25, vertices_73, vertices_265, vertices_145, vertices_529, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_180, vertices_84, vertices_100, vertices_548, vertices_88, vertices_104, vertices_296, vertices_552, vertices_776, vertices_208, vertices_656, vertices_224, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_29), (false, vertices_781), (false, vertices_217), (false, vertices_361), (false, vertices_657), (false, vertices_961), (true, vertices_38), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_770), (true, vertices_44), (true, vertices_76), (true, vertices_180), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_552), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 24 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_180) then 20 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_100) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 6 180
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 3 6 7 8 914 146 3
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 22 182 3
cert_coverFacet 1 550
cert_cover_2 1 1 0 4 8 38 550 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 290 810 1
cert_coverFacet 3 914
cert_cover_5 3 2 0 3 6 7 146 914 3
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 162 482 2
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 244
cert_cover_5 8 0 1 3 4 5 180 244 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0558

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4413 : Certifies 4413 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0529.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4414 : Certifies 4414 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0530.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4415 : Certifies 4415 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0531.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4416 : Certifies 4416 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0532.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4417 : Certifies 4417 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0533.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4418 : Certifies 4418 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0534.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4419 : Certifies 4419 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0535.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4420 : Certifies 4420 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0536.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4421 : Certifies 4421 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0537.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4422 : Certifies 4422 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0538.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4423 : Certifies 4423 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0539.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4424 : Certifies 4424 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0540.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4425 : Certifies 4425 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0541.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4426 : Certifies 4426 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0542.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4427 : Certifies 4427 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0543.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4428 : Certifies 4428 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0544.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4429 : Certifies 4429 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0545.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4430 : Certifies 4430 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0546.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4431 : Certifies 4431 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0547.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4432 : Certifies 4432 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0548.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4433 : Certifies 4433 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0549.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4434 : Certifies 4434 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0550.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4435 : Certifies 4435 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0551.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4436 : Certifies 4436 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0552.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4437 : Certifies 4437 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0553.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4438 : Certifies 4438 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0554.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4439 : Certifies 4439 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0555.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4440 : Certifies 4440 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0556.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4441 : Certifies 4441 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0557.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4442 : Certifies 4442 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0558.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B146 (j : Fin 30) :
    Certifies (4413 + j.val) := by
  fin_cases j
  · exact projection_4413
  · exact projection_4414
  · exact projection_4415
  · exact projection_4416
  · exact projection_4417
  · exact projection_4418
  · exact projection_4419
  · exact projection_4420
  · exact projection_4421
  · exact projection_4422
  · exact projection_4423
  · exact projection_4424
  · exact projection_4425
  · exact projection_4426
  · exact projection_4427
  · exact projection_4428
  · exact projection_4429
  · exact projection_4430
  · exact projection_4431
  · exact projection_4432
  · exact projection_4433
  · exact projection_4434
  · exact projection_4435
  · exact projection_4436
  · exact projection_4437
  · exact projection_4438
  · exact projection_4439
  · exact projection_4440
  · exact projection_4441
  · exact projection_4442

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
