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
/- Source: ProjectionCertificates/R_m15e10q0_0045.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 157, 557, 901, 121, 721, 782, 314, 554, 482, 706, 898, 284, 468, 368, 13, 133, 517, 25, 41, 81, 145, 97, 545, 577, 641, 42, 266, 522, 98, 290, 546, 194, 578, 386, 642, 770, 28, 268, 524, 148, 276, 388, 772, 56, 280, 552, 112, 304, 208, 336, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_157, vertices_557, vertices_901, vertices_121, vertices_721, vertices_782, vertices_314, vertices_554, vertices_482, vertices_706, vertices_898, vertices_284, vertices_468, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_41, vertices_81, vertices_145, vertices_97, vertices_545, vertices_577, vertices_641, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_388, vertices_772, vertices_56, vertices_280, vertices_552, vertices_112, vertices_304, vertices_208, vertices_336, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_157), (false, vertices_557), (false, vertices_901), (false, vertices_121), (false, vertices_721), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_280), (true, vertices_304), (true, vertices_336), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 42 1 266 522 290 194 386 642 770 268 276 280 304 336 352 448 611 157 557 901 121 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 3 4 7 314 42 2
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 42 314 2
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 98 482 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 148 468 2
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0045

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q0_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 403, 355, 547, 213, 613, 457, 666, 930, 124, 540, 812, 216, 360, 904, 19, 35, 259, 515, 21, 69, 517, 145, 97, 545, 193, 321, 385, 146, 530, 290, 546, 386, 642, 28, 44, 524, 84, 532, 100, 548, 88, 152, 536, 104, 296, 200, 328, 392, 648, 776, 208, 352, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_403, vertices_355, vertices_547, vertices_213, vertices_613, vertices_457, vertices_666, vertices_930, vertices_124, vertices_540, vertices_812, vertices_216, vertices_360, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_21, vertices_69, vertices_517, vertices_145, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_146, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_524, vertices_84, vertices_532, vertices_100, vertices_548, vertices_88, vertices_152, vertices_536, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_208, vertices_352, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_403), (false, vertices_355), (false, vertices_547), (false, vertices_213), (false, vertices_613), (false, vertices_457), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_296), (true, vertices_648), (true, vertices_776), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 1 2 3 4 5 124 28 3
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 1 0 2 3 6 146 666 1
cert_coverFacet 1 930
cert_cover_5 1 2 0 4 6 7 290 930 2
cert_coverFacet 2 124
cert_cover_5 2 0 1 2 3 4 28 124 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 812
cert_cover_5 4 3 1 2 4 7 44 812 3
cert_coverFacet 5 216
cert_cover_2 5 3 2 5 6 88 216 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0046

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 453, 681, 585, 625, 433, 337, 334, 782, 678, 198, 650, 820, 420, 856, 73, 137, 521, 49, 81, 273, 161, 545, 193, 321, 577, 385, 270, 70, 134, 518, 74, 138, 522, 194, 642, 164, 292, 548, 196, 324, 388, 772, 328, 584, 648, 776, 304, 560, 336, 592, 784, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_453, vertices_681, vertices_585, vertices_625, vertices_433, vertices_337, vertices_334, vertices_782, vertices_678, vertices_198, vertices_650, vertices_820, vertices_420, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_49, vertices_81, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_270, vertices_70, vertices_134, vertices_518, vertices_74, vertices_138, vertices_522, vertices_194, vertices_642, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_388, vertices_772, vertices_328, vertices_584, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_453), (false, vertices_681), (false, vertices_585), (false, vertices_625), (false, vertices_433), (false, vertices_337), (true, vertices_270), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_522), (true, vertices_642), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_328), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 134 2
cert_row_2 1 0 1 2 7 270
cert_row_4 2 1 3 4 7 8 820 292 1
cert_row_4 3 2 3 5 7 8 856 328 1
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 270 334 3
cert_coverFacet 1 782
cert_cover_5 1 1 0 1 2 8 270 782 3
cert_coverFacet 2 678
cert_cover_5 2 0 0 1 4 6 134 678 2
cert_coverFacet 3 198
cert_cover_2 3 1 0 5 6 70 198 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 820
cert_cover_5 5 2 1 3 4 7 292 820 1
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 328 856 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0000

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 355, 163, 579, 597, 425, 465, 838, 810, 674, 220, 540, 460, 780, 696, 35, 67, 131, 515, 81, 145, 529, 161, 289, 321, 577, 385, 162, 290, 546, 322, 578, 642, 770, 28, 204, 268, 524, 84, 532, 324, 580, 772, 152, 536, 168, 296, 552, 392, 776, 208, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_355, vertices_163, vertices_579, vertices_597, vertices_425, vertices_465, vertices_838, vertices_810, vertices_674, vertices_220, vertices_540, vertices_460, vertices_780, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_515, vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_204, vertices_268, vertices_524, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_355), (false, vertices_163), (false, vertices_579), (false, vertices_597), (false, vertices_425), (false, vertices_465), (true, vertices_546), (true, vertices_770), (true, vertices_28), (true, vertices_204), (true, vertices_268), (true, vertices_524), (true, vertices_324), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 163 579 546 770 28 268 524 324 772 152 536 552 776 672 659 355 597 204 425 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 6 8 696 152 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 5 7 8 838 322 1
cert_row_4 3 0 2 4 7 8 810 290 1
cert_rows
cert_pivot_2 3 6 1 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 2 0 1 5 7 322 838 1
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 290 810 1
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 220
cert_cover_5 3 1 1 2 3 5 28 220 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 7 204 460 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 696
cert_cover_5 7 0 2 3 4 6 152 696 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0001

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 341, 149, 421, 665, 457, 593, 806, 234, 554, 850, 482, 684, 660, 788, 21, 133, 261, 73, 137, 521, 81, 145, 529, 321, 577, 385, 42, 74, 522, 226, 290, 546, 322, 578, 770, 148, 276, 532, 164, 292, 548, 644, 772, 168, 552, 200, 648, 336, 592, 656, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_341, vertices_149, vertices_421, vertices_665, vertices_457, vertices_593, vertices_806, vertices_234, vertices_554, vertices_850, vertices_482, vertices_684, vertices_660, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_42, vertices_74, vertices_522, vertices_226, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_168, vertices_552, vertices_200, vertices_648, vertices_336, vertices_592, vertices_656, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_341), (false, vertices_149), (false, vertices_421), (false, vertices_665), (false, vertices_457), (false, vertices_593), (true, vertices_42), (true, vertices_226), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_168), (true, vertices_552), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_226) then 16 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 149 1 593 42 290 546 322 770 532 548 644 772 168 552 784 587 226 341 421 665 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 322 1
cert_row_2 1 0 4 5 6 226
cert_row_4 2 0 1 4 7 8 806 290 1
cert_row_4 3 1 2 4 6 8 684 164 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 290 806 1
cert_coverFacet 1 234
cert_cover_5 1 1 0 2 4 5 42 234 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 850
cert_cover_5 3 0 0 3 5 7 322 850 1
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 7 226 482 3
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 164 684 1
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0002

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 403, 323, 643, 333, 793, 689, 454, 706, 108, 812, 244, 820, 404, 744, 67, 131, 259, 515, 73, 265, 521, 145, 273, 529, 321, 641, 194, 322, 578, 386, 642, 44, 76, 268, 52, 148, 276, 100, 804, 196, 324, 388, 104, 552, 584, 776, 176, 560, 400, 784, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_403, vertices_323, vertices_643, vertices_333, vertices_793, vertices_689, vertices_454, vertices_706, vertices_108, vertices_812, vertices_244, vertices_820, vertices_404, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_321, vertices_641, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_44, vertices_76, vertices_268, vertices_52, vertices_148, vertices_276, vertices_100, vertices_804, vertices_196, vertices_324, vertices_388, vertices_104, vertices_552, vertices_584, vertices_776, vertices_176, vertices_560, vertices_400, vertices_784, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_403), (false, vertices_323), (false, vertices_643), (false, vertices_333), (false, vertices_793), (false, vertices_689), (true, vertices_194), (true, vertices_44), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_804), (true, vertices_196), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_804) then 19 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 323 643 194 44 52 148 276 100 196 388 104 552 224 704 587 403 333 804 793 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_2 1 1 4 7 8 804
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 820
cert_cover_5 5 1 1 3 4 7 52 820 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0003

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 613, 409, 369, 721, 673, 110, 142, 678, 362, 394, 668, 844, 792, 848, 81, 145, 273, 97, 161, 289, 545, 577, 385, 641, 14, 38, 134, 106, 138, 266, 162, 290, 386, 76, 140, 524, 100, 548, 580, 644, 152, 280, 536, 328, 392, 776, 336, 592, 656, 784, 352, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_613, vertices_409, vertices_369, vertices_721, vertices_673, vertices_110, vertices_142, vertices_678, vertices_362, vertices_394, vertices_668, vertices_844, vertices_792, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_14, vertices_38, vertices_134, vertices_106, vertices_138, vertices_266, vertices_162, vertices_290, vertices_386, vertices_76, vertices_140, vertices_524, vertices_100, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_328, vertices_392, vertices_776, vertices_336, vertices_592, vertices_656, vertices_784, vertices_352, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_613), (false, vertices_409), (false, vertices_369), (false, vertices_721), (false, vertices_673), (true, vertices_14), (true, vertices_38), (true, vertices_134), (true, vertices_106), (true, vertices_138), (true, vertices_266), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_536), (true, vertices_328), (true, vertices_776), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 673 14 38 134 138 266 76 140 524 644 536 328 776 784 832 419 106 613 409 369 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 8 668 140 2
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_2 2 0 2 4 5 106
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 2 0 1 2 4 14 110 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 362
cert_cover_5 3 2 0 2 4 7 106 362 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 668
cert_cover_5 5 0 1 2 3 6 140 668 2
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 76 844 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0004

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 803, 323, 301, 333, 121, 689, 454, 714, 898, 188, 204, 932, 600, 664, 67, 259, 515, 269, 41, 73, 49, 81, 529, 289, 545, 321, 194, 322, 578, 386, 642, 770, 44, 76, 140, 164, 292, 196, 324, 388, 56, 88, 152, 536, 200, 584, 648, 176, 592, 656, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_803, vertices_323, vertices_301, vertices_333, vertices_121, vertices_689, vertices_454, vertices_714, vertices_898, vertices_188, vertices_204, vertices_932, vertices_600, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_269, vertices_41, vertices_73, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_152, vertices_536, vertices_200, vertices_584, vertices_648, vertices_176, vertices_592, vertices_656, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_803), (false, vertices_323), (false, vertices_301), (false, vertices_333), (false, vertices_121), (false, vertices_689), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 6 188 44 2
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 1 5 6 7 454 194 1
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 2 0 1 5 6 194 454 1
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 194 714 1
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 4 44 188 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 932
cert_cover_5 5 3 1 4 6 7 164 932 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0005

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 781, 405, 709, 281, 689, 838, 58, 362, 778, 562, 738, 452, 248, 472, 133, 261, 517, 25, 265, 521, 145, 273, 529, 641, 26, 42, 266, 522, 50, 530, 98, 546, 322, 578, 770, 196, 324, 580, 388, 772, 56, 216, 280, 104, 328, 776, 176, 560, 400, 224, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_781, vertices_405, vertices_709, vertices_281, vertices_689, vertices_838, vertices_58, vertices_362, vertices_778, vertices_562, vertices_738, vertices_452, vertices_248, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_216, vertices_280, vertices_104, vertices_328, vertices_776, vertices_176, vertices_560, vertices_400, vertices_224, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_781), (false, vertices_405), (false, vertices_709), (false, vertices_281), (false, vertices_689), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_324), (true, vertices_56), (true, vertices_216), (true, vertices_104), (true, vertices_328), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_216) then 22 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 0 4 5 6 8 738 98 3
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 42 362 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 738
cert_cover_5 5 3 0 4 5 6 98 738 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 56 248 3
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 7 216 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0006

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0007.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0007

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 179, 563, 835, 805, 361, 169, 598, 210, 428, 692, 340, 404, 836, 472, 51, 67, 131, 515, 41, 73, 137, 161, 289, 545, 321, 769, 82, 146, 530, 194, 578, 84, 148, 276, 532, 164, 292, 548, 324, 580, 388, 772, 168, 296, 200, 328, 392, 176, 560, 208, 336, 400, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_179, vertices_563, vertices_835, vertices_805, vertices_361, vertices_169, vertices_598, vertices_210, vertices_428, vertices_692, vertices_340, vertices_404, vertices_836, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_67, vertices_131, vertices_515, vertices_41, vertices_73, vertices_137, vertices_161, vertices_289, vertices_545, vertices_321, vertices_769, vertices_82, vertices_146, vertices_530, vertices_194, vertices_578, vertices_84, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_179), (false, vertices_563), (false, vertices_835), (false, vertices_805), (false, vertices_361), (false, vertices_169), (true, vertices_82), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_392), (true, vertices_208), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 14 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_563) then 21 else
  if p.val = (false, vertices_835) then 22 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 1 169 0 82 2 84 148 276 532 164 324 580 388 392 208 336 400 805 203 361 179 563 835
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 1 3 4 6 8 692 148 2
cert_row_4 2 1 2 4 6 7 428 164 1
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 210
cert_cover_2 1 3 0 5 6 82 210 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 164 428 1
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 148 692 2
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 200 472 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0007

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 557, 789, 165, 361, 777, 433, 598, 710, 338, 402, 482, 676, 856, 744, 21, 37, 133, 517, 41, 265, 521, 145, 273, 161, 289, 769, 22, 582, 134, 82, 146, 274, 194, 322, 386, 532, 164, 548, 644, 104, 552, 328, 584, 776, 336, 592, 400, 784, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_557, vertices_789, vertices_165, vertices_361, vertices_777, vertices_433, vertices_598, vertices_710, vertices_338, vertices_402, vertices_482, vertices_676, vertices_856, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_161, vertices_289, vertices_769, vertices_22, vertices_582, vertices_134, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_532, vertices_164, vertices_548, vertices_644, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_557), (false, vertices_789), (false, vertices_165), (false, vertices_361), (false, vertices_777), (false, vertices_433), (true, vertices_582), (true, vertices_82), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_644), (true, vertices_584), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_582) then 16 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 165 1 777 82 274 194 322 386 644 584 336 592 224 672 704 151 582 557 789 361 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 2 3 5 7 8 856 328 1
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 582 710 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 194 482 1
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 328 856 1
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0008

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 661, 713, 817, 465, 110, 590, 566, 354, 802, 316, 156, 652, 408, 488, 145, 273, 529, 193, 321, 577, 641, 769, 78, 38, 518, 98, 290, 546, 322, 578, 770, 28, 44, 140, 524, 52, 148, 532, 644, 152, 280, 104, 296, 200, 584, 392, 648, 304, 560, 400, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_661, vertices_713, vertices_817, vertices_465, vertices_110, vertices_590, vertices_566, vertices_354, vertices_802, vertices_316, vertices_156, vertices_652, vertices_408, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_78, vertices_38, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_52, vertices_148, vertices_532, vertices_644, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_400, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_661), (false, vertices_713), (false, vertices_817), (false, vertices_465), (true, vertices_78), (true, vertices_38), (true, vertices_518), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_392), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_78) then 18 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 38 2
cert_row_2 1 0 1 2 5 78
cert_row_4 2 1 2 3 4 7 316 28 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 78 110 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 8 78 590 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 38 566 2
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 316
cert_cover_5 5 2 1 2 3 4 28 316 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 104 488 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0009

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 709, 793, 681, 457, 118, 614, 570, 338, 786, 428, 308, 468, 676, 312, 137, 265, 521, 193, 321, 577, 641, 769, 102, 50, 82, 274, 530, 546, 322, 578, 770, 52, 84, 276, 164, 292, 548, 196, 580, 388, 644, 56, 280, 536, 168, 296, 552, 392, 304, 336, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_709, vertices_793, vertices_681, vertices_457, vertices_118, vertices_614, vertices_570, vertices_338, vertices_786, vertices_428, vertices_308, vertices_468, vertices_676, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_102, vertices_50, vertices_82, vertices_274, vertices_530, vertices_546, vertices_322, vertices_578, vertices_770, vertices_52, vertices_84, vertices_276, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_304, vertices_336, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_709), (false, vertices_793), (false, vertices_681), (false, vertices_457), (true, vertices_102), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_56), (true, vertices_296), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 50 1
cert_row_2 1 0 1 4 5 102
cert_row_4 2 1 2 4 6 7 428 164 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 102 118 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 8 102 614 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 50 570 1
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 428
cert_cover_5 5 2 1 2 4 6 164 428 1
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 84 468 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coverFacet 9 312
cert_cover_2 9 3 2 4 7 56 312 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0010

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 587, 163, 643, 709, 457, 433, 678, 794, 818, 604, 244, 564, 344, 464, 11, 35, 131, 515, 73, 265, 161, 289, 193, 577, 385, 641, 266, 522, 786, 162, 290, 546, 642, 52, 84, 532, 164, 548, 196, 580, 644, 88, 280, 536, 328, 584, 176, 304, 560, 208, 336, 400, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_587, vertices_163, vertices_643, vertices_709, vertices_457, vertices_433, vertices_678, vertices_794, vertices_818, vertices_604, vertices_244, vertices_564, vertices_344, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_131, vertices_515, vertices_73, vertices_265, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_266, vertices_522, vertices_786, vertices_162, vertices_290, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_587), (false, vertices_163), (false, vertices_643), (false, vertices_709), (false, vertices_457), (false, vertices_433), (true, vertices_786), (true, vertices_546), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_786) then 17 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 163 643 546 52 84 532 164 548 88 280 536 560 208 336 299 587 786 709 457 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 1 2 3 5 8 604 84 1
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 266 794 2
cert_coverFacet 2 818
cert_cover_5 2 0 0 3 4 7 786 818 2
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 84 604 1
cert_coverFacet 4 244
cert_cover_5 4 3 1 3 4 5 52 244 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0011

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 661, 421, 553, 737, 790, 122, 538, 778, 466, 482, 404, 728, 616, 133, 261, 517, 41, 265, 521, 161, 289, 545, 641, 26, 42, 266, 522, 82, 274, 530, 98, 290, 450, 770, 148, 276, 532, 388, 772, 88, 536, 104, 552, 584, 776, 208, 400, 656, 224, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_661, vertices_421, vertices_553, vertices_737, vertices_790, vertices_122, vertices_538, vertices_778, vertices_466, vertices_482, vertices_404, vertices_728, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_450, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_88, vertices_536, vertices_104, vertices_552, vertices_584, vertices_776, vertices_208, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_661), (false, vertices_421), (false, vertices_553), (false, vertices_737), (true, vertices_26), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_450), (true, vertices_770), (true, vertices_276), (true, vertices_88), (true, vertices_536), (true, vertices_104), (true, vertices_584), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_450) then 17 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 26 122 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 82 466 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 98 482 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0012

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 789, 185, 809, 561, 465, 270, 526, 598, 454, 234, 618, 780, 340, 752, 41, 137, 265, 49, 145, 273, 529, 545, 385, 769, 14, 70, 262, 518, 106, 138, 266, 522, 194, 578, 386, 268, 524, 84, 276, 532, 324, 772, 168, 552, 776, 176, 560, 208, 336, 592, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_789, vertices_185, vertices_809, vertices_561, vertices_465, vertices_270, vertices_526, vertices_598, vertices_454, vertices_234, vertices_618, vertices_780, vertices_340, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_49, vertices_145, vertices_273, vertices_529, vertices_545, vertices_385, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_106, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_168, vertices_552, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_789), (false, vertices_185), (false, vertices_809), (false, vertices_561), (false, vertices_465), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_324), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 561 14 70 262 518 522 194 578 268 524 84 324 592 224 608 395 106 789 185 809 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 0 1 3 5 8 598 70 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 2 7 0 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 70 598 2
cert_coverFacet 3 454
cert_cover_5 3 1 0 1 5 6 70 454 3
cert_coverFacet 4 234
cert_cover_5 4 0 0 2 4 6 106 234 3
cert_coverFacet 5 618
cert_cover_5 5 0 0 2 4 8 106 618 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0013

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0014.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0014

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 395, 227, 611, 185, 809, 598, 454, 284, 540, 780, 340, 568, 472, 752, 99, 131, 259, 515, 41, 137, 265, 161, 545, 769, 70, 262, 518, 194, 578, 386, 28, 268, 524, 84, 276, 532, 324, 772, 56, 152, 280, 536, 552, 392, 776, 176, 560, 208, 336, 592, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_395, vertices_227, vertices_611, vertices_185, vertices_809, vertices_598, vertices_454, vertices_284, vertices_540, vertices_780, vertices_340, vertices_568, vertices_472, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_131, vertices_259, vertices_515, vertices_41, vertices_137, vertices_265, vertices_161, vertices_545, vertices_769, vertices_70, vertices_262, vertices_518, vertices_194, vertices_578, vertices_386, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_552, vertices_392, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_395), (false, vertices_227), (false, vertices_611), (false, vertices_185), (false, vertices_809), (true, vertices_70), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 15 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_611) then 20 else
  if p.val = (false, vertices_185) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 1 70 0 28 2 268 524 84 276 532 324 280 536 560 208 336 592 448 775 395 227 611 185 809
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 6 7 472 152 2
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 0 1 3 5 8 598 70 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 2 7 0 3
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 70 598 2
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 472
cert_cover_5 7 0 2 3 5 6 152 472 2
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0014

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 781, 229, 421, 313, 617, 214, 646, 794, 626, 402, 898, 900, 568, 496, 165, 69, 261, 517, 41, 265, 521, 97, 289, 577, 70, 134, 518, 82, 146, 274, 530, 578, 386, 642, 770, 196, 388, 644, 772, 56, 280, 536, 552, 776, 112, 304, 560, 208, 400, 224, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_781, vertices_229, vertices_421, vertices_313, vertices_617, vertices_214, vertices_646, vertices_794, vertices_626, vertices_402, vertices_898, vertices_900, vertices_568, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_577, vertices_70, vertices_134, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_578, vertices_386, vertices_642, vertices_770, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_781), (false, vertices_229), (false, vertices_421), (false, vertices_313), (false, vertices_617), (true, vertices_134), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_536), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 134 1 82 2 146 274 530 386 642 770 644 536 112 560 208 400 896 583 781 229 421 313 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 70 2
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 70 214 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 794
cert_cover_5 2 1 0 2 3 7 274 794 1
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 82 626 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0015

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 781, 661, 389, 425, 585, 737, 790, 58, 282, 842, 242, 722, 436, 312, 133, 261, 517, 41, 73, 265, 521, 97, 161, 577, 385, 641, 26, 42, 74, 266, 50, 210, 274, 530, 98, 578, 770, 148, 276, 532, 388, 772, 56, 280, 296, 584, 776, 176, 304, 656, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_781, vertices_661, vertices_389, vertices_425, vertices_585, vertices_737, vertices_790, vertices_58, vertices_282, vertices_842, vertices_242, vertices_722, vertices_436, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_74, vertices_266, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_56, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_781), (false, vertices_661), (false, vertices_389), (false, vertices_425), (false, vertices_585), (false, vertices_737), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 389 1 585 26 266 50 274 530 578 770 276 56 280 176 304 107 210 781 661 425 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 842
cert_cover_5 3 0 0 2 5 7 74 842 3
cert_coverFacet 4 242
cert_cover_5 4 1 0 3 4 5 50 242 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 8 210 722 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 148 436 2
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0017

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 789, 357, 709, 121, 601, 902, 154, 794, 650, 178, 482, 452, 184, 744, 69, 261, 517, 89, 49, 273, 529, 97, 289, 577, 26, 138, 522, 50, 146, 274, 162, 290, 386, 642, 770, 196, 324, 388, 644, 772, 56, 152, 536, 104, 168, 584, 648, 176, 784, 224, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_789, vertices_357, vertices_709, vertices_121, vertices_601, vertices_902, vertices_154, vertices_794, vertices_650, vertices_178, vertices_482, vertices_452, vertices_184, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_89, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_26, vertices_138, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_584, vertices_648, vertices_176, vertices_784, vertices_224, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_789), (false, vertices_357), (false, vertices_709), (false, vertices_121), (false, vertices_601), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_648), (true, vertices_176), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 26 1 138 2 522 146 162 386 642 770 388 152 168 648 176 224 448 307 789 357 709 121 601
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 794
cert_cover_5 2 1 0 2 3 7 26 794 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 482
cert_cover_5 5 2 0 4 5 6 162 482 2
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0018

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 357, 677, 713, 465, 609, 654, 310, 566, 602, 282, 394, 216, 408, 880, 37, 133, 261, 97, 545, 193, 321, 577, 385, 641, 54, 134, 262, 518, 26, 138, 266, 522, 274, 530, 386, 292, 548, 644, 88, 152, 280, 200, 584, 392, 648, 304, 560, 208, 336, 592, 400, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_357, vertices_677, vertices_713, vertices_465, vertices_609, vertices_654, vertices_310, vertices_566, vertices_602, vertices_282, vertices_394, vertices_216, vertices_408, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_292, vertices_548, vertices_644, vertices_88, vertices_152, vertices_280, vertices_200, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_357), (false, vertices_677), (false, vertices_713), (false, vertices_465), (false, vertices_609), (true, vertices_54), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_304), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_54) then 17 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 609 518 26 138 266 522 274 530 88 152 280 392 304 560 592 391 54 357 677 713 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 0 1 3 4 54
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 6 1 0 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 310
cert_cover_5 1 1 0 1 3 7 54 310 3
cert_coverFacet 2 566
cert_cover_5 2 1 0 1 3 8 54 566 3
cert_coverFacet 3 602
cert_cover_5 3 2 0 2 3 5 26 602 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 304 880 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0019

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 333, 565, 789, 229, 617, 182, 714, 394, 818, 402, 674, 468, 456, 736, 533, 37, 69, 261, 73, 265, 521, 97, 545, 769, 138, 266, 522, 50, 146, 274, 162, 546, 386, 642, 770, 52, 148, 276, 164, 196, 324, 200, 328, 584, 392, 560, 400, 784, 224, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_333, vertices_565, vertices_789, vertices_229, vertices_617, vertices_182, vertices_714, vertices_394, vertices_818, vertices_402, vertices_674, vertices_468, vertices_456, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_37, vertices_69, vertices_261, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_769, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_276, vertices_164, vertices_196, vertices_324, vertices_200, vertices_328, vertices_584, vertices_392, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_333), (false, vertices_565), (false, vertices_789), (false, vertices_229), (false, vertices_617), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_200), (true, vertices_392), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_229) then 23 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 138 1 50 2 146 274 162 546 386 642 148 200 392 400 672 448 704 779 333 617 565 789 229
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 0 1 3 4 6 182 50 1
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 2 0 1 3 4 50 182 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 138 714 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 818
cert_cover_5 3 1 0 3 4 7 50 818 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 148 468 2
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0020

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0021.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0021

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 309, 229, 709, 121, 849, 654, 422, 794, 394, 184, 600, 408, 744, 432, 37, 197, 261, 517, 49, 81, 273, 97, 577, 769, 134, 262, 518, 138, 266, 522, 386, 770, 164, 292, 644, 56, 88, 152, 280, 536, 104, 168, 584, 392, 648, 176, 304, 592, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_309, vertices_229, vertices_709, vertices_121, vertices_849, vertices_654, vertices_422, vertices_794, vertices_394, vertices_184, vertices_600, vertices_408, vertices_744, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_197, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_97, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_386, vertices_770, vertices_164, vertices_292, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_592, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_309), (false, vertices_229), (false, vertices_709), (false, vertices_121), (false, vertices_849), (true, vertices_134), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 134 1 138 266 522 386 152 280 536 168 584 392 648 176 400 416 775 309 229 709 121 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 1 2 6 8 654 134 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 7 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 422
cert_cover_5 1 1 0 1 4 6 134 422 2
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 266 794 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0021

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 397, 181, 805, 561, 465, 782, 602, 458, 338, 236, 620, 688, 720, 736, 37, 133, 261, 49, 145, 273, 529, 545, 385, 769, 74, 266, 522, 82, 274, 530, 322, 770, 108, 140, 268, 524, 164, 548, 772, 200, 584, 392, 176, 560, 208, 336, 592, 656, 224, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_397, vertices_181, vertices_805, vertices_561, vertices_465, vertices_782, vertices_602, vertices_458, vertices_338, vertices_236, vertices_620, vertices_688, vertices_720, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_49, vertices_145, vertices_273, vertices_529, vertices_545, vertices_385, vertices_769, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_108, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_772, vertices_200, vertices_584, vertices_392, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_397), (false, vertices_181), (false, vertices_805), (false, vertices_561), (false, vertices_465), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_322), (true, vertices_108), (true, vertices_524), (true, vertices_200), (true, vertices_584), (true, vertices_592), (true, vertices_656), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 561 1 74 2 266 3 522 82 322 524 200 584 592 656 224 608 672 704 787 397 108 181 805 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 3 5 8 602 74 2
cert_row_4 3 0 2 5 6 7 458 74 3
cert_rows
cert_pivot_2 4 1 3 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 74 602 2
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 74 458 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 6 108 236 3
cert_coverFacet 5 620
cert_cover_5 5 0 1 2 4 8 108 620 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0022

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 405, 677, 837, 553, 585, 481, 790, 58, 538, 842, 242, 466, 660, 696, 133, 261, 517, 41, 73, 521, 97, 161, 545, 321, 577, 385, 26, 42, 74, 522, 50, 210, 274, 530, 98, 322, 770, 148, 276, 532, 644, 772, 56, 536, 552, 584, 176, 400, 656, 224, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_405, vertices_677, vertices_837, vertices_553, vertices_585, vertices_481, vertices_790, vertices_58, vertices_538, vertices_842, vertices_242, vertices_466, vertices_660, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_56, vertices_536, vertices_552, vertices_584, vertices_176, vertices_400, vertices_656, vertices_224, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_405), (false, vertices_677), (false, vertices_837), (false, vertices_553), (false, vertices_585), (false, vertices_481), (true, vertices_26), (true, vertices_522), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_770), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_176), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_2 2 0 3 5 6 210
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 74 842 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 50 242 3
cert_coverFacet 5 466
cert_cover_5 5 2 0 3 5 7 210 466 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 56 696 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0023

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 597, 645, 361, 113, 433, 961, 30, 526, 902, 186, 426, 842, 124, 588, 21, 133, 517, 49, 81, 145, 97, 289, 321, 577, 385, 641, 14, 22, 134, 518, 26, 170, 266, 522, 146, 386, 770, 28, 76, 524, 84, 580, 644, 56, 104, 296, 328, 584, 112, 176, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_597, vertices_645, vertices_361, vertices_113, vertices_433, vertices_961, vertices_30, vertices_526, vertices_902, vertices_186, vertices_426, vertices_842, vertices_124, vertices_588] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_49, vertices_81, vertices_145, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_22, vertices_134, vertices_518, vertices_26, vertices_170, vertices_266, vertices_522, vertices_146, vertices_386, vertices_770, vertices_28, vertices_76, vertices_524, vertices_84, vertices_580, vertices_644, vertices_56, vertices_104, vertices_296, vertices_328, vertices_584, vertices_112, vertices_176, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_597), (false, vertices_645), (false, vertices_361), (false, vertices_113), (false, vertices_433), (false, vertices_961), (true, vertices_14), (true, vertices_518), (true, vertices_26), (true, vertices_170), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_56), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 15 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_170) then 16 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_584) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 5 124 28 3
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 0 2 5 7 8 842 266 2
cert_rows
cert_pivot_2 3 4 1 0
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 134 902 3
cert_coverFacet 3 186
cert_cover_5 3 1 0 2 3 4 26 186 3
cert_coverFacet 4 426
cert_cover_5 4 1 0 2 4 7 170 426 3
cert_coverFacet 5 842
cert_cover_5 5 3 0 2 5 7 266 842 2
cert_coverFacet 6 124
cert_cover_5 6 0 1 2 3 4 28 124 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0024

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0025.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 23, 563, 333, 405, 665, 393, 310, 358, 582, 738, 588, 968, 496, 688, 7, 19, 515, 13, 21, 261, 137, 265, 521, 145, 529, 385, 22, 294, 70, 518, 50, 98, 546, 578, 76, 524, 276, 324, 580, 328, 584, 392, 648, 176, 304, 560, 400, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_23, vertices_563, vertices_333, vertices_405, vertices_665, vertices_393, vertices_310, vertices_358, vertices_582, vertices_738, vertices_588, vertices_968, vertices_496, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_515, vertices_13, vertices_21, vertices_261, vertices_137, vertices_265, vertices_521, vertices_145, vertices_529, vertices_385, vertices_22, vertices_294, vertices_70, vertices_518, vertices_50, vertices_98, vertices_546, vertices_578, vertices_76, vertices_524, vertices_276, vertices_324, vertices_580, vertices_328, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_23), (false, vertices_563), (false, vertices_333), (false, vertices_405), (false, vertices_665), (false, vertices_393), (true, vertices_294), (true, vertices_70), (true, vertices_98), (true, vertices_578), (true, vertices_580), (true, vertices_584), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_352), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_23) then 0 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_23), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_2 0 0 1 4 7 294
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_4 2 2 5 6 7 8 968 328 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 5 294 358 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 738
cert_cover_5 3 1 0 4 5 6 98 738 3
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 968
cert_cover_5 5 2 2 5 6 7 328 968 2
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 176 496 2
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0025

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0026.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0026

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 557, 397, 181, 617, 481, 662, 602, 394, 650, 370, 402, 652, 628, 432, 13, 37, 133, 553, 73, 265, 97, 161, 321, 385, 74, 138, 266, 522, 82, 146, 274, 530, 322, 386, 642, 140, 524, 52, 148, 532, 548, 644, 584, 392, 648, 112, 176, 304, 592, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_557, vertices_397, vertices_181, vertices_617, vertices_481, vertices_662, vertices_602, vertices_394, vertices_650, vertices_370, vertices_402, vertices_652, vertices_628, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_553, vertices_73, vertices_265, vertices_97, vertices_161, vertices_321, vertices_385, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_386, vertices_642, vertices_140, vertices_524, vertices_52, vertices_148, vertices_532, vertices_548, vertices_644, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_557), (false, vertices_397), (false, vertices_181), (false, vertices_617), (false, vertices_481), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_532), (true, vertices_644), (true, vertices_648), (true, vertices_112), (true, vertices_304), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 3 4 5 7 370 82 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 370
cert_cover_5 4 2 0 3 4 5 82 370 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0026

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0027.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0027

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 901, 665, 841, 241, 481, 30, 526, 54, 422, 838, 586, 370, 188, 652, 25, 73, 521, 81, 145, 225, 321, 385, 641, 769, 14, 22, 38, 262, 518, 26, 74, 522, 50, 82, 290, 322, 578, 28, 140, 524, 52, 164, 388, 644, 772, 152, 584, 648, 112, 176, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_901, vertices_665, vertices_841, vertices_241, vertices_481, vertices_30, vertices_526, vertices_54, vertices_422, vertices_838, vertices_586, vertices_370, vertices_188, vertices_652] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_521, vertices_81, vertices_145, vertices_225, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_262, vertices_518, vertices_26, vertices_74, vertices_522, vertices_50, vertices_82, vertices_290, vertices_322, vertices_578, vertices_28, vertices_140, vertices_524, vertices_52, vertices_164, vertices_388, vertices_644, vertices_772, vertices_152, vertices_584, vertices_648, vertices_112, vertices_176, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_901), (false, vertices_665), (false, vertices_841), (false, vertices_241), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_164)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_578) then 9 else
  if p.val = (true, vertices_28) then 10 else
  if p.val = (true, vertices_140) then 11 else
  if p.val = (true, vertices_524) then 12 else
  if p.val = (true, vertices_52) then 13 else
  if p.val = (true, vertices_164) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 262 2
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 1 4 6 7 422 38 3
cert_row_4 3 1 2 3 4 6 188 28 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 54
cert_cover_2 2 1 0 3 4 22 54 3
cert_coverFacet 3 422
cert_cover_5 3 2 0 1 4 6 38 422 3
cert_coverFacet 4 838
cert_cover_5 4 0 0 1 5 7 262 838 2
cert_coverFacet 5 586
cert_cover_2 5 2 0 5 8 74 586 3
cert_coverFacet 6 370
cert_cover_5 6 1 0 3 4 5 50 370 3
cert_coverFacet 7 188
cert_cover_5 7 3 1 2 3 4 28 188 3
cert_coverFacet 8 652
cert_cover_2 8 2 1 6 8 140 652 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0027

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 395, 835, 345, 681, 585, 182, 790, 402, 124, 852, 740, 184, 408, 616, 131, 259, 515, 73, 137, 265, 521, 321, 577, 641, 22, 134, 518, 146, 274, 386, 770, 52, 84, 788, 100, 164, 580, 644, 56, 88, 152, 280, 104, 168, 552, 584, 392, 176, 336, 400, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_395, vertices_835, vertices_345, vertices_681, vertices_585, vertices_182, vertices_790, vertices_402, vertices_124, vertices_852, vertices_740, vertices_184, vertices_408, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_22, vertices_134, vertices_518, vertices_146, vertices_274, vertices_386, vertices_770, vertices_52, vertices_84, vertices_788, vertices_100, vertices_164, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_552, vertices_584, vertices_392, vertices_176, vertices_336, vertices_400, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_395), (false, vertices_835), (false, vertices_345), (false, vertices_681), (false, vertices_585), (true, vertices_22), (true, vertices_146), (true, vertices_274), (true, vertices_52), (true, vertices_84), (true, vertices_788), (true, vertices_100), (true, vertices_164), (true, vertices_580), (true, vertices_56), (true, vertices_152), (true, vertices_104), (true, vertices_176), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_788) then 20 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 7 8 788
cert_row_4 1 0 1 3 4 6 182 22 3
cert_row_4 2 1 2 3 4 5 124 52 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 22 182 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 52 124 1
cert_coverFacet 4 852
cert_cover_5 4 0 1 3 5 7 84 852 3
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 100 740 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0028

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2613 : Certifies 2613 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0045.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2614 : Certifies 2614 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2615 : Certifies 2615 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2616 : Certifies 2616 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2617 : Certifies 2617 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2618 : Certifies 2618 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2619 : Certifies 2619 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2620 : Certifies 2620 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2621 : Certifies 2621 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2622 : Certifies 2622 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0007.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2623 : Certifies 2623 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2624 : Certifies 2624 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2625 : Certifies 2625 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2626 : Certifies 2626 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2627 : Certifies 2627 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2628 : Certifies 2628 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2629 : Certifies 2629 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0014.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2630 : Certifies 2630 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2631 : Certifies 2631 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2632 : Certifies 2632 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2633 : Certifies 2633 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2634 : Certifies 2634 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2635 : Certifies 2635 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0021.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2636 : Certifies 2636 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2637 : Certifies 2637 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2638 : Certifies 2638 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2639 : Certifies 2639 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0025.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2640 : Certifies 2640 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0026.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2641 : Certifies 2641 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0027.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2642 : Certifies 2642 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B086 (j : Fin 30) :
    Certifies (2613 + j.val) := by
  fin_cases j
  · exact projection_2613
  · exact projection_2614
  · exact projection_2615
  · exact projection_2616
  · exact projection_2617
  · exact projection_2618
  · exact projection_2619
  · exact projection_2620
  · exact projection_2621
  · exact projection_2622
  · exact projection_2623
  · exact projection_2624
  · exact projection_2625
  · exact projection_2626
  · exact projection_2627
  · exact projection_2628
  · exact projection_2629
  · exact projection_2630
  · exact projection_2631
  · exact projection_2632
  · exact projection_2633
  · exact projection_2634
  · exact projection_2635
  · exact projection_2636
  · exact projection_2637
  · exact projection_2638
  · exact projection_2639
  · exact projection_2640
  · exact projection_2641
  · exact projection_2642

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
