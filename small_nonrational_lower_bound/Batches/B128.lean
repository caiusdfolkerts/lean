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
/- Source: ProjectionCertificates/R_m15e11q2_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 57, 601, 361, 689, 206, 334, 678, 774, 722, 412, 436, 312, 216, 25, 41, 73, 49, 529, 289, 545, 321, 577, 769, 78, 134, 262, 518, 194, 322, 578, 642, 770, 140, 268, 404, 164, 292, 548, 772, 56, 88, 152, 280, 296, 200, 328, 176, 304, 208, 592, 656, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_57, vertices_601, vertices_361, vertices_689, vertices_206, vertices_334, vertices_678, vertices_774, vertices_722, vertices_412, vertices_436, vertices_312, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_49, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_78, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_140, vertices_268, vertices_404, vertices_164, vertices_292, vertices_548, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_296, vertices_200, vertices_328, vertices_176, vertices_304, vertices_208, vertices_592, vertices_656, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_57), (false, vertices_601), (false, vertices_361), (false, vertices_689), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_404), (true, vertices_164), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_304), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 1 3 6 7 404
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 1 4 6 8 678 134 2
cert_row_4 3 0 3 5 6 8 722 194 1
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 7 78 334 3
cert_coverFacet 2 678
cert_cover_5 2 2 0 1 4 6 134 678 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 194 722 1
cert_coverFacet 5 412
cert_cover_5 5 0 1 2 3 6 140 412 2
cert_coverFacet 6 436
cert_cover_5 6 0 1 3 4 6 404 436 2
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0071

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e11q2_0072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 51, 803, 707, 357, 241, 833, 542, 566, 650, 412, 812, 116, 468, 968, 19, 35, 131, 515, 49, 145, 97, 289, 193, 321, 577, 769, 534, 26, 138, 522, 50, 546, 642, 28, 268, 524, 52, 84, 404, 100, 292, 548, 324, 152, 392, 648, 776, 112, 208, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_51, vertices_803, vertices_707, vertices_357, vertices_241, vertices_833, vertices_542, vertices_566, vertices_650, vertices_412, vertices_812, vertices_116, vertices_468, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_49, vertices_145, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_769, vertices_534, vertices_26, vertices_138, vertices_522, vertices_50, vertices_546, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_84, vertices_404, vertices_100, vertices_292, vertices_548, vertices_324, vertices_152, vertices_392, vertices_648, vertices_776, vertices_112, vertices_208, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_51), (false, vertices_803), (false, vertices_707), (false, vertices_357), (false, vertices_241), (false, vertices_833), (true, vertices_534), (true, vertices_522), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_404), (true, vertices_548), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 22 13 24 15 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_241) then 18 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_534) then 21 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_404) then 23 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 15 => Sum.inl 4
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_534), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 8 534
cert_row_2 1 1 3 6 7 404
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 2 5 6 7 8 968 392 1
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 534 542 2
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 4 534 566 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 412
cert_cover_5 3 1 1 2 3 6 28 412 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 268 812 2
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 468
cert_cover_5 6 1 1 3 5 6 84 468 3
cert_coverFacet 7 968
cert_cover_5 7 3 2 5 6 7 392 968 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0072

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e11q2_0073.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0073

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 789, 457, 241, 337, 929, 110, 398, 118, 534, 902, 554, 650, 348, 744, 49, 81, 273, 529, 161, 545, 193, 321, 385, 769, 14, 22, 102, 390, 518, 42, 138, 522, 50, 530, 546, 642, 76, 268, 84, 276, 532, 772, 104, 552, 200, 328, 392, 648, 112, 336, 224, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_789, vertices_457, vertices_241, vertices_337, vertices_929, vertices_110, vertices_398, vertices_118, vertices_534, vertices_902, vertices_554, vertices_650, vertices_348, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_14, vertices_22, vertices_102, vertices_390, vertices_518, vertices_42, vertices_138, vertices_522, vertices_50, vertices_530, vertices_546, vertices_642, vertices_76, vertices_268, vertices_84, vertices_276, vertices_532, vertices_772, vertices_104, vertices_552, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_336, vertices_224, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_789), (false, vertices_457), (false, vertices_241), (false, vertices_337), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_390), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_642), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_104), (true, vertices_552), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 23 25 14 16 20 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_457) then 15 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 22 else
  if p.val = (true, vertices_390) then 24 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_648) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 23 => Sum.inl 0
  | 24 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 25 => Sum.inl 1
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 7 348 76 2
cert_row_2 1 0 1 6 7 390
cert_row_2 2 0 1 4 5 102
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 7 0 2
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 2 0 1 2 4 14 110 3
cert_coverFacet 1 398
cert_cover_5 1 1 0 1 2 6 14 398 3
cert_coverFacet 2 118
cert_cover_5 2 2 0 1 3 4 22 118 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 902
cert_cover_5 4 1 0 1 6 8 390 902 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 650
cert_cover_2 6 2 0 6 8 138 650 3
cert_coverFacet 7 348
cert_cover_5 7 0 1 2 3 5 76 348 2
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0073

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e11q2_0074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 901, 57, 89, 425, 713, 865, 158, 790, 422, 186, 850, 354, 604, 652, 25, 41, 73, 137, 49, 81, 97, 289, 577, 385, 641, 769, 22, 134, 262, 154, 50, 82, 786, 98, 162, 290, 322, 28, 140, 524, 532, 388, 644, 772, 56, 88, 168, 584, 648, 592, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_901, vertices_57, vertices_89, vertices_425, vertices_713, vertices_865, vertices_158, vertices_790, vertices_422, vertices_186, vertices_850, vertices_354, vertices_604, vertices_652] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_137, vertices_49, vertices_81, vertices_97, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_262, vertices_154, vertices_50, vertices_82, vertices_786, vertices_98, vertices_162, vertices_290, vertices_322, vertices_28, vertices_140, vertices_524, vertices_532, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_168, vertices_584, vertices_648, vertices_592, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_901), (false, vertices_57), (false, vertices_89), (false, vertices_425), (false, vertices_713), (false, vertices_865), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_154), (true, vertices_786), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_532), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 22 13 19 24 15 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_89) then 1 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_865) then 18 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_262) then 4 else
  if p.val = (true, vertices_154) then 21 else
  if p.val = (true, vertices_786) then 23 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_89), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 15 => Sum.inl 4
  | 16 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 22 => Sum.inl 0
  | 23 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_2 1 0 2 3 6 154
cert_row_2 2 0 3 7 8 786
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 22 158 2
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 134 422 2
cert_coverFacet 3 186
cert_cover_5 3 1 0 2 3 4 154 186 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 28 604 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0074

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e11q2_0076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 789, 709, 817, 481, 590, 58, 218, 554, 434, 706, 572, 284, 472, 69, 261, 517, 785, 161, 289, 545, 193, 321, 641, 26, 42, 74, 522, 50, 146, 162, 546, 194, 578, 642, 28, 76, 268, 524, 276, 532, 580, 56, 216, 280, 552, 328, 304, 560, 400, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_789, vertices_709, vertices_817, vertices_481, vertices_590, vertices_58, vertices_218, vertices_554, vertices_434, vertices_706, vertices_572, vertices_284, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_785, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_146, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_580, vertices_56, vertices_216, vertices_280, vertices_552, vertices_328, vertices_304, vertices_560, vertices_400, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_789), (false, vertices_709), (false, vertices_817), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_524), (true, vertices_56), (true, vertices_216), (true, vertices_280), (true, vertices_552), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_216) then 20 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_2 1 2 3 5 6 216
cert_row_4 2 0 1 2 5 8 590 74 1
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 74 590 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 26 218 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 50 434 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 284
cert_cover_2 7 2 1 3 7 28 284 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 7 216 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0076

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e11q2_0077.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 779, 659, 195, 569, 281, 465, 230, 646, 774, 620, 844, 692, 440, 488, 67, 131, 259, 515, 25, 265, 521, 145, 273, 529, 193, 321, 70, 134, 262, 518, 194, 642, 770, 588, 100, 164, 548, 324, 644, 772, 56, 280, 104, 424, 552, 328, 776, 176, 560, 400, 656, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_779, vertices_659, vertices_195, vertices_569, vertices_281, vertices_465, vertices_230, vertices_646, vertices_774, vertices_620, vertices_844, vertices_692, vertices_440, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_25, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_70, vertices_134, vertices_262, vertices_518, vertices_194, vertices_642, vertices_770, vertices_588, vertices_100, vertices_164, vertices_548, vertices_324, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_424, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_400, vertices_656, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_779), (false, vertices_659), (false, vertices_195), (false, vertices_569), (false, vertices_281), (false, vertices_465), (true, vertices_134), (true, vertices_518), (true, vertices_588), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_424), (true, vertices_328), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_588) then 18 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_424) then 21 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 7 424
cert_row_2 1 1 2 5 8 588
cert_row_4 2 0 1 4 5 6 230 70 2
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 2 0 1 4 5 70 230 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 588 620 2
cert_coverFacet 4 844
cert_cover_5 4 1 1 2 5 7 588 844 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 164 692 1
cert_coverFacet 6 440
cert_cover_5 6 0 2 3 4 6 56 440 3
cert_coverFacet 7 488
cert_cover_5 7 0 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0077

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e11q2_0078.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 541, 301, 837, 665, 457, 806, 314, 346, 242, 674, 834, 60, 692, 216, 13, 261, 517, 537, 137, 265, 193, 321, 577, 641, 282, 50, 82, 162, 290, 546, 194, 322, 578, 642, 770, 28, 44, 52, 532, 292, 548, 772, 56, 88, 152, 296, 200, 328, 176, 208, 656, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_541, vertices_301, vertices_837, vertices_665, vertices_457, vertices_806, vertices_314, vertices_346, vertices_242, vertices_674, vertices_834, vertices_60, vertices_692, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_537, vertices_137, vertices_265, vertices_193, vertices_321, vertices_577, vertices_641, vertices_282, vertices_50, vertices_82, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_52, vertices_532, vertices_292, vertices_548, vertices_772, vertices_56, vertices_88, vertices_152, vertices_296, vertices_200, vertices_328, vertices_176, vertices_208, vertices_656, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_541), (false, vertices_301), (false, vertices_837), (false, vertices_665), (false, vertices_457), (true, vertices_282), (true, vertices_50), (true, vertices_82), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_52), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_176), (true, vertices_208), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_282) then 16 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 282 314 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 282 346 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 60
cert_cover_2 6 2 1 3 4 28 60 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 52 692 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0078

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e11q2_0079.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0079

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 789, 681, 241, 337, 961, 110, 398, 118, 534, 902, 554, 650, 348, 488, 49, 81, 273, 529, 161, 545, 193, 321, 641, 769, 14, 22, 102, 390, 518, 42, 138, 522, 50, 530, 546, 642, 76, 268, 84, 276, 532, 772, 104, 168, 552, 328, 392, 648, 112, 336, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_789, vertices_681, vertices_241, vertices_337, vertices_961, vertices_110, vertices_398, vertices_118, vertices_534, vertices_902, vertices_554, vertices_650, vertices_348, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_390, vertices_518, vertices_42, vertices_138, vertices_522, vertices_50, vertices_530, vertices_546, vertices_642, vertices_76, vertices_268, vertices_84, vertices_276, vertices_532, vertices_772, vertices_104, vertices_168, vertices_552, vertices_328, vertices_392, vertices_648, vertices_112, vertices_336, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_789), (false, vertices_681), (false, vertices_241), (false, vertices_337), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_390), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_642), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_104), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 22 24 14 16 20 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_681) then 15 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 21 else
  if p.val = (true, vertices_390) then 23 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_392) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 22 => Sum.inl 0
  | 23 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 24 => Sum.inl 1
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 7 348 76 2
cert_row_4 1 2 4 5 6 7 488 104 3
cert_row_2 2 0 1 6 7 390
cert_row_2 3 0 1 4 5 102
cert_rows
cert_pivot_2 3 2 6 0
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 3 0 1 2 4 14 110 3
cert_coverFacet 1 398
cert_cover_5 1 2 0 1 2 6 14 398 3
cert_coverFacet 2 118
cert_cover_5 2 3 0 1 3 4 22 118 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 902
cert_cover_5 4 2 0 1 6 8 390 902 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 650
cert_cover_2 6 2 0 6 8 138 650 3
cert_coverFacet 7 348
cert_cover_5 7 0 1 2 3 5 76 348 2
cert_coverFacet 8 488
cert_cover_5 8 1 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0079

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e11q2_0080.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0080

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 339, 707, 653, 233, 361, 790, 626, 412, 780, 180, 564, 740, 440, 368, 67, 259, 515, 105, 137, 265, 521, 193, 321, 641, 82, 274, 530, 578, 770, 140, 268, 524, 52, 148, 276, 532, 164, 548, 644, 772, 408, 168, 296, 776, 112, 176, 304, 560, 336, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_339, vertices_707, vertices_653, vertices_233, vertices_361, vertices_790, vertices_626, vertices_412, vertices_780, vertices_180, vertices_564, vertices_740, vertices_440, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_105, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_644, vertices_772, vertices_408, vertices_168, vertices_296, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_339), (false, vertices_707), (false, vertices_653), (false, vertices_233), (false, vertices_361), (true, vertices_530), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_408), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 626
cert_cover_5 1 2 0 3 4 5 82 626 2
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 140 412 2
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 440
cert_cover_5 7 0 2 3 4 6 408 440 2
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0080

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e11q2_0081.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0081

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 157, 301, 789, 233, 241, 561, 662, 362, 114, 562, 210, 962, 716, 844, 13, 21, 261, 41, 137, 49, 145, 529, 225, 289, 545, 769, 50, 82, 146, 530, 98, 290, 546, 194, 322, 642, 770, 588, 140, 268, 148, 532, 644, 772, 104, 296, 200, 328, 112, 560, 208, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_157, vertices_301, vertices_789, vertices_233, vertices_241, vertices_561, vertices_662, vertices_362, vertices_114, vertices_562, vertices_210, vertices_962, vertices_716, vertices_844] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_41, vertices_137, vertices_49, vertices_145, vertices_529, vertices_225, vertices_289, vertices_545, vertices_769, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_642, vertices_770, vertices_588, vertices_140, vertices_268, vertices_148, vertices_532, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_328, vertices_112, vertices_560, vertices_208, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_157), (false, vertices_301), (false, vertices_789), (false, vertices_233), (false, vertices_241), (false, vertices_561), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_588), (true, vertices_644), (true, vertices_328), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 21 15 22 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_588) then 20 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 1 2 5 8 588
cert_row_4 2 0 2 4 5 7 362 98 1
cert_row_4 3 0 5 6 7 8 962 194 3
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 362
cert_cover_5 1 2 0 2 4 5 98 362 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 962
cert_cover_5 5 3 0 5 6 7 194 962 3
cert_coverFacet 6 716
cert_cover_5 6 1 1 2 5 6 588 716 3
cert_coverFacet 7 844
cert_cover_5 7 1 1 2 5 7 588 844 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0081

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e11q2_0082.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0082

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 309, 405, 709, 457, 865, 62, 662, 90, 554, 842, 722, 440, 216, 808, 277, 37, 133, 517, 289, 545, 193, 321, 577, 385, 22, 38, 518, 26, 42, 74, 522, 82, 658, 546, 578, 52, 148, 644, 56, 88, 152, 296, 552, 200, 328, 392, 776, 304, 208, 400, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_309, vertices_405, vertices_709, vertices_457, vertices_865, vertices_62, vertices_662, vertices_90, vertices_554, vertices_842, vertices_722, vertices_440, vertices_216, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_37, vertices_133, vertices_517, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_22, vertices_38, vertices_518, vertices_26, vertices_42, vertices_74, vertices_522, vertices_82, vertices_658, vertices_546, vertices_578, vertices_52, vertices_148, vertices_644, vertices_56, vertices_88, vertices_152, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_304, vertices_208, vertices_400, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_309), (false, vertices_405), (false, vertices_709), (false, vertices_457), (false, vertices_865), (true, vertices_22), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_658), (true, vertices_578), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_658) then 16 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 4 62 22 2
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_2 2 0 3 6 8 658
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 22 62 2
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 90
cert_cover_2 2 2 0 3 5 26 90 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 842
cert_cover_5 4 1 0 2 5 7 74 842 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 82 722 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 56 440 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0082

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e11q2_0083.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0083

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 285, 541, 837, 617, 425, 449, 662, 122, 602, 178, 962, 436, 900, 312, 29, 261, 517, 41, 265, 521, 97, 161, 193, 321, 577, 385, 90, 50, 146, 530, 98, 162, 194, 578, 642, 148, 276, 532, 388, 644, 772, 56, 280, 536, 104, 296, 584, 176, 304, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_285, vertices_541, vertices_837, vertices_617, vertices_425, vertices_449, vertices_662, vertices_122, vertices_602, vertices_178, vertices_962, vertices_436, vertices_900, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_97, vertices_161, vertices_193, vertices_321, vertices_577, vertices_385, vertices_90, vertices_50, vertices_146, vertices_530, vertices_98, vertices_162, vertices_194, vertices_578, vertices_642, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_584, vertices_176, vertices_304, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_285), (false, vertices_541), (false, vertices_837), (false, vertices_617), (false, vertices_425), (false, vertices_449), (true, vertices_90), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_148), (true, vertices_388), (true, vertices_644), (true, vertices_56), (true, vertices_176), (true, vertices_304), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 14 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 436
cert_cover_5 5 3 1 3 4 6 148 436 2
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0083

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e11q2_0084.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0084

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 45, 333, 181, 85, 721, 481, 174, 666, 794, 738, 866, 156, 284, 852, 13, 21, 37, 69, 41, 265, 81, 145, 161, 289, 193, 321, 538, 42, 138, 266, 610, 162, 290, 642, 770, 28, 44, 140, 268, 84, 148, 276, 164, 324, 152, 280, 592, 656, 784, 224, 352, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_45, vertices_333, vertices_181, vertices_85, vertices_721, vertices_481, vertices_174, vertices_666, vertices_794, vertices_738, vertices_866, vertices_156, vertices_284, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_69, vertices_41, vertices_265, vertices_81, vertices_145, vertices_161, vertices_289, vertices_193, vertices_321, vertices_538, vertices_42, vertices_138, vertices_266, vertices_610, vertices_162, vertices_290, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_164, vertices_324, vertices_152, vertices_280, vertices_592, vertices_656, vertices_784, vertices_224, vertices_352, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_45), (false, vertices_333), (false, vertices_181), (false, vertices_85), (false, vertices_721), (false, vertices_481), (true, vertices_538), (true, vertices_138), (true, vertices_610), (true, vertices_162), (true, vertices_642), (true, vertices_770), (true, vertices_28), (true, vertices_140), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 16 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_333) then 14 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_538) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_610) then 20 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_538), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(true, vertices_610), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 6 174 42 1
cert_row_2 1 0 2 3 8 538
cert_row_2 2 0 4 5 8 610
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 42 174 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 538 666 3
cert_coverFacet 2 794
cert_cover_5 2 1 0 2 3 7 538 794 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 610 738 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 610 866 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 852
cert_cover_5 7 3 1 3 5 7 84 852 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0084

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e11q2_0085.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0085

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 155, 539, 451, 613, 325, 721, 426, 778, 812, 116, 436, 468, 632, 184, 27, 131, 259, 515, 69, 261, 517, 145, 529, 193, 321, 577, 138, 266, 522, 386, 770, 52, 84, 404, 100, 292, 548, 324, 772, 56, 152, 536, 168, 296, 552, 776, 112, 176, 208, 592, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_155, vertices_539, vertices_451, vertices_613, vertices_325, vertices_721, vertices_426, vertices_778, vertices_812, vertices_116, vertices_436, vertices_468, vertices_632, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_138, vertices_266, vertices_522, vertices_386, vertices_770, vertices_52, vertices_84, vertices_404, vertices_100, vertices_292, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_155), (false, vertices_539), (false, vertices_451), (false, vertices_613), (false, vertices_325), (false, vertices_721), (true, vertices_266), (true, vertices_52), (true, vertices_84), (true, vertices_404), (true, vertices_292), (true, vertices_56), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_112), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_155) then 18 else
  if p.val = (false, vertices_539) then 19 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_404) then 16 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 2 4 6 7 426 138 2
cert_row_2 1 1 3 6 7 404
cert_row_4 2 1 2 4 7 8 812 292 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 0 0 2 4 6 138 426 2
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 292 812 1
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 436
cert_cover_5 4 1 1 3 4 6 52 436 3
cert_coverFacet 5 468
cert_cover_5 5 1 1 3 5 6 84 468 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 56 632 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0085

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e11q2_0086.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0086

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 565, 405, 293, 217, 537, 905, 358, 234, 682, 466, 898, 604, 620, 340, 21, 37, 261, 25, 137, 521, 145, 529, 289, 545, 385, 769, 170, 98, 290, 546, 194, 322, 386, 642, 770, 588, 84, 276, 532, 100, 292, 548, 324, 88, 536, 104, 552, 200, 648, 208, 336, 400, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_565, vertices_405, vertices_293, vertices_217, vertices_537, vertices_905, vertices_358, vertices_234, vertices_682, vertices_466, vertices_898, vertices_604, vertices_620, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_25, vertices_137, vertices_521, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_170, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_588, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_88, vertices_536, vertices_104, vertices_552, vertices_200, vertices_648, vertices_208, vertices_336, vertices_400, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_565), (false, vertices_405), (false, vertices_293), (false, vertices_217), (false, vertices_537), (false, vertices_905), (true, vertices_170), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_588), (true, vertices_84), (true, vertices_100), (true, vertices_324), (true, vertices_104), (true, vertices_552), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (true, vertices_170) then 15 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_588) then 19 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 1 4 5 7 358 98 1
cert_row_4 3 0 3 5 6 7 466 194 1
cert_rows
cert_pivot_2 8 2 1 0
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 2 0 1 4 5 98 358 1
cert_coverFacet 1 234
cert_cover_5 1 1 0 2 4 5 170 234 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 8 170 682 3
cert_coverFacet 3 466
cert_cover_5 3 3 0 3 5 6 194 466 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 604
cert_cover_5 5 0 1 2 3 5 588 604 2
cert_coverFacet 6 620
cert_cover_5 6 0 1 2 4 5 588 620 2
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0086

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e11q2_0087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 789, 409, 233, 329, 721, 310, 230, 710, 774, 362, 572, 684, 312, 664, 73, 137, 265, 145, 273, 529, 193, 321, 577, 769, 38, 198, 262, 518, 98, 290, 322, 578, 770, 556, 52, 276, 532, 164, 644, 772, 56, 152, 280, 536, 104, 168, 296, 328, 648, 304, 656, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_789, vertices_409, vertices_233, vertices_329, vertices_721, vertices_310, vertices_230, vertices_710, vertices_774, vertices_362, vertices_572, vertices_684, vertices_312, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_38, vertices_198, vertices_262, vertices_518, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_556, vertices_52, vertices_276, vertices_532, vertices_164, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_328, vertices_648, vertices_304, vertices_656, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_789), (false, vertices_409), (false, vertices_233), (false, vertices_329), (false, vertices_721), (true, vertices_38), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_290), (true, vertices_556), (true, vertices_52), (true, vertices_164), (true, vertices_644), (true, vertices_56), (true, vertices_536), (true, vertices_296), (true, vertices_648), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_556) then 19 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_304) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_556), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_2 1 1 2 4 8 556
cert_row_4 2 0 1 3 4 7 310 38 2
cert_row_4 3 0 2 4 5 7 362 98 1
cert_rows
cert_pivot_2 6 8 1 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 2 0 1 3 4 38 310 2
cert_coverFacet 1 230
cert_cover_5 1 0 0 1 4 5 38 230 3
cert_coverFacet 2 710
cert_cover_5 2 0 0 1 5 8 198 710 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 362
cert_cover_5 4 3 0 2 4 5 98 362 1
cert_coverFacet 5 572
cert_cover_5 5 1 1 2 3 4 556 572 2
cert_coverFacet 6 684
cert_cover_5 6 1 1 2 4 6 556 684 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0087

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e11q2_0088.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0088

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 531, 227, 835, 541, 457, 777, 118, 598, 178, 412, 812, 436, 612, 992, 19, 67, 131, 515, 25, 137, 265, 521, 529, 193, 321, 769, 86, 50, 146, 530, 98, 162, 578, 28, 268, 524, 52, 404, 532, 100, 292, 548, 580, 152, 392, 776, 176, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_531, vertices_227, vertices_835, vertices_541, vertices_457, vertices_777, vertices_118, vertices_598, vertices_178, vertices_412, vertices_812, vertices_436, vertices_612, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_25, vertices_137, vertices_265, vertices_521, vertices_529, vertices_193, vertices_321, vertices_769, vertices_86, vertices_50, vertices_146, vertices_530, vertices_98, vertices_162, vertices_578, vertices_28, vertices_268, vertices_524, vertices_52, vertices_404, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_152, vertices_392, vertices_776, vertices_176, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_531), (false, vertices_227), (false, vertices_835), (false, vertices_541), (false, vertices_457), (false, vertices_777), (true, vertices_86), (true, vertices_50), (true, vertices_268), (true, vertices_52), (true, vertices_404), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_176), (true, vertices_608), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 22 13 24 17 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_227) then 18 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_541) then 15 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_86) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_404) then 23 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_2 1 1 3 6 7 404
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 86 118 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 412
cert_cover_5 3 1 1 2 3 6 28 412 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 268 812 2
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 52 436 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0088

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e11q2_0089.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0089

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 139, 179, 275, 173, 121, 849, 398, 914, 812, 244, 724, 612, 900, 872, 11, 19, 131, 259, 41, 73, 137, 49, 81, 273, 161, 321, 138, 266, 146, 274, 386, 44, 140, 268, 212, 100, 164, 548, 580, 388, 644, 772, 104, 808, 328, 112, 176, 592, 656, 784, 608, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_139, vertices_179, vertices_275, vertices_173, vertices_121, vertices_849, vertices_398, vertices_914, vertices_812, vertices_244, vertices_724, vertices_612, vertices_900, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_131, vertices_259, vertices_41, vertices_73, vertices_137, vertices_49, vertices_81, vertices_273, vertices_161, vertices_321, vertices_138, vertices_266, vertices_146, vertices_274, vertices_386, vertices_44, vertices_140, vertices_268, vertices_212, vertices_100, vertices_164, vertices_548, vertices_580, vertices_388, vertices_644, vertices_772, vertices_104, vertices_808, vertices_328, vertices_112, vertices_176, vertices_592, vertices_656, vertices_784, vertices_608, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_139), (false, vertices_179), (false, vertices_275), (false, vertices_173), (false, vertices_121), (false, vertices_849), (true, vertices_386), (true, vertices_268), (true, vertices_212), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_808), (true, vertices_656), (true, vertices_608), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_275) then 1 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_212) then 18 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_808) then 21 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 7 8 808
cert_row_2 1 1 3 5 6 212
cert_row_4 2 0 1 2 6 7 398 138 1
cert_row_4 3 0 3 6 7 8 914 146 3
cert_rows
cert_pivot_2 4 5 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 138 398 1
cert_coverFacet 1 914
cert_cover_5 1 3 0 3 6 7 146 914 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 212 244 2
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 8 212 724 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 872
cert_cover_5 7 0 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0089

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e11q2_0090.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 781, 613, 293, 313, 153, 689, 838, 218, 346, 778, 738, 436, 468, 228, 37, 261, 517, 25, 137, 265, 521, 49, 145, 289, 545, 641, 90, 138, 266, 522, 194, 322, 578, 642, 770, 404, 100, 164, 292, 196, 324, 580, 772, 152, 280, 776, 176, 304, 208, 336, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_781, vertices_613, vertices_293, vertices_313, vertices_153, vertices_689, vertices_838, vertices_218, vertices_346, vertices_778, vertices_738, vertices_436, vertices_468, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_404, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_781), (false, vertices_613), (false, vertices_293), (false, vertices_313), (false, vertices_153), (false, vertices_689), (true, vertices_90), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_404), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_208), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_2 0 0 2 3 5 90
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 1 5 7 8 838 322 1
cert_row_4 3 0 4 5 6 8 738 194 1
cert_rows
cert_pivot_2 2 3 1 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 2 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 3 0 4 5 6 194 738 1
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 404 436 2
cert_coverFacet 6 468
cert_cover_5 6 1 1 3 5 6 404 468 2
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0090

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e11q2_0091.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0091

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 451, 301, 677, 837, 721, 174, 122, 202, 306, 850, 668, 796, 312, 216, 387, 37, 261, 517, 161, 289, 193, 321, 577, 641, 42, 74, 138, 50, 82, 274, 162, 290, 194, 322, 540, 44, 140, 268, 164, 644, 772, 56, 88, 152, 280, 296, 200, 304, 208, 592, 656, 784, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_451, vertices_301, vertices_677, vertices_837, vertices_721, vertices_174, vertices_122, vertices_202, vertices_306, vertices_850, vertices_668, vertices_796, vertices_312, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_387, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_42, vertices_74, vertices_138, vertices_50, vertices_82, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_540, vertices_44, vertices_140, vertices_268, vertices_164, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_296, vertices_200, vertices_304, vertices_208, vertices_592, vertices_656, vertices_784, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_451), (false, vertices_301), (false, vertices_677), (false, vertices_837), (false, vertices_721), (true, vertices_42), (true, vertices_74), (true, vertices_138), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_540), (true, vertices_140), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_540) then 19 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 6 174 42 1
cert_row_2 1 1 2 3 8 540
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 0 3 5 7 8 850 82 3
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 42 174 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 42 122 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 850
cert_cover_5 4 3 0 3 5 7 82 850 3
cert_coverFacet 5 668
cert_cover_5 5 1 1 2 3 6 540 668 3
cert_coverFacet 6 796
cert_cover_5 6 1 1 2 3 7 540 796 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0091

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e11q2_0092.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0092

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 653, 269, 357, 549, 409, 961, 566, 218, 602, 434, 482, 316, 540, 712, 13, 37, 261, 517, 137, 265, 97, 545, 321, 577, 385, 641, 90, 50, 146, 530, 98, 418, 546, 194, 578, 28, 268, 524, 52, 532, 292, 548, 152, 280, 536, 200, 584, 648, 304, 400, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_653, vertices_269, vertices_357, vertices_549, vertices_409, vertices_961, vertices_566, vertices_218, vertices_602, vertices_434, vertices_482, vertices_316, vertices_540, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_137, vertices_265, vertices_97, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_90, vertices_50, vertices_146, vertices_530, vertices_98, vertices_418, vertices_546, vertices_194, vertices_578, vertices_28, vertices_268, vertices_524, vertices_52, vertices_532, vertices_292, vertices_548, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_648, vertices_304, vertices_400, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_653), (false, vertices_269), (false, vertices_357), (false, vertices_549), (false, vertices_409), (false, vertices_961), (true, vertices_90), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_418), (true, vertices_194), (true, vertices_28), (true, vertices_52), (true, vertices_532), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 16 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 20 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_357) then 15 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_409) then 17 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_418) then 21 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_304) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_418), by decide +kernel⟩
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
cert_row_2 0 0 2 3 5 90
cert_row_2 1 0 4 6 7 418
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 6 50 434 3
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 98 482 3
cert_coverFacet 5 316
cert_cover_5 5 3 1 2 3 4 28 316 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0092

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 285, 837, 625, 433, 782, 218, 282, 682, 402, 418, 204, 652, 740, 240, 29, 69, 261, 49, 81, 273, 289, 545, 577, 769, 26, 138, 266, 522, 146, 274, 162, 290, 546, 386, 770, 76, 140, 268, 524, 196, 580, 644, 772, 88, 280, 200, 648, 112, 176, 208, 400, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_285, vertices_837, vertices_625, vertices_433, vertices_782, vertices_218, vertices_282, vertices_682, vertices_402, vertices_418, vertices_204, vertices_652, vertices_740, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_261, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_644, vertices_772, vertices_88, vertices_280, vertices_200, vertices_648, vertices_112, vertices_176, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_285), (false, vertices_837), (false, vertices_625), (false, vertices_433), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_386), (true, vertices_140), (true, vertices_524), (true, vertices_196), (true, vertices_644), (true, vertices_200), (true, vertices_648), (true, vertices_208), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_285) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 3 5 6 218 26 3
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 26 218 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 138 682 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 740
cert_cover_5 8 3 1 4 5 6 196 740 1
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0000

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 597, 569, 281, 465, 865, 286, 542, 422, 710, 170, 650, 212, 404, 744, 480, 25, 41, 265, 81, 273, 529, 289, 545, 321, 577, 30, 134, 262, 518, 42, 138, 266, 522, 162, 290, 642, 84, 148, 276, 532, 196, 580, 388, 280, 536, 168, 552, 648, 208, 400, 224, 352, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_597, vertices_569, vertices_281, vertices_465, vertices_865, vertices_286, vertices_542, vertices_422, vertices_710, vertices_170, vertices_650, vertices_212, vertices_404, vertices_744, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_81, vertices_273, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_30, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_642, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_280, vertices_536, vertices_168, vertices_552, vertices_648, vertices_208, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_597), (false, vertices_569), (false, vertices_281), (false, vertices_465), (false, vertices_865), (true, vertices_30), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_168), (true, vertices_648), (true, vertices_224), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 281 134 262 518 138 522 162 642 148 276 196 388 168 648 224 416 704 299 30 597 569 465 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 3 7 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 7 30 286 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 134 422 2
cert_coverFacet 3 710
cert_cover_5 3 2 0 1 5 6 134 710 2
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 650
cert_cover_2 5 2 0 6 8 138 650 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 168 744 2
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0001

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 787, 547, 451, 345, 689, 209, 558, 390, 774, 796, 364, 484, 728, 616, 736, 35, 131, 259, 515, 81, 145, 273, 529, 161, 545, 193, 321, 38, 134, 262, 518, 546, 386, 770, 44, 268, 524, 356, 164, 388, 772, 88, 280, 536, 104, 552, 328, 584, 208, 656, 784, 224, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_787, vertices_547, vertices_451, vertices_345, vertices_689, vertices_209, vertices_558, vertices_390, vertices_774, vertices_796, vertices_364, vertices_484, vertices_728, vertices_616, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_38, vertices_134, vertices_262, vertices_518, vertices_546, vertices_386, vertices_770, vertices_44, vertices_268, vertices_524, vertices_356, vertices_164, vertices_388, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_208, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_787), (false, vertices_547), (false, vertices_451), (false, vertices_345), (false, vertices_689), (false, vertices_209), (true, vertices_262), (true, vertices_518), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_356), (true, vertices_388), (true, vertices_772), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_224), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 17 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_356) then 21 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 8 558 38 2
cert_row_2 1 1 4 5 7 356
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 38 558 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 268 796 2
cert_coverFacet 4 364
cert_cover_5 4 1 1 2 4 5 44 364 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 356 484 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0002

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 181, 565, 901, 601, 409, 329, 710, 362, 434, 226, 898, 620, 228, 312, 568, 53, 133, 517, 25, 73, 265, 145, 529, 321, 577, 385, 769, 98, 162, 290, 194, 322, 578, 386, 642, 770, 100, 164, 548, 196, 580, 644, 56, 280, 536, 104, 296, 552, 328, 584, 176, 304, 560, 400, 224, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_181, vertices_565, vertices_901, vertices_601, vertices_409, vertices_329, vertices_710, vertices_362, vertices_434, vertices_226, vertices_898, vertices_620, vertices_228, vertices_312, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_53, vertices_133, vertices_517, vertices_25, vertices_73, vertices_265, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_769, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_224, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_181), (false, vertices_565), (false, vertices_901), (false, vertices_601), (false, vertices_409), (false, vertices_329), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 162 1
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 2 4 5 7 362 98 1
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 362
cert_cover_5 1 2 0 2 4 5 98 362 1
cert_coverFacet 2 434
cert_cover_5 2 0 0 3 4 6 162 434 1
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 100 620 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0003

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 299, 523, 707, 781, 597, 197, 554, 434, 674, 244, 404, 788, 376, 856, 744, 11, 131, 259, 515, 69, 133, 261, 517, 265, 521, 193, 577, 42, 522, 162, 290, 546, 386, 642, 84, 148, 276, 532, 196, 388, 772, 344, 104, 296, 552, 584, 776, 112, 176, 304, 592, 400, 784, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_299, vertices_523, vertices_707, vertices_781, vertices_597, vertices_197, vertices_554, vertices_434, vertices_674, vertices_244, vertices_404, vertices_788, vertices_376, vertices_856, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_265, vertices_521, vertices_193, vertices_577, vertices_42, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_388, vertices_772, vertices_344, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_784, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_299), (false, vertices_523), (false, vertices_707), (false, vertices_781), (false, vertices_597), (false, vertices_197), (true, vertices_162), (true, vertices_546), (true, vertices_148), (true, vertices_276), (true, vertices_344), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_597) then 22 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_344) then 24 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 162 1
cert_row_2 1 2 3 5 7 344
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 554
cert_cover_2 0 2 0 4 8 42 554 3
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 162 434 1
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 84 244 2
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 376
cert_cover_5 6 1 2 3 4 5 344 376 2
cert_coverFacet 7 856
cert_cover_5 7 1 2 3 5 8 344 856 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0004

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 269, 453, 241, 593, 913, 302, 186, 666, 482, 898, 60, 540, 628, 356, 13, 69, 261, 265, 521, 81, 145, 529, 193, 577, 385, 769, 154, 42, 266, 522, 162, 290, 386, 642, 770, 28, 44, 268, 524, 52, 532, 100, 292, 324, 580, 56, 536, 112, 176, 592, 656, 224, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_269, vertices_453, vertices_241, vertices_593, vertices_913, vertices_302, vertices_186, vertices_666, vertices_482, vertices_898, vertices_60, vertices_540, vertices_628, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_154, vertices_42, vertices_266, vertices_522, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_100, vertices_292, vertices_324, vertices_580, vertices_56, vertices_536, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_269), (false, vertices_453), (false, vertices_241), (false, vertices_593), (false, vertices_913), (true, vertices_154), (true, vertices_42), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_56), (true, vertices_536), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_913) then 25 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_536) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 1 3 4 5 8 628 52 3
cert_row_2 1 0 2 3 6 154
cert_row_4 2 0 1 2 4 7 302 42 1
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 8 3 1 0
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 2 0 1 2 4 42 302 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 154 186 3
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 8 154 666 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 162 482 2
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 628
cert_cover_5 7 0 1 3 4 5 52 628 3
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0005

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 551, 339, 707, 789, 665, 209, 362, 610, 908, 740, 420, 248, 344, 792, 424, 39, 67, 259, 515, 261, 517, 81, 145, 273, 529, 193, 641, 98, 290, 546, 322, 578, 164, 292, 548, 388, 644, 772, 88, 152, 280, 536, 104, 168, 296, 328, 392, 648, 776, 208, 336, 784, 224, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_551, vertices_339, vertices_707, vertices_789, vertices_665, vertices_209, vertices_362, vertices_610, vertices_908, vertices_740, vertices_420, vertices_248, vertices_344, vertices_792, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_67, vertices_259, vertices_515, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_641, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_208, vertices_336, vertices_784, vertices_224, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_551), (false, vertices_339), (false, vertices_707), (false, vertices_789), (false, vertices_665), (false, vertices_209), (true, vertices_98), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 16 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 17 else
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_339) then 21 else
  if p.val = (false, vertices_707) then 22 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 98 1
cert_row_4 1 1 2 6 7 8 908 388 1
cert_row_4 2 1 4 5 6 8 740 164 2
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 362
cert_cover_5 0 0 0 2 4 5 98 362 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 908
cert_cover_5 2 1 1 2 6 7 388 908 1
cert_coverFacet 3 740
cert_cover_5 3 2 1 4 5 6 164 740 2
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 248
cert_cover_5 5 3 2 3 4 5 88 248 2
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0006

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0007.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0007

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 565, 341, 293, 217, 537, 841, 422, 234, 618, 466, 834, 684, 404, 660, 664, 21, 37, 261, 25, 73, 521, 81, 529, 289, 545, 321, 769, 106, 162, 290, 546, 194, 322, 578, 386, 770, 148, 276, 532, 164, 292, 548, 388, 644, 152, 536, 168, 552, 200, 584, 648, 208, 336, 400, 656, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_565, vertices_341, vertices_293, vertices_217, vertices_537, vertices_841, vertices_422, vertices_234, vertices_618, vertices_466, vertices_834, vertices_684, vertices_404, vertices_660, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_25, vertices_73, vertices_521, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_769, vertices_106, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_565), (false, vertices_341), (false, vertices_293), (false, vertices_217), (false, vertices_537), (false, vertices_841), (true, vertices_106), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 293 1 537 162 194 322 578 386 148 164 388 644 168 552 648 400 656 803 106 565 341 217 841
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 194 1
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 1 2 4 6 8 684 164 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 234
cert_cover_5 1 1 0 2 4 6 106 234 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 8 106 618 3
cert_coverFacet 3 466
cert_cover_5 3 0 0 3 5 6 194 466 1
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 164 684 1
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0007

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 789, 421, 709, 89, 537, 465, 782, 678, 294, 314, 106, 738, 248, 792, 432, 133, 261, 517, 25, 73, 521, 81, 273, 529, 193, 577, 385, 38, 262, 518, 42, 74, 266, 522, 98, 674, 290, 578, 164, 292, 644, 772, 56, 88, 280, 536, 104, 776, 176, 304, 208, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_789, vertices_421, vertices_709, vertices_89, vertices_537, vertices_465, vertices_782, vertices_678, vertices_294, vertices_314, vertices_106, vertices_738, vertices_248, vertices_792, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_73, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_38, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_674, vertices_290, vertices_578, vertices_164, vertices_292, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_789), (false, vertices_421), (false, vertices_709), (false, vertices_89), (false, vertices_537), (false, vertices_465), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_98), (true, vertices_674), (true, vertices_290), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_674) then 18 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 89 1 537 38 262 518 42 266 98 290 56 280 104 776 176 304 224 587 674 789 421 709 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 0 4 6 8 674
cert_row_4 2 0 2 3 4 7 314 42 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 38 678 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 314
cert_cover_5 3 2 0 2 3 4 42 314 2
cert_coverFacet 4 106
cert_cover_2 4 2 0 4 5 42 106 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 98 738 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0008

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3873 : Certifies 3873 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3874 : Certifies 3874 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3875 : Certifies 3875 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0073.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3876 : Certifies 3876 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3877 : Certifies 3877 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3878 : Certifies 3878 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0077.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3879 : Certifies 3879 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0078.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3880 : Certifies 3880 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0079.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3881 : Certifies 3881 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0080.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3882 : Certifies 3882 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0081.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3883 : Certifies 3883 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0082.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3884 : Certifies 3884 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0083.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3885 : Certifies 3885 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0084.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3886 : Certifies 3886 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0085.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3887 : Certifies 3887 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0086.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3888 : Certifies 3888 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3889 : Certifies 3889 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0088.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3890 : Certifies 3890 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0089.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3891 : Certifies 3891 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0090.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3892 : Certifies 3892 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0091.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3893 : Certifies 3893 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0092.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3894 : Certifies 3894 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3895 : Certifies 3895 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3896 : Certifies 3896 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3897 : Certifies 3897 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3898 : Certifies 3898 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3899 : Certifies 3899 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3900 : Certifies 3900 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3901 : Certifies 3901 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0007.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3902 : Certifies 3902 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B128 (j : Fin 30) :
    Certifies (3873 + j.val) := by
  fin_cases j
  · exact projection_3873
  · exact projection_3874
  · exact projection_3875
  · exact projection_3876
  · exact projection_3877
  · exact projection_3878
  · exact projection_3879
  · exact projection_3880
  · exact projection_3881
  · exact projection_3882
  · exact projection_3883
  · exact projection_3884
  · exact projection_3885
  · exact projection_3886
  · exact projection_3887
  · exact projection_3888
  · exact projection_3889
  · exact projection_3890
  · exact projection_3891
  · exact projection_3892
  · exact projection_3893
  · exact projection_3894
  · exact projection_3895
  · exact projection_3896
  · exact projection_3897
  · exact projection_3898
  · exact projection_3899
  · exact projection_3900
  · exact projection_3901
  · exact projection_3902

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
