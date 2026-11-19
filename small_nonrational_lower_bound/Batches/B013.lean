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
/- Source: ProjectionCertificates/R_m14e11q2_0007.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0007

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 115, 547, 323, 653, 457, 737, 310, 806, 466, 412, 780, 628, 724, 35, 67, 259, 515, 137, 265, 521, 97, 545, 193, 321, 641, 294, 50, 82, 274, 546, 322, 770, 140, 268, 524, 52, 596, 148, 276, 548, 644, 772, 392, 776, 112, 208, 400, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_115, vertices_547, vertices_323, vertices_653, vertices_457, vertices_737, vertices_310, vertices_806, vertices_466, vertices_412, vertices_780, vertices_628, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_97, vertices_545, vertices_193, vertices_321, vertices_641, vertices_294, vertices_50, vertices_82, vertices_274, vertices_546, vertices_322, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_596, vertices_148, vertices_276, vertices_548, vertices_644, vertices_772, vertices_392, vertices_776, vertices_112, vertices_208, vertices_400, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_115), (false, vertices_547), (false, vertices_323), (false, vertices_653), (false, vertices_457), (false, vertices_737), (true, vertices_294), (true, vertices_274), (true, vertices_268), (true, vertices_52), (true, vertices_596), (true, vertices_148), (true, vertices_276), (true, vertices_548), (true, vertices_772), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_115) then 13 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_294) then 14 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_596) then 17 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_400) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 8 596
cert_row_2 1 0 1 4 7 294
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 2 3 6 7 412 140 2
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 294 310 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 8 294 806 3
cert_coverFacet 2 466
cert_cover_5 2 2 0 3 5 6 82 466 3
cert_coverFacet 3 412
cert_cover_5 3 3 1 2 3 6 140 412 2
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 628
cert_cover_5 5 0 1 3 4 5 52 628 3
cert_coverFacet 6 724
cert_cover_5 6 0 1 3 5 6 596 724 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0007

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e11q2_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 309, 213, 837, 409, 905, 110, 206, 682, 866, 60, 156, 356, 824, 21, 69, 261, 393, 145, 273, 193, 577, 641, 769, 78, 42, 138, 98, 546, 194, 578, 642, 28, 44, 140, 52, 148, 100, 292, 196, 324, 56, 152, 280, 552, 648, 776, 304, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_309, vertices_213, vertices_837, vertices_409, vertices_905, vertices_110, vertices_206, vertices_682, vertices_866, vertices_60, vertices_156, vertices_356, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_393, vertices_145, vertices_273, vertices_193, vertices_577, vertices_641, vertices_769, vertices_78, vertices_42, vertices_138, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_140, vertices_52, vertices_148, vertices_100, vertices_292, vertices_196, vertices_324, vertices_56, vertices_152, vertices_280, vertices_552, vertices_648, vertices_776, vertices_304, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_309), (false, vertices_213), (false, vertices_837), (false, vertices_409), (false, vertices_905), (true, vertices_78), (true, vertices_42), (true, vertices_138), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_100), (true, vertices_56), (true, vertices_552), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (true, vertices_78) then 14 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 78 110 3
cert_coverFacet 1 206
cert_cover_5 1 0 0 1 2 6 78 206 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 42 682 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 98 866 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0008

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e11q2_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 397, 661, 805, 617, 713, 790, 122, 458, 562, 466, 802, 404, 752, 133, 261, 517, 41, 585, 137, 265, 289, 545, 641, 42, 74, 266, 50, 82, 274, 530, 290, 546, 450, 770, 148, 276, 532, 388, 772, 104, 200, 392, 112, 560, 208, 400, 656, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_397, vertices_661, vertices_805, vertices_617, vertices_713, vertices_790, vertices_122, vertices_458, vertices_562, vertices_466, vertices_802, vertices_404, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_585, vertices_137, vertices_265, vertices_289, vertices_545, vertices_641, vertices_42, vertices_74, vertices_266, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_450, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_200, vertices_392, vertices_112, vertices_560, vertices_208, vertices_400, vertices_656, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_397), (false, vertices_661), (false, vertices_805), (false, vertices_617), (false, vertices_713), (true, vertices_74), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_450), (true, vertices_770), (true, vertices_276), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_450) then 14 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 7 0 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 42 122 2
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 82 466 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0009

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e11q2_0010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 789, 841, 689, 465, 110, 590, 566, 226, 674, 188, 412, 780, 488, 145, 273, 529, 193, 321, 577, 641, 769, 78, 38, 518, 98, 162, 546, 194, 578, 642, 156, 44, 268, 524, 52, 276, 532, 772, 104, 168, 328, 584, 392, 776, 176, 560, 400, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_789, vertices_841, vertices_689, vertices_465, vertices_110, vertices_590, vertices_566, vertices_226, vertices_674, vertices_188, vertices_412, vertices_780, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_78, vertices_38, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_156, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_772, vertices_104, vertices_168, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_560, vertices_400, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_789), (false, vertices_841), (false, vertices_689), (false, vertices_465), (true, vertices_78), (true, vertices_38), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_156), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_104), (true, vertices_168), (true, vertices_392), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_156) then 18 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 38 2
cert_row_2 1 0 1 2 5 78
cert_row_2 2 1 2 3 6 156
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
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 188
cert_cover_5 5 2 1 2 3 4 156 188 3
cert_coverFacet 6 412
cert_cover_5 6 2 1 2 3 7 156 412 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0010

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e11q2_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 333, 597, 421, 677, 617, 662, 218, 538, 554, 458, 930, 468, 600, 165, 69, 261, 517, 41, 73, 265, 289, 545, 577, 26, 42, 202, 266, 522, 146, 530, 290, 546, 386, 642, 84, 148, 532, 324, 388, 644, 88, 536, 552, 328, 584, 208, 592, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_333, vertices_597, vertices_421, vertices_677, vertices_617, vertices_662, vertices_218, vertices_538, vertices_554, vertices_458, vertices_930, vertices_468, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_289, vertices_545, vertices_577, vertices_26, vertices_42, vertices_202, vertices_266, vertices_522, vertices_146, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_84, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_88, vertices_536, vertices_552, vertices_328, vertices_584, vertices_208, vertices_592, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_333), (false, vertices_597), (false, vertices_421), (false, vertices_677), (false, vertices_617), (true, vertices_26), (true, vertices_202), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_88), (true, vertices_536), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_333) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_617) then 17 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_202) then 14 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 4 6 7 8 930 290 2
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 458
cert_cover_5 4 0 0 2 5 7 202 458 3
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 290 930 2
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0011

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e11q2_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 403, 227, 611, 589, 453, 186, 562, 786, 572, 348, 788, 472, 744, 99, 131, 259, 515, 69, 261, 517, 193, 577, 385, 50, 146, 274, 530, 162, 546, 770, 28, 76, 524, 276, 532, 324, 772, 56, 344, 152, 168, 552, 200, 584, 560, 400, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_403, vertices_227, vertices_611, vertices_589, vertices_453, vertices_186, vertices_562, vertices_786, vertices_572, vertices_348, vertices_788, vertices_472, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_770, vertices_28, vertices_76, vertices_524, vertices_276, vertices_532, vertices_324, vertices_772, vertices_56, vertices_344, vertices_152, vertices_168, vertices_552, vertices_200, vertices_584, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_403), (false, vertices_227), (false, vertices_611), (false, vertices_589), (false, vertices_453), (true, vertices_50), (true, vertices_530), (true, vertices_28), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_344), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_227) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (false, vertices_453) then 15 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_344) then 21 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 7 344
cert_row_4 1 0 2 3 4 6 186 50 1
cert_row_4 2 1 2 3 4 8 572 28 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 1 0 2 3 4 50 186 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 4 28 572 3
cert_coverFacet 4 348
cert_cover_5 4 0 1 2 3 5 28 348 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 472
cert_cover_5 6 0 2 3 5 6 344 472 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 168 744 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0012

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e11q2_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 709, 217, 425, 849, 929, 30, 46, 342, 678, 838, 810, 188, 212, 25, 137, 265, 81, 273, 417, 193, 577, 641, 769, 14, 22, 38, 326, 518, 26, 42, 266, 274, 546, 770, 28, 44, 84, 148, 164, 196, 580, 644, 152, 168, 296, 208, 336, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_709, vertices_217, vertices_425, vertices_849, vertices_929, vertices_30, vertices_46, vertices_342, vertices_678, vertices_838, vertices_810, vertices_188, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_81, vertices_273, vertices_417, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_326, vertices_518, vertices_26, vertices_42, vertices_266, vertices_274, vertices_546, vertices_770, vertices_28, vertices_44, vertices_84, vertices_148, vertices_164, vertices_196, vertices_580, vertices_644, vertices_152, vertices_168, vertices_296, vertices_208, vertices_336, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_709), (false, vertices_217), (false, vertices_425), (false, vertices_849), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_326), (true, vertices_518), (true, vertices_42), (true, vertices_546), (true, vertices_770), (true, vertices_28), (true, vertices_44), (true, vertices_84), (true, vertices_148), (true, vertices_164)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 21 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 13 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_217) then 18 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_326) then 14 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_164) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 7 326
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 2 3 4 6 188 28 3
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 5 22 342 3
cert_coverFacet 3 678
cert_cover_5 3 2 0 1 4 6 38 678 3
cert_coverFacet 4 838
cert_cover_5 4 0 0 1 5 8 326 838 3
cert_coverFacet 5 810
cert_cover_5 5 1 0 2 4 7 42 810 3
cert_coverFacet 6 188
cert_cover_5 6 3 1 2 3 4 28 188 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0013

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e11q2_0014.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0014

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 333, 313, 617, 465, 737, 214, 342, 678, 774, 810, 306, 716, 780, 41, 73, 265, 49, 145, 273, 609, 161, 193, 321, 86, 134, 262, 518, 50, 146, 274, 162, 290, 546, 770, 76, 268, 524, 196, 324, 644, 772, 296, 552, 584, 776, 304, 208, 336, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_333, vertices_313, vertices_617, vertices_465, vertices_737, vertices_214, vertices_342, vertices_678, vertices_774, vertices_810, vertices_306, vertices_716, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_49, vertices_145, vertices_273, vertices_609, vertices_161, vertices_193, vertices_321, vertices_86, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_770, vertices_76, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_772, vertices_296, vertices_552, vertices_584, vertices_776, vertices_304, vertices_208, vertices_336, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_333), (false, vertices_313), (false, vertices_617), (false, vertices_465), (false, vertices_737), (true, vertices_86), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_524), (true, vertices_196), (true, vertices_644), (true, vertices_772), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 21 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 13 else
  if p.val = (false, vertices_333) then 16 else
  if p.val = (false, vertices_313) then 18 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 1 4 6 8 678 134 2
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 678
cert_cover_5 2 2 0 1 4 6 134 678 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 810
cert_cover_5 4 1 0 2 4 7 290 810 1
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0014

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e11q2_0015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 61, 205, 453, 665, 433, 30, 78, 54, 838, 602, 690, 930, 968, 13, 37, 197, 261, 25, 137, 49, 145, 289, 385, 14, 22, 38, 70, 262, 26, 74, 50, 530, 674, 290, 578, 770, 28, 76, 52, 324, 536, 200, 584, 648, 176, 656, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_61, vertices_205, vertices_453, vertices_665, vertices_433, vertices_30, vertices_78, vertices_54, vertices_838, vertices_602, vertices_690, vertices_930, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_197, vertices_261, vertices_25, vertices_137, vertices_49, vertices_145, vertices_289, vertices_385, vertices_14, vertices_22, vertices_38, vertices_70, vertices_262, vertices_26, vertices_74, vertices_50, vertices_530, vertices_674, vertices_290, vertices_578, vertices_770, vertices_28, vertices_76, vertices_52, vertices_324, vertices_536, vertices_200, vertices_584, vertices_648, vertices_176, vertices_656, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_61), (false, vertices_205), (false, vertices_453), (false, vertices_665), (false, vertices_433), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_50), (true, vertices_530), (true, vertices_674), (true, vertices_578), (true, vertices_770), (true, vertices_584), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_674) then 14 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_674), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 0 4 6 8 674
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 78
cert_cover_2 1 1 0 2 5 14 78 3
cert_coverFacet 2 54
cert_cover_2 2 1 0 3 4 22 54 3
cert_coverFacet 3 838
cert_cover_5 3 1 0 1 5 7 70 838 3
cert_coverFacet 4 602
cert_cover_5 4 2 0 2 3 5 26 602 3
cert_coverFacet 5 690
cert_cover_5 5 0 0 3 4 6 50 690 3
cert_coverFacet 6 930
cert_cover_5 6 0 0 4 6 7 674 930 3
cert_coverFacet 7 968
cert_cover_5 7 3 2 5 6 7 200 968 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0015

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e11q2_0016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 597, 357, 901, 217, 457, 422, 678, 410, 538, 362, 554, 620, 600, 69, 261, 517, 201, 81, 145, 529, 321, 385, 641, 166, 26, 42, 266, 522, 146, 530, 290, 546, 386, 642, 100, 292, 548, 580, 388, 644, 88, 152, 536, 104, 552, 328, 584, 392, 592, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_597, vertices_357, vertices_901, vertices_217, vertices_457, vertices_422, vertices_678, vertices_410, vertices_538, vertices_362, vertices_554, vertices_620, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_201, vertices_81, vertices_145, vertices_529, vertices_321, vertices_385, vertices_641, vertices_166, vertices_26, vertices_42, vertices_266, vertices_522, vertices_146, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_100, vertices_292, vertices_548, vertices_580, vertices_388, vertices_644, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_392, vertices_592, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_597), (false, vertices_357), (false, vertices_901), (false, vertices_217), (false, vertices_457), (true, vertices_166), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_548), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_166) then 14 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_584) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_2 1 0 1 4 6 166
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 7 166 422 3
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 8 166 678 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 6 26 410 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 362
cert_cover_5 4 2 0 2 4 5 42 362 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0016

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e11q2_0017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 157, 285, 677, 809, 713, 118, 278, 842, 338, 738, 802, 244, 472, 29, 37, 133, 261, 137, 265, 521, 289, 545, 641, 22, 38, 262, 82, 274, 98, 290, 546, 322, 578, 770, 116, 148, 276, 164, 152, 280, 200, 328, 584, 776, 208, 336, 224, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_157, vertices_285, vertices_677, vertices_809, vertices_713, vertices_118, vertices_278, vertices_842, vertices_338, vertices_738, vertices_802, vertices_244, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_289, vertices_545, vertices_641, vertices_22, vertices_38, vertices_262, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_116, vertices_148, vertices_276, vertices_164, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_776, vertices_208, vertices_336, vertices_224, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_157), (false, vertices_285), (false, vertices_677), (false, vertices_809), (false, vertices_713), (true, vertices_22), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_116), (true, vertices_328), (true, vertices_208), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 21 23 14 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_116) then 17 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inl 4
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 5 116
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 842
cert_cover_5 2 2 0 2 5 7 322 842 1
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 98 738 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 244
cert_cover_5 6 0 1 3 4 6 116 244 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 152 472 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0017

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e11q2_0020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 355, 547, 451, 117, 569, 217, 902, 818, 604, 716, 308, 788, 484, 35, 323, 131, 515, 25, 137, 521, 49, 81, 97, 545, 193, 290, 546, 386, 642, 770, 588, 52, 84, 276, 532, 100, 292, 196, 388, 644, 772, 88, 536, 200, 648, 304, 560, 784, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_355, vertices_547, vertices_451, vertices_117, vertices_569, vertices_217, vertices_902, vertices_818, vertices_604, vertices_716, vertices_308, vertices_788, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_323, vertices_131, vertices_515, vertices_25, vertices_137, vertices_521, vertices_49, vertices_81, vertices_97, vertices_545, vertices_193, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_588, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_196, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_200, vertices_648, vertices_304, vertices_560, vertices_784, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_355), (false, vertices_547), (false, vertices_451), (false, vertices_117), (false, vertices_569), (false, vertices_217), (true, vertices_770), (true, vertices_588), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_355) then 13 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_588) then 17 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_2 0 1 2 5 8 588
cert_row_4 1 0 3 4 7 8 818 290 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 818
cert_cover_5 1 1 0 3 4 7 290 818 1
cert_coverFacet 2 604
cert_cover_5 2 0 1 2 3 5 588 604 2
cert_coverFacet 3 716
cert_cover_5 3 0 1 2 5 6 588 716 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0020

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e11q2_0023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 677, 837, 241, 465, 174, 654, 58, 538, 434, 850, 604, 120, 37, 69, 517, 209, 97, 161, 321, 385, 641, 769, 142, 26, 42, 522, 50, 274, 530, 162, 386, 642, 770, 44, 76, 524, 164, 580, 644, 56, 88, 536, 104, 112, 176, 336, 592, 400, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_677, vertices_837, vertices_241, vertices_465, vertices_174, vertices_654, vertices_58, vertices_538, vertices_434, vertices_850, vertices_604, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_209, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_142, vertices_26, vertices_42, vertices_522, vertices_50, vertices_274, vertices_530, vertices_162, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_524, vertices_164, vertices_580, vertices_644, vertices_56, vertices_88, vertices_536, vertices_104, vertices_112, vertices_176, vertices_336, vertices_592, vertices_400, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_677), (false, vertices_837), (false, vertices_241), (false, vertices_465), (true, vertices_142), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_524), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_109) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_142) then 14 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 142 174 3
cert_coverFacet 1 654
cert_cover_5 1 1 0 1 2 8 142 654 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 50 434 3
cert_coverFacet 5 850
cert_cover_5 5 2 0 3 5 7 274 850 2
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0023

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e11q2_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 87, 171, 563, 197, 849, 737, 334, 58, 346, 428, 964, 312, 944, 7, 139, 19, 35, 69, 133, 81, 529, 161, 545, 193, 577, 14, 70, 26, 42, 330, 50, 82, 140, 268, 196, 324, 388, 56, 280, 168, 296, 304, 560, 336, 784, 416, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_87, vertices_171, vertices_563, vertices_197, vertices_849, vertices_737, vertices_334, vertices_58, vertices_346, vertices_428, vertices_964, vertices_312, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_139, vertices_19, vertices_35, vertices_69, vertices_133, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_577, vertices_14, vertices_70, vertices_26, vertices_42, vertices_330, vertices_50, vertices_82, vertices_140, vertices_268, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_168, vertices_296, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_87), (false, vertices_171), (false, vertices_563), (false, vertices_197), (false, vertices_849), (false, vertices_737), (true, vertices_26), (true, vertices_330), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_304), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 11 23 13 16 18 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 21 else
  if p.val = (false, vertices_87) then 12 else
  if p.val = (false, vertices_171) then 22 else
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_849) then 15 else
  if p.val = (false, vertices_737) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_330) then 19 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 7 330
cert_row_4 1 1 2 4 6 7 428 140 2
cert_row_4 2 1 5 6 7 8 964 196 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 26 346 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 140 428 2
cert_coverFacet 4 964
cert_cover_5 4 2 1 5 6 7 196 964 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0024

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e11q2_0025.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 333, 589, 405, 721, 481, 62, 526, 362, 586, 562, 738, 316, 944, 77, 21, 261, 517, 145, 529, 193, 321, 577, 385, 14, 22, 518, 42, 74, 522, 50, 530, 98, 546, 578, 60, 268, 524, 276, 296, 328, 584, 304, 560, 400, 656, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_333, vertices_589, vertices_405, vertices_721, vertices_481, vertices_62, vertices_526, vertices_362, vertices_586, vertices_562, vertices_738, vertices_316, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_21, vertices_261, vertices_517, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_14, vertices_22, vertices_518, vertices_42, vertices_74, vertices_522, vertices_50, vertices_530, vertices_98, vertices_546, vertices_578, vertices_60, vertices_268, vertices_524, vertices_276, vertices_296, vertices_328, vertices_584, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_333), (false, vertices_589), (false, vertices_405), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_60), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 21 14 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 13 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_721) then 16 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 4 5 7 362 42 3
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 42 362 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 316
cert_cover_5 6 0 1 2 3 7 60 316 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0025

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e11q2_0028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 117, 277, 709, 773, 233, 433, 790, 314, 538, 426, 714, 572, 620, 21, 69, 261, 517, 49, 273, 97, 161, 193, 385, 641, 769, 26, 298, 138, 522, 274, 530, 386, 642, 770, 556, 52, 276, 532, 100, 580, 772, 56, 536, 104, 168, 200, 584, 304, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_277, vertices_709, vertices_773, vertices_233, vertices_433, vertices_790, vertices_314, vertices_538, vertices_426, vertices_714, vertices_572, vertices_620] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_97, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_298, vertices_138, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_556, vertices_52, vertices_276, vertices_532, vertices_100, vertices_580, vertices_772, vertices_56, vertices_536, vertices_104, vertices_168, vertices_200, vertices_584, vertices_304, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_277), (false, vertices_709), (false, vertices_773), (false, vertices_233), (false, vertices_433), (true, vertices_26), (true, vertices_298), (true, vertices_138), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_556), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_298) then 13 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_556) then 17 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_584) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_298), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_556), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 0 2 4 7 298
cert_row_2 2 1 2 4 8 556
cert_row_4 3 0 2 5 6 8 714 138 2
cert_rows
cert_pivot_2 3 7 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 26 314 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 426
cert_cover_5 3 1 0 2 4 6 298 426 3
cert_coverFacet 4 714
cert_cover_5 4 3 0 2 5 6 138 714 2
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 556 572 2
cert_coverFacet 6 620
cert_cover_5 6 2 1 2 4 5 556 620 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0028

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e11q2_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 199, 539, 403, 109, 793, 457, 526, 182, 566, 556, 484, 872, 944, 7, 11, 19, 131, 13, 69, 537, 73, 265, 273, 193, 385, 14, 54, 134, 518, 522, 146, 530, 44, 524, 100, 164, 548, 196, 104, 552, 328, 776, 176, 560, 400, 784, 352, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_199, vertices_539, vertices_403, vertices_109, vertices_793, vertices_457, vertices_526, vertices_182, vertices_566, vertices_556, vertices_484, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_19, vertices_131, vertices_13, vertices_69, vertices_537, vertices_73, vertices_265, vertices_273, vertices_193, vertices_385, vertices_14, vertices_54, vertices_134, vertices_518, vertices_522, vertices_146, vertices_530, vertices_44, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_400, vertices_784, vertices_352, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_199), (false, vertices_539), (false, vertices_403), (false, vertices_109), (false, vertices_793), (false, vertices_457), (true, vertices_54), (true, vertices_518), (true, vertices_524), (true, vertices_164), (true, vertices_548), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_352), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 17 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_539) then 18 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_109) then 13 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_2 0 0 1 3 4 54
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 6 54 182 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 8 54 566 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 484
cert_cover_5 4 1 1 4 5 6 100 484 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0029

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e11q2_0030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 205, 525, 837, 409, 537, 481, 62, 542, 614, 434, 866, 108, 248, 13, 69, 517, 25, 137, 521, 273, 529, 193, 321, 385, 769, 30, 38, 518, 50, 274, 530, 610, 290, 770, 44, 76, 524, 100, 580, 56, 152, 536, 104, 200, 176, 400, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_205, vertices_525, vertices_837, vertices_409, vertices_537, vertices_481, vertices_62, vertices_542, vertices_614, vertices_434, vertices_866, vertices_108, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_137, vertices_521, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_30, vertices_38, vertices_518, vertices_50, vertices_274, vertices_530, vertices_610, vertices_290, vertices_770, vertices_44, vertices_76, vertices_524, vertices_100, vertices_580, vertices_56, vertices_152, vertices_536, vertices_104, vertices_200, vertices_176, vertices_400, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_205), (false, vertices_525), (false, vertices_837), (false, vertices_409), (false, vertices_537), (false, vertices_481), (true, vertices_30), (true, vertices_38), (true, vertices_518), (true, vertices_50), (true, vertices_610), (true, vertices_290), (true, vertices_44), (true, vertices_100), (true, vertices_56), (true, vertices_104), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_205) then 12 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_837) then 13 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_30) then 14 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_610) then 17 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_176) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_610), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_2 1 0 4 5 8 610
cert_row_4 2 0 3 4 6 7 434 50 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 4 30 62 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 5 38 614 3
cert_coverFacet 3 434
cert_cover_5 3 2 0 3 4 6 50 434 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 610 866 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0030

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e11q2_0032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 205, 589, 789, 421, 409, 806, 218, 618, 242, 306, 786, 740, 432, 77, 133, 261, 517, 25, 137, 521, 273, 529, 385, 26, 74, 522, 50, 210, 274, 530, 98, 290, 546, 770, 164, 292, 548, 196, 580, 772, 152, 200, 584, 176, 304, 400, 784, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_205, vertices_589, vertices_789, vertices_421, vertices_409, vertices_806, vertices_218, vertices_618, vertices_242, vertices_306, vertices_786, vertices_740, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_273, vertices_529, vertices_385, vertices_26, vertices_74, vertices_522, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_770, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_772, vertices_152, vertices_200, vertices_584, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_205), (false, vertices_589), (false, vertices_789), (false, vertices_421), (false, vertices_409), (true, vertices_74), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_548), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 13 else
  if p.val = (false, vertices_205) then 16 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_409) then 18 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 5 74 618 2
cert_coverFacet 3 242
cert_cover_5 3 0 0 3 4 5 50 242 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0032

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e11q2_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 285, 541, 425, 369, 689, 206, 590, 626, 226, 674, 396, 852, 484, 29, 137, 265, 521, 49, 273, 529, 161, 289, 641, 78, 138, 522, 98, 162, 546, 194, 578, 642, 140, 268, 524, 276, 532, 196, 324, 580, 388, 392, 112, 560, 336, 592, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_285, vertices_541, vertices_425, vertices_369, vertices_689, vertices_206, vertices_590, vertices_626, vertices_226, vertices_674, vertices_396, vertices_852, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_78, vertices_138, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_392, vertices_112, vertices_560, vertices_336, vertices_592, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_285), (false, vertices_541), (false, vertices_425), (false, vertices_369), (false, vertices_689), (true, vertices_78), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_140), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_285) then 16 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_78) then 14 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 5 8 626 98 1
cert_row_4 2 1 3 5 7 8 852 276 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 98 626 1
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 852
cert_cover_5 6 2 1 3 5 7 276 852 2
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 196 484 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0033

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e11q2_0034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 157, 653, 345, 809, 721, 558, 166, 710, 466, 418, 802, 316, 436, 141, 25, 265, 521, 81, 145, 321, 577, 641, 769, 38, 134, 518, 162, 290, 546, 194, 322, 578, 386, 770, 28, 44, 524, 308, 148, 164, 644, 280, 296, 552, 208, 336, 400, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_157, vertices_653, vertices_345, vertices_809, vertices_721, vertices_558, vertices_166, vertices_710, vertices_466, vertices_418, vertices_802, vertices_316, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_769, vertices_38, vertices_134, vertices_518, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_44, vertices_524, vertices_308, vertices_148, vertices_164, vertices_644, vertices_280, vertices_296, vertices_552, vertices_208, vertices_336, vertices_400, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_157), (false, vertices_653), (false, vertices_345), (false, vertices_809), (false, vertices_721), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_386), (true, vertices_44), (true, vertices_308), (true, vertices_164), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_157) then 15 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_308) then 17 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 38 2
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 0 3 5 6 7 466 194 1
cert_rows
cert_pivot_2 2 4 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 38 558 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 466
cert_cover_5 3 3 0 3 5 6 194 466 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 4 28 316 3
cert_coverFacet 7 436
cert_cover_5 7 1 1 3 4 6 308 436 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0034

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e11q2_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 211, 659, 355, 345, 817, 654, 166, 226, 796, 236, 364, 804, 728, 147, 35, 67, 515, 81, 273, 529, 289, 545, 321, 38, 134, 518, 98, 162, 194, 642, 108, 140, 268, 524, 164, 292, 548, 772, 88, 280, 536, 200, 328, 648, 208, 656, 784, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_211, vertices_659, vertices_355, vertices_345, vertices_817, vertices_654, vertices_166, vertices_226, vertices_796, vertices_236, vertices_364, vertices_804, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_35, vertices_67, vertices_515, vertices_81, vertices_273, vertices_529, vertices_289, vertices_545, vertices_321, vertices_38, vertices_134, vertices_518, vertices_98, vertices_162, vertices_194, vertices_642, vertices_108, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_648, vertices_208, vertices_656, vertices_784, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_211), (false, vertices_659), (false, vertices_355), (false, vertices_345), (false, vertices_817), (true, vertices_134), (true, vertices_162), (true, vertices_108), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_772), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_211) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_108) then 14 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 226
cert_cover_2 2 4 0 5 6 98 226 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 268 796 2
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 6 108 236 3
cert_coverFacet 5 364
cert_cover_5 5 0 1 2 4 7 108 364 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0036

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e11q2_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 61, 541, 233, 841, 689, 782, 662, 278, 242, 370, 834, 364, 308, 29, 41, 73, 521, 49, 529, 161, 193, 577, 641, 22, 262, 518, 114, 146, 274, 194, 322, 578, 642, 770, 44, 268, 524, 52, 276, 532, 292, 104, 328, 776, 176, 304, 656, 224, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_61, vertices_541, vertices_233, vertices_841, vertices_689, vertices_782, vertices_662, vertices_278, vertices_242, vertices_370, vertices_834, vertices_364, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_41, vertices_73, vertices_521, vertices_49, vertices_529, vertices_161, vertices_193, vertices_577, vertices_641, vertices_22, vertices_262, vertices_518, vertices_114, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_104, vertices_328, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_61), (false, vertices_541), (false, vertices_233), (false, vertices_841), (false, vertices_689), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_114) then 14 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 22 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 2 7 8 782 262 2
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 262 782 2
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 22 662 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 6 114 242 3
cert_coverFacet 4 370
cert_cover_5 4 1 0 3 4 7 114 370 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0037

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e11q2_0038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 157, 541, 421, 837, 457, 806, 570, 218, 306, 466, 834, 692, 432, 29, 133, 261, 517, 73, 137, 521, 321, 577, 385, 26, 74, 522, 50, 210, 274, 290, 546, 322, 578, 770, 148, 532, 164, 292, 548, 772, 152, 536, 200, 176, 304, 560, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_157, vertices_541, vertices_421, vertices_837, vertices_457, vertices_806, vertices_570, vertices_218, vertices_306, vertices_466, vertices_834, vertices_692, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_321, vertices_577, vertices_385, vertices_26, vertices_74, vertices_522, vertices_50, vertices_210, vertices_274, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_772, vertices_152, vertices_536, vertices_200, vertices_176, vertices_304, vertices_560, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_157), (false, vertices_541), (false, vertices_421), (false, vertices_837), (false, vertices_457), (true, vertices_26), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_548), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 218
cert_cover_5 2 0 0 2 3 5 26 218 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 7 210 466 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 148 692 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0038

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e11q2_0039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 805, 217, 689, 849, 449, 558, 206, 294, 454, 666, 674, 348, 796, 81, 145, 529, 161, 289, 545, 193, 321, 385, 769, 14, 38, 198, 262, 138, 522, 162, 290, 546, 386, 642, 284, 76, 524, 292, 548, 324, 772, 88, 152, 536, 200, 336, 656, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_805, vertices_217, vertices_689, vertices_849, vertices_449, vertices_558, vertices_206, vertices_294, vertices_454, vertices_666, vertices_674, vertices_348, vertices_796] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_14, vertices_38, vertices_198, vertices_262, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_284, vertices_76, vertices_524, vertices_292, vertices_548, vertices_324, vertices_772, vertices_88, vertices_152, vertices_536, vertices_200, vertices_336, vertices_656, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_805), (false, vertices_217), (false, vertices_689), (false, vertices_849), (false, vertices_449), (true, vertices_14), (true, vertices_38), (true, vertices_198), (true, vertices_262), (true, vertices_138), (true, vertices_522), (true, vertices_546), (true, vertices_642), (true, vertices_284), (true, vertices_76), (true, vertices_524), (true, vertices_324), (true, vertices_536)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_198) then 14 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_284) then 17 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_536) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 1 2 4 8 558 14 3
cert_row_4 3 0 2 3 6 8 666 138 2
cert_rows
cert_pivot_2 5 7 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 14 558 3
cert_coverFacet 1 206
cert_cover_5 1 0 0 1 2 5 14 206 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 454
cert_cover_5 3 0 0 1 5 7 198 454 3
cert_coverFacet 4 666
cert_cover_5 4 3 0 2 3 6 138 666 2
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 348
cert_cover_5 6 1 1 2 3 5 284 348 3
cert_coverFacet 7 796
cert_cover_5 7 1 1 2 3 8 284 796 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0039

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e11q2_0040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 555, 397, 805, 709, 665, 614, 602, 410, 114, 306, 244, 436, 720, 43, 133, 261, 517, 137, 265, 521, 289, 545, 641, 26, 266, 522, 50, 82, 274, 98, 290, 546, 578, 180, 100, 292, 548, 196, 580, 388, 152, 536, 392, 112, 304, 208, 592, 400, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_555, vertices_397, vertices_805, vertices_709, vertices_665, vertices_614, vertices_602, vertices_410, vertices_114, vertices_306, vertices_244, vertices_436, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_289, vertices_545, vertices_641, vertices_26, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_578, vertices_180, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_152, vertices_536, vertices_392, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_555), (false, vertices_397), (false, vertices_805), (false, vertices_709), (false, vertices_665), (true, vertices_26), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_578), (true, vertices_180), (true, vertices_100), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_665) then 17 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_180) then 21 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_2 1 1 3 4 6 180
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 7 6 1 0
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 602
cert_cover_5 1 3 0 2 3 5 26 602 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 6 26 410 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 244
cert_cover_5 5 1 1 3 4 5 180 244 3
cert_coverFacet 6 436
cert_cover_5 6 1 1 3 4 7 180 436 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0040

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e11q2_0041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 805, 601, 465, 785, 737, 94, 174, 342, 294, 714, 450, 796, 684, 81, 273, 529, 161, 289, 545, 193, 577, 385, 769, 14, 86, 38, 262, 74, 138, 162, 290, 194, 322, 386, 28, 172, 524, 276, 292, 548, 772, 88, 536, 584, 648, 336, 784, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_805, vertices_601, vertices_465, vertices_785, vertices_737, vertices_94, vertices_174, vertices_342, vertices_294, vertices_714, vertices_450, vertices_796, vertices_684] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_86, vertices_38, vertices_262, vertices_74, vertices_138, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_172, vertices_524, vertices_276, vertices_292, vertices_548, vertices_772, vertices_88, vertices_536, vertices_584, vertices_648, vertices_336, vertices_784, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_805), (false, vertices_601), (false, vertices_465), (false, vertices_785), (false, vertices_737), (true, vertices_14), (true, vertices_86), (true, vertices_38), (true, vertices_262), (true, vertices_74), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_28), (true, vertices_172), (true, vertices_524), (true, vertices_276), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_172) then 17 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_648) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 6 172
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_2 2 0 1 3 5 86
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 3 14 94 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 14 174 3
cert_coverFacet 2 342
cert_cover_5 2 2 0 1 3 7 86 342 3
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 714
cert_cover_5 4 1 0 2 5 6 74 714 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 28 796 3
cert_coverFacet 7 684
cert_cover_5 7 0 1 2 4 8 172 684 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0041

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e11q2_0042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 61, 541, 421, 361, 905, 214, 598, 842, 482, 898, 180, 632, 240, 29, 37, 133, 517, 41, 265, 521, 289, 385, 641, 86, 134, 518, 194, 322, 578, 386, 642, 770, 52, 148, 532, 164, 56, 536, 104, 328, 584, 776, 112, 176, 208, 592, 224, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_61, vertices_541, vertices_421, vertices_361, vertices_905, vertices_214, vertices_598, vertices_842, vertices_482, vertices_898, vertices_180, vertices_632, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_289, vertices_385, vertices_641, vertices_86, vertices_134, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_532, vertices_164, vertices_56, vertices_536, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_61), (false, vertices_541), (false, vertices_421), (false, vertices_361), (false, vertices_905), (true, vertices_86), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_148), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_194) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 842
cert_cover_5 2 2 0 2 5 7 322 842 1
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 194 482 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 56 632 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0042

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e11q2_0043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 173, 269, 341, 149, 809, 913, 118, 182, 618, 466, 962, 108, 844, 13, 21, 133, 261, 41, 265, 145, 273, 161, 545, 641, 769, 54, 82, 146, 98, 162, 546, 450, 578, 642, 44, 76, 268, 84, 148, 100, 164, 324, 104, 552, 584, 776, 336, 400, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_173, vertices_269, vertices_341, vertices_149, vertices_809, vertices_913, vertices_118, vertices_182, vertices_618, vertices_466, vertices_962, vertices_108, vertices_844] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_261, vertices_41, vertices_265, vertices_145, vertices_273, vertices_161, vertices_545, vertices_641, vertices_769, vertices_54, vertices_82, vertices_146, vertices_98, vertices_162, vertices_546, vertices_450, vertices_578, vertices_642, vertices_44, vertices_76, vertices_268, vertices_84, vertices_148, vertices_100, vertices_164, vertices_324, vertices_104, vertices_552, vertices_584, vertices_776, vertices_336, vertices_400, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_173), (false, vertices_269), (false, vertices_341), (false, vertices_149), (false, vertices_809), (false, vertices_913), (true, vertices_54), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_450), (true, vertices_578), (true, vertices_76), (true, vertices_100), (true, vertices_104), (true, vertices_584), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_173) then 12 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_450) then 17 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 5 54 118 3
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 6 54 182 3
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 5 98 618 1
cert_coverFacet 3 466
cert_cover_5 3 1 0 3 5 6 82 466 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 8 450 962 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 76 844 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0043

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e11q2_0044.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0044

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 93, 341, 793, 713, 481, 62, 278, 422, 570, 786, 738, 620, 356, 85, 25, 73, 521, 273, 193, 321, 385, 641, 769, 22, 38, 262, 58, 274, 530, 162, 546, 386, 642, 770, 28, 44, 76, 276, 100, 292, 324, 536, 552, 584, 784, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_93, vertices_341, vertices_793, vertices_713, vertices_481, vertices_62, vertices_278, vertices_422, vertices_570, vertices_786, vertices_738, vertices_620, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_25, vertices_73, vertices_521, vertices_273, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_262, vertices_58, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_276, vertices_100, vertices_292, vertices_324, vertices_536, vertices_552, vertices_584, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_93), (false, vertices_341), (false, vertices_793), (false, vertices_713), (false, vertices_481), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_58), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_44), (true, vertices_100), (true, vertices_292), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 7 422 38 3
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 22 62 2
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 38 422 3
cert_coverFacet 3 570
cert_cover_5 3 0 0 2 3 8 58 570 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0044

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0390 : Certifies 390 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0007.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0391 : Certifies 391 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0392 : Certifies 392 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0393 : Certifies 393 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0394 : Certifies 394 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0395 : Certifies 395 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0396 : Certifies 396 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0397 : Certifies 397 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0014.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0398 : Certifies 398 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0399 : Certifies 399 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0400 : Certifies 400 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0401 : Certifies 401 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0402 : Certifies 402 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0403 : Certifies 403 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0404 : Certifies 404 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0025.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0405 : Certifies 405 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0406 : Certifies 406 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0407 : Certifies 407 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0408 : Certifies 408 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0409 : Certifies 409 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0410 : Certifies 410 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0411 : Certifies 411 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0412 : Certifies 412 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0413 : Certifies 413 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0414 : Certifies 414 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0415 : Certifies 415 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0416 : Certifies 416 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0417 : Certifies 417 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0418 : Certifies 418 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0419 : Certifies 419 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0044.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B013 (j : Fin 30) :
    Certifies (390 + j.val) := by
  fin_cases j
  · exact projection_0390
  · exact projection_0391
  · exact projection_0392
  · exact projection_0393
  · exact projection_0394
  · exact projection_0395
  · exact projection_0396
  · exact projection_0397
  · exact projection_0398
  · exact projection_0399
  · exact projection_0400
  · exact projection_0401
  · exact projection_0402
  · exact projection_0403
  · exact projection_0404
  · exact projection_0405
  · exact projection_0406
  · exact projection_0407
  · exact projection_0408
  · exact projection_0409
  · exact projection_0410
  · exact projection_0411
  · exact projection_0412
  · exact projection_0413
  · exact projection_0414
  · exact projection_0415
  · exact projection_0416
  · exact projection_0417
  · exact projection_0418
  · exact projection_0419

end Nonrational.TerminalVerification
