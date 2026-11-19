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
/- Source: ProjectionCertificates/R_m16e10q1_0436.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0436

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 395, 803, 569, 665, 361, 198, 582, 466, 834, 124, 692, 212, 868, 344, 408, 131, 259, 515, 537, 41, 137, 265, 289, 545, 641, 70, 134, 518, 194, 322, 578, 386, 770, 52, 84, 148, 100, 548, 196, 580, 644, 56, 88, 152, 280, 104, 328, 392, 560, 208, 336, 400, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_395, vertices_803, vertices_569, vertices_665, vertices_361, vertices_198, vertices_582, vertices_466, vertices_834, vertices_124, vertices_692, vertices_212, vertices_868, vertices_344, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_537, vertices_41, vertices_137, vertices_265, vertices_289, vertices_545, vertices_641, vertices_70, vertices_134, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_84, vertices_148, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_328, vertices_392, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_395), (false, vertices_803), (false, vertices_569), (false, vertices_665), (false, vertices_361), (true, vertices_70), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 0 3 5 6 7 466 194 1
cert_row_4 1 1 2 3 4 5 124 52 1
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 198
cert_cover_2 0 1 0 5 6 70 198 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 194 466 1
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 124
cert_cover_5 4 1 1 2 3 4 52 124 1
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 52 692 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 100 868 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0436

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0437.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0437

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 563, 163, 451, 333, 617, 225, 182, 658, 898, 604, 284, 628, 404, 484, 920, 35, 131, 259, 515, 73, 265, 521, 97, 161, 545, 193, 321, 50, 146, 530, 162, 386, 642, 770, 28, 76, 268, 52, 596, 148, 276, 100, 164, 324, 388, 280, 536, 584, 776, 560, 400, 656, 224, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_563, vertices_163, vertices_451, vertices_333, vertices_617, vertices_225, vertices_182, vertices_658, vertices_898, vertices_604, vertices_284, vertices_628, vertices_404, vertices_484, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_50, vertices_146, vertices_530, vertices_162, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_52, vertices_596, vertices_148, vertices_276, vertices_100, vertices_164, vertices_324, vertices_388, vertices_280, vertices_536, vertices_584, vertices_776, vertices_560, vertices_400, vertices_656, vertices_224, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_563), (false, vertices_163), (false, vertices_451), (false, vertices_333), (false, vertices_617), (false, vertices_225), (true, vertices_146), (true, vertices_642), (true, vertices_28), (true, vertices_52), (true, vertices_596), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_388), (true, vertices_280), (true, vertices_536), (true, vertices_400), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_596) then 22 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 163 225 146 642 28 52 148 276 100 164 388 280 536 400 656 896 779 563 451 333 596 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 50 1
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_2 2 1 3 5 8 596
cert_row_4 3 2 3 6 7 8 920 280 2
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 50 182 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 28 604 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 52 628 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 484
cert_cover_5 7 1 1 4 5 6 100 484 3
cert_coverFacet 8 920
cert_cover_5 8 3 2 3 6 7 280 920 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0437

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0438.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0438

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 837, 345, 617, 393, 166, 806, 122, 178, 466, 866, 692, 568, 408, 664, 133, 261, 517, 73, 137, 265, 521, 321, 577, 385, 38, 134, 262, 50, 82, 146, 98, 162, 802, 322, 386, 164, 548, 644, 772, 56, 88, 152, 280, 536, 104, 552, 392, 648, 176, 560, 336, 400, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_837, vertices_345, vertices_617, vertices_393, vertices_166, vertices_806, vertices_122, vertices_178, vertices_466, vertices_866, vertices_692, vertices_568, vertices_408, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_385, vertices_38, vertices_134, vertices_262, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_802, vertices_322, vertices_386, vertices_164, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_392, vertices_648, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_837), (false, vertices_345), (false, vertices_617), (false, vertices_393), (true, vertices_38), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_802), (true, vertices_322), (true, vertices_164), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_560), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_617) then 25 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_802) then 19 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 5 122 50 1
cert_row_4 1 0 3 5 6 7 466 82 3
cert_row_2 2 0 4 7 8 802
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 806
cert_cover_5 1 2 0 1 4 7 38 806 3
cert_coverFacet 2 122
cert_cover_5 2 0 0 2 3 4 50 122 1
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 82 466 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 98 866 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 164 692 1
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0438

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0439.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0439

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 397, 613, 421, 713, 241, 286, 774, 538, 370, 722, 834, 804, 440, 664, 864, 13, 37, 389, 517, 137, 521, 97, 161, 193, 577, 14, 262, 518, 26, 522, 82, 274, 530, 322, 578, 770, 268, 292, 548, 772, 152, 280, 536, 392, 648, 112, 176, 304, 208, 656, 352, 608, 416, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_397, vertices_613, vertices_421, vertices_713, vertices_241, vertices_286, vertices_774, vertices_538, vertices_370, vertices_722, vertices_834, vertices_804, vertices_440, vertices_664, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_389, vertices_517, vertices_137, vertices_521, vertices_97, vertices_161, vertices_193, vertices_577, vertices_14, vertices_262, vertices_518, vertices_26, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_268, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_208, vertices_656, vertices_352, vertices_608, vertices_416, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_397), (false, vertices_613), (false, vertices_421), (false, vertices_713), (false, vertices_241), (true, vertices_262), (true, vertices_26), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_304), (true, vertices_656), (true, vertices_352), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 18 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_800) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 7 286 14 3
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 3 4 5 7 370 82 2
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 82 370 2
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 152 440 2
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 864
cert_cover_2 9 5 4 7 8 352 864 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0439

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0440.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0440

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 565, 313, 537, 713, 865, 206, 182, 806, 838, 394, 418, 724, 408, 664, 432, 25, 73, 265, 521, 49, 529, 289, 545, 321, 577, 38, 70, 134, 774, 74, 138, 266, 162, 290, 322, 386, 52, 148, 532, 548, 196, 580, 152, 280, 536, 200, 392, 648, 176, 304, 400, 656, 416, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_565, vertices_313, vertices_537, vertices_713, vertices_865, vertices_206, vertices_182, vertices_806, vertices_838, vertices_394, vertices_418, vertices_724, vertices_408, vertices_664, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_49, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_38, vertices_70, vertices_134, vertices_774, vertices_74, vertices_138, vertices_266, vertices_162, vertices_290, vertices_322, vertices_386, vertices_52, vertices_148, vertices_532, vertices_548, vertices_196, vertices_580, vertices_152, vertices_280, vertices_536, vertices_200, vertices_392, vertices_648, vertices_176, vertices_304, vertices_400, vertices_656, vertices_416, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_565), (false, vertices_313), (false, vertices_537), (false, vertices_713), (false, vertices_865), (true, vertices_38), (true, vertices_70), (true, vertices_134), (true, vertices_774), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_152), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_774) then 19 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 1 2 5 6 206 70 2
cert_row_4 2 0 1 3 4 6 182 38 2
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 70 206 2
cert_coverFacet 1 182
cert_cover_5 1 2 0 1 3 4 38 182 2
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 38 806 3
cert_coverFacet 3 838
cert_cover_5 3 0 0 1 5 7 70 838 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0440

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0441.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0441

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 789, 665, 241, 305, 865, 542, 206, 358, 774, 650, 834, 284, 236, 300, 440, 49, 145, 273, 529, 97, 289, 193, 577, 641, 769, 14, 70, 262, 518, 138, 522, 194, 322, 578, 642, 770, 28, 44, 204, 268, 276, 532, 100, 292, 772, 152, 280, 536, 168, 296, 648, 176, 304, 224, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_789, vertices_665, vertices_241, vertices_305, vertices_865, vertices_542, vertices_206, vertices_358, vertices_774, vertices_650, vertices_834, vertices_284, vertices_236, vertices_300, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_204, vertices_268, vertices_276, vertices_532, vertices_100, vertices_292, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_648, vertices_176, vertices_304, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_789), (false, vertices_665), (false, vertices_241), (false, vertices_305), (false, vertices_865), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_322), (true, vertices_770), (true, vertices_28), (true, vertices_44), (true, vertices_204), (true, vertices_268), (true, vertices_100), (true, vertices_292), (true, vertices_280), (true, vertices_168), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_204) then 21 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_100) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_168) then 15 else
  if p.val = (true, vertices_296) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_4 1 0 1 4 5 7 358 70 2
cert_row_2 2 1 2 5 6 204
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 206
cert_cover_5 1 2 0 1 2 5 14 206 3
cert_coverFacet 2 358
cert_cover_5 2 1 0 1 4 5 70 358 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 236
cert_cover_5 7 2 1 2 4 5 44 236 3
cert_coverFacet 8 300
cert_cover_2 8 2 1 4 7 44 300 3
cert_coverFacet 9 440
cert_cover_5 9 3 2 3 4 6 152 440 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0441

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0442.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0442

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 589, 85, 789, 241, 401, 865, 654, 170, 298, 842, 914, 124, 188, 660, 360, 21, 69, 517, 81, 145, 273, 97, 161, 289, 577, 385, 769, 42, 138, 266, 522, 162, 290, 386, 642, 770, 60, 76, 140, 524, 84, 148, 532, 644, 104, 168, 296, 328, 584, 112, 176, 400, 656, 784, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_589, vertices_85, vertices_789, vertices_241, vertices_401, vertices_865, vertices_654, vertices_170, vertices_298, vertices_842, vertices_914, vertices_124, vertices_188, vertices_660, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_644, vertices_104, vertices_168, vertices_296, vertices_328, vertices_584, vertices_112, vertices_176, vertices_400, vertices_656, vertices_784, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_589), (false, vertices_85), (false, vertices_789), (false, vertices_241), (false, vertices_401), (false, vertices_865), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_642), (true, vertices_770), (true, vertices_60), (true, vertices_140), (true, vertices_148), (true, vertices_644), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_60) then 21 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 2 6 8 654 138 1
cert_row_4 2 0 2 5 7 8 842 266 2
cert_row_4 3 0 3 6 7 8 914 386 1
cert_rows
cert_pivot_2 4 1 2 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 138 654 1
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 266 842 2
cert_coverFacet 4 914
cert_cover_5 4 3 0 3 6 7 386 914 1
cert_coverFacet 5 124
cert_cover_5 5 0 1 2 3 5 60 124 3
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 6 60 188 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0442

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0443.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0443

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 403, 227, 771, 309, 177, 865, 398, 202, 778, 220, 604, 812, 564, 404, 752, 67, 131, 259, 515, 49, 145, 273, 97, 161, 289, 577, 769, 74, 138, 266, 522, 194, 386, 770, 92, 140, 268, 524, 52, 148, 276, 532, 292, 548, 388, 200, 584, 776, 176, 560, 208, 592, 400, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_403, vertices_227, vertices_771, vertices_309, vertices_177, vertices_865, vertices_398, vertices_202, vertices_778, vertices_220, vertices_604, vertices_812, vertices_564, vertices_404, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_577, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_386, vertices_770, vertices_92, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_388, vertices_200, vertices_584, vertices_776, vertices_176, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_403), (false, vertices_227), (false, vertices_771), (false, vertices_309), (false, vertices_177), (false, vertices_865), (true, vertices_138), (true, vertices_266), (true, vertices_92), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_388), (true, vertices_200), (true, vertices_776), (true, vertices_560), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_92) then 22 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_4 1 1 2 4 7 8 812 268 2
cert_row_2 2 1 2 3 5 92
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 6 92 220 3
cert_coverFacet 4 604
cert_cover_5 4 2 1 2 3 8 92 604 3
cert_coverFacet 5 812
cert_cover_5 5 1 1 2 4 7 268 812 2
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0443

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0444.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0444

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 555, 403, 227, 661, 277, 105, 713, 418, 802, 348, 604, 812, 360, 496, 720, 35, 131, 259, 515, 21, 261, 517, 41, 73, 521, 145, 273, 97, 193, 641, 162, 290, 546, 386, 770, 92, 268, 524, 276, 532, 772, 104, 296, 552, 328, 584, 208, 336, 592, 400, 656, 224, 352, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_555, vertices_403, vertices_227, vertices_661, vertices_277, vertices_105, vertices_713, vertices_418, vertices_802, vertices_348, vertices_604, vertices_812, vertices_360, vertices_496, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_21, vertices_261, vertices_517, vertices_41, vertices_73, vertices_521, vertices_145, vertices_273, vertices_97, vertices_193, vertices_641, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_92, vertices_268, vertices_524, vertices_276, vertices_532, vertices_772, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_555), (false, vertices_403), (false, vertices_227), (false, vertices_661), (false, vertices_277), (false, vertices_105), (false, vertices_713), (true, vertices_290), (true, vertices_92), (true, vertices_268), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_352), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_227) then 20 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_92) then 16 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
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
cert_row_4 0 1 2 4 7 8 812 268 2
cert_row_2 1 1 2 3 5 92
cert_row_4 2 3 4 5 6 7 496 208 1
cert_rows_3
cert_pivot_3 1 8 3
cert_heightProof 3
cert_coverFacet 0 418
cert_cover_2 0 4 0 6 7 162 418 3
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 348
cert_cover_5 2 1 1 2 3 7 92 348 3
cert_coverFacet 3 604
cert_cover_5 3 1 1 2 3 8 92 604 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 268 812 2
cert_coverFacet 5 360
cert_cover_2 5 4 2 5 7 104 360 3
cert_coverFacet 6 496
cert_cover_5 6 2 3 4 5 6 208 496 1
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0444

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0445.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0445

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 211, 803, 643, 677, 89, 409, 417, 710, 834, 572, 604, 436, 212, 312, 872, 67, 131, 259, 515, 25, 73, 265, 81, 145, 161, 289, 545, 385, 641, 194, 322, 578, 642, 770, 540, 52, 84, 148, 164, 548, 196, 580, 644, 56, 88, 280, 296, 552, 328, 584, 304, 208, 400, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_211, vertices_803, vertices_643, vertices_677, vertices_89, vertices_409, vertices_417, vertices_710, vertices_834, vertices_572, vertices_604, vertices_436, vertices_212, vertices_312, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_25, vertices_73, vertices_265, vertices_81, vertices_145, vertices_161, vertices_289, vertices_545, vertices_385, vertices_641, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_540, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_304, vertices_208, vertices_400, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_211), (false, vertices_803), (false, vertices_643), (false, vertices_677), (false, vertices_89), (false, vertices_409), (false, vertices_417), (true, vertices_578), (true, vertices_540), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_56), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_211) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_89) then 1 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_417) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_540) then 21 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_89), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 1 3 4 6 7 436 52 3
cert_row_2 2 1 2 3 8 540
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 834
cert_cover_2 1 5 0 7 8 322 834 3
cert_coverFacet 2 572
cert_cover_5 2 2 1 2 3 4 540 572 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 540 604 3
cert_coverFacet 4 436
cert_cover_5 4 1 1 3 4 6 52 436 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 296 872 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0445

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0446.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0446

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 203, 659, 355, 293, 837, 601, 153, 226, 674, 796, 436, 692, 408, 488, 840, 35, 67, 131, 515, 37, 261, 517, 25, 73, 137, 145, 529, 289, 321, 577, 98, 162, 546, 194, 642, 180, 276, 532, 292, 548, 772, 152, 280, 536, 200, 328, 584, 392, 776, 400, 656, 224, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_203, vertices_659, vertices_355, vertices_293, vertices_837, vertices_601, vertices_153, vertices_226, vertices_674, vertices_796, vertices_436, vertices_692, vertices_408, vertices_488, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_515, vertices_37, vertices_261, vertices_517, vertices_25, vertices_73, vertices_137, vertices_145, vertices_529, vertices_289, vertices_321, vertices_577, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_180, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_203), (false, vertices_659), (false, vertices_355), (false, vertices_293), (false, vertices_837), (false, vertices_601), (false, vertices_153), (true, vertices_162), (true, vertices_180), (true, vertices_276), (true, vertices_532), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_400), (true, vertices_224), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 14 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_355) then 20 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_837) then 15 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_180) then 16 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 7 8 796 276 1
cert_row_2 1 1 3 4 6 180
cert_row_4 2 2 4 5 6 7 488 200 1
cert_rows_3
cert_pivot_3 1 8 2
cert_heightProof 3
cert_coverFacet 0 226
cert_cover_2 0 4 0 5 6 98 226 3
cert_coverFacet 1 674
cert_cover_2 1 4 0 6 8 162 674 3
cert_coverFacet 2 796
cert_cover_5 2 0 1 2 3 7 276 796 1
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 7 180 436 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 8 180 692 3
cert_coverFacet 5 408
cert_cover_2 5 3 2 6 7 152 408 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 6 200 488 1
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0446

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0447.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0447

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 341, 601, 457, 817, 897, 110, 142, 182, 618, 930, 332, 396, 628, 404, 432, 73, 137, 521, 81, 273, 529, 321, 385, 641, 769, 14, 38, 134, 106, 138, 522, 162, 546, 642, 76, 140, 268, 52, 84, 148, 276, 100, 324, 388, 328, 584, 392, 176, 304, 560, 592, 400, 608, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_341, vertices_601, vertices_457, vertices_817, vertices_897, vertices_110, vertices_142, vertices_182, vertices_618, vertices_930, vertices_332, vertices_396, vertices_628, vertices_404, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_81, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_134, vertices_106, vertices_138, vertices_522, vertices_162, vertices_546, vertices_642, vertices_76, vertices_140, vertices_268, vertices_52, vertices_84, vertices_148, vertices_276, vertices_100, vertices_324, vertices_388, vertices_328, vertices_584, vertices_392, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_608, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_341), (false, vertices_601), (false, vertices_457), (false, vertices_817), (false, vertices_897), (true, vertices_14), (true, vertices_38), (true, vertices_134), (true, vertices_106), (true, vertices_162), (true, vertices_546), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_100), (true, vertices_388), (true, vertices_176), (true, vertices_400), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_817) then 26 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_106) then 19 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 897 14 38 134 162 546 76 140 268 52 148 100 388 176 400 608 416 651 106 341 601 457 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 1 3 4 6 182 38 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 182
cert_cover_5 2 2 0 1 3 4 38 182 2
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 8 106 618 3
cert_coverFacet 4 930
cert_cover_5 4 1 0 4 6 7 162 930 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0447

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0448.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0448

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 181, 341, 561, 593, 481, 782, 234, 554, 458, 850, 652, 660, 788, 696, 21, 133, 261, 49, 81, 529, 97, 161, 545, 321, 577, 385, 42, 202, 266, 522, 98, 546, 322, 578, 770, 140, 268, 524, 148, 276, 532, 644, 772, 168, 552, 392, 648, 176, 560, 336, 592, 656, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_181, vertices_341, vertices_561, vertices_593, vertices_481, vertices_782, vertices_234, vertices_554, vertices_458, vertices_850, vertices_652, vertices_660, vertices_788, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_49, vertices_81, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_168, vertices_552, vertices_392, vertices_648, vertices_176, vertices_560, vertices_336, vertices_592, vertices_656, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_181), (false, vertices_341), (false, vertices_561), (false, vertices_593), (false, vertices_481), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_770), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
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
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_2 2 0 2 5 6 202
cert_row_4 3 2 3 4 6 8 696 168 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 234
cert_cover_5 1 2 0 2 4 5 42 234 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 458
cert_cover_5 3 2 0 2 5 7 202 458 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 322 850 1
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 696
cert_cover_5 8 3 2 3 4 6 168 696 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0448

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0449.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0449

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 611, 291, 653, 357, 197, 721, 906, 434, 690, 220, 332, 780, 376, 408, 624, 35, 259, 515, 69, 133, 261, 517, 97, 289, 193, 577, 641, 178, 290, 546, 386, 642, 770, 76, 140, 268, 524, 196, 324, 772, 88, 152, 280, 328, 392, 648, 776, 112, 304, 560, 208, 592, 400, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_611, vertices_291, vertices_653, vertices_357, vertices_197, vertices_721, vertices_906, vertices_434, vertices_690, vertices_220, vertices_332, vertices_780, vertices_376, vertices_408, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_178, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_772, vertices_88, vertices_152, vertices_280, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_611), (false, vertices_291), (false, vertices_653), (false, vertices_357), (false, vertices_197), (false, vertices_721), (true, vertices_178), (true, vertices_386), (true, vertices_642), (true, vertices_76), (true, vertices_268), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_178) then 19 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_4 0 0 2 6 7 8 906 386 1
cert_row_2 1 0 3 4 6 178
cert_row_4 2 1 2 3 5 6 220 76 2
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 906
cert_cover_5 0 0 0 2 6 7 386 906 1
cert_coverFacet 1 434
cert_cover_5 1 1 0 3 4 7 178 434 3
cert_coverFacet 2 690
cert_cover_5 2 1 0 3 4 8 178 690 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 76 220 2
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 88 376 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0449

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0450.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0450

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 557, 101, 709, 793, 233, 393, 838, 410, 242, 338, 706, 372, 820, 184, 568, 37, 69, 517, 41, 137, 265, 521, 97, 193, 385, 641, 769, 82, 146, 274, 194, 322, 578, 386, 642, 770, 308, 100, 548, 324, 580, 772, 56, 152, 280, 536, 168, 552, 392, 112, 176, 560, 336, 784, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_557, vertices_101, vertices_709, vertices_793, vertices_233, vertices_393, vertices_838, vertices_410, vertices_242, vertices_338, vertices_706, vertices_372, vertices_820, vertices_184, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_41, vertices_137, vertices_265, vertices_521, vertices_97, vertices_193, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_308, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_560, vertices_336, vertices_784, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_557), (false, vertices_101), (false, vertices_709), (false, vertices_793), (false, vertices_233), (false, vertices_393), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_308), (true, vertices_324), (true, vertices_772), (true, vertices_56), (true, vertices_152), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_308) then 21 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 2 3 6 7 410 146 1
cert_row_4 3 0 3 4 5 6 242 82 2
cert_rows
cert_pivot_2 8 1 2 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 146 410 1
cert_coverFacet 2 242
cert_cover_5 2 3 0 3 4 5 82 242 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 372
cert_cover_5 5 1 1 3 4 5 308 372 3
cert_coverFacet 6 820
cert_cover_5 6 1 1 3 4 8 308 820 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0450

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0451.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0451

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 339, 205, 525, 597, 665, 177, 481, 838, 810, 690, 594, 428, 780, 452, 680, 275, 13, 69, 517, 137, 521, 49, 81, 145, 529, 161, 289, 193, 321, 50, 82, 530, 290, 546, 322, 578, 770, 140, 268, 524, 196, 324, 580, 388, 772, 168, 296, 552, 648, 776, 176, 592, 656, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_339, vertices_205, vertices_525, vertices_597, vertices_665, vertices_177, vertices_481, vertices_838, vertices_810, vertices_690, vertices_594, vertices_428, vertices_780, vertices_452, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_275, vertices_13, vertices_69, vertices_517, vertices_137, vertices_521, vertices_49, vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_193, vertices_321, vertices_50, vertices_82, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_176, vertices_592, vertices_656, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_339), (false, vertices_205), (false, vertices_525), (false, vertices_597), (false, vertices_665), (false, vertices_177), (false, vertices_481), (true, vertices_530), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_772), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 290 810 1
cert_coverFacet 2 690
cert_cover_5 2 1 0 3 4 6 50 690 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 428
cert_cover_5 4 3 1 2 4 6 140 428 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0451

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0453.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0453

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 557, 53, 597, 233, 649, 369, 782, 394, 650, 850, 482, 188, 412, 788, 432, 21, 37, 517, 41, 137, 521, 49, 81, 97, 193, 577, 641, 138, 266, 522, 194, 322, 578, 386, 642, 770, 156, 44, 268, 524, 52, 276, 532, 772, 168, 392, 648, 176, 304, 336, 592, 400, 784, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_557, vertices_53, vertices_597, vertices_233, vertices_649, vertices_369, vertices_782, vertices_394, vertices_650, vertices_850, vertices_482, vertices_188, vertices_412, vertices_788, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_41, vertices_137, vertices_521, vertices_49, vertices_81, vertices_97, vertices_193, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_156, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_772, vertices_168, vertices_392, vertices_648, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_557), (false, vertices_53), (false, vertices_597), (false, vertices_233), (false, vertices_649), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_156), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_156) then 21 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 4 5 6 7 482 194 1
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 0 3 5 7 8 850 322 1
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 850
cert_cover_5 3 3 0 3 5 7 322 850 1
cert_coverFacet 4 482
cert_cover_5 4 0 0 4 5 6 194 482 1
cert_coverFacet 5 188
cert_cover_5 5 1 1 2 3 4 156 188 3
cert_coverFacet 6 412
cert_cover_5 6 1 1 2 3 7 156 412 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0453

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0454.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0454

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 299, 659, 547, 557, 269, 709, 370, 562, 402, 220, 412, 588, 344, 872, 752, 35, 131, 259, 515, 13, 133, 261, 517, 41, 265, 545, 641, 50, 146, 274, 530, 290, 546, 386, 156, 76, 268, 524, 196, 580, 388, 88, 280, 296, 552, 328, 584, 112, 560, 208, 336, 400, 656, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_299, vertices_659, vertices_547, vertices_557, vertices_269, vertices_709, vertices_370, vertices_562, vertices_402, vertices_220, vertices_412, vertices_588, vertices_344, vertices_872, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_545, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_156, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_299), (false, vertices_659), (false, vertices_547), (false, vertices_557), (false, vertices_269), (false, vertices_709), (true, vertices_50), (true, vertices_274), (true, vertices_156), (true, vertices_76), (true, vertices_88), (true, vertices_280), (true, vertices_328), (true, vertices_584), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_156) then 23 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 547 269 50 274 76 88 280 328 584 112 560 208 336 400 352 608 391 299 659 557 709 156
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 2 4 5 7 8 872 296 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 1 0 3 4 5 50 370 3
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 156 220 3
cert_coverFacet 4 412
cert_cover_5 4 0 1 2 3 7 156 412 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 872
cert_cover_5 7 2 2 4 5 7 296 872 2
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0454

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0455.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0455

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 147, 355, 707, 541, 837, 657, 234, 402, 418, 188, 556, 436, 804, 728, 872, 19, 67, 131, 259, 21, 261, 517, 145, 529, 321, 577, 641, 146, 274, 98, 162, 290, 194, 386, 28, 44, 524, 180, 276, 292, 548, 772, 152, 536, 104, 168, 552, 200, 584, 400, 656, 352, 416, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_147, vertices_355, vertices_707, vertices_541, vertices_837, vertices_657, vertices_234, vertices_402, vertices_418, vertices_188, vertices_556, vertices_436, vertices_804, vertices_728, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_259, vertices_21, vertices_261, vertices_517, vertices_145, vertices_529, vertices_321, vertices_577, vertices_641, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_194, vertices_386, vertices_28, vertices_44, vertices_524, vertices_180, vertices_276, vertices_292, vertices_548, vertices_772, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_400, vertices_656, vertices_352, vertices_416, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_147), (false, vertices_355), (false, vertices_707), (false, vertices_541), (false, vertices_837), (false, vertices_657), (true, vertices_162), (true, vertices_386), (true, vertices_44), (true, vertices_180), (true, vertices_292), (true, vertices_548), (true, vertices_152), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_400), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_180) then 23 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 147 657 162 386 44 292 548 152 104 168 552 200 584 400 416 800 279 355 707 541 837 180
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 6 180
cert_row_4 1 0 2 4 5 6 234 98 1
cert_row_4 2 2 3 5 6 8 728 152 2
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 234
cert_cover_5 0 1 0 2 4 5 98 234 1
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 4 28 188 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 436
cert_cover_5 5 0 1 3 4 7 180 436 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 728
cert_cover_5 7 2 2 3 5 6 152 728 2
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0455

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0456.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0456

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 395, 835, 345, 681, 585, 182, 534, 434, 786, 124, 852, 740, 312, 616, 424, 131, 259, 515, 73, 137, 265, 521, 321, 577, 641, 22, 134, 518, 178, 274, 530, 386, 770, 52, 84, 532, 100, 164, 580, 644, 56, 88, 280, 104, 168, 296, 552, 584, 392, 304, 336, 784, 608, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_395, vertices_835, vertices_345, vertices_681, vertices_585, vertices_182, vertices_534, vertices_434, vertices_786, vertices_124, vertices_852, vertices_740, vertices_312, vertices_616, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_22, vertices_134, vertices_518, vertices_178, vertices_274, vertices_530, vertices_386, vertices_770, vertices_52, vertices_84, vertices_532, vertices_100, vertices_164, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_584, vertices_392, vertices_304, vertices_336, vertices_784, vertices_608, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_395), (false, vertices_835), (false, vertices_345), (false, vertices_681), (false, vertices_585), (true, vertices_22), (true, vertices_178), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_164), (true, vertices_580), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_304), (true, vertices_784), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_395) then 20 else
  if p.val = (false, vertices_835) then 21 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_681) then 25 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_178) then 22 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 6 178
cert_row_4 1 1 2 3 4 5 124 52 1
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 22 182 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 434
cert_cover_5 2 0 0 3 4 7 178 434 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 124
cert_cover_5 4 1 1 2 3 4 52 124 1
cert_coverFacet 5 852
cert_cover_5 5 2 1 3 5 7 84 852 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0456

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0457.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0457

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 301, 781, 677, 233, 721, 310, 598, 774, 330, 778, 466, 564, 440, 456, 688, 269, 37, 517, 41, 73, 521, 161, 193, 577, 641, 22, 262, 518, 74, 266, 522, 82, 274, 322, 578, 770, 52, 532, 292, 548, 772, 168, 296, 200, 328, 392, 776, 176, 304, 560, 208, 592, 400, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_301, vertices_781, vertices_677, vertices_233, vertices_721, vertices_310, vertices_598, vertices_774, vertices_330, vertices_778, vertices_466, vertices_564, vertices_440, vertices_456, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_517, vertices_41, vertices_73, vertices_521, vertices_161, vertices_193, vertices_577, vertices_641, vertices_22, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_52, vertices_532, vertices_292, vertices_548, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_301), (false, vertices_781), (false, vertices_677), (false, vertices_233), (false, vertices_721), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_322), (true, vertices_770), (true, vertices_52), (true, vertices_532), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_4 1 0 1 3 4 7 310 22 3
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 2 3 4 6 7 440 168 1
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 22 310 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 5 22 598 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 466
cert_cover_5 5 2 0 3 5 6 82 466 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 168 440 1
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coverFacet 9 688
cert_cover_2 9 4 3 6 8 176 688 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0457

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0458.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0458

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 653, 789, 453, 281, 425, 230, 678, 838, 122, 554, 594, 312, 680, 496, 848, 133, 261, 517, 25, 137, 265, 521, 273, 529, 385, 166, 70, 518, 26, 42, 522, 82, 530, 98, 546, 578, 196, 324, 644, 772, 56, 280, 168, 296, 552, 648, 112, 304, 336, 592, 784, 224, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_653, vertices_789, vertices_453, vertices_281, vertices_425, vertices_230, vertices_678, vertices_838, vertices_122, vertices_554, vertices_594, vertices_312, vertices_680, vertices_496, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_273, vertices_529, vertices_385, vertices_166, vertices_70, vertices_518, vertices_26, vertices_42, vertices_522, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_280, vertices_168, vertices_296, vertices_552, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_653), (false, vertices_789), (false, vertices_453), (false, vertices_281), (false, vertices_425), (true, vertices_166), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_82), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_56), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (true, vertices_166) then 19 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 281 70 518 42 82 98 546 578 56 552 112 304 336 592 224 672 832 539 166 653 789 453 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 70 3
cert_row_2 1 0 1 4 6 166
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 1 0 1 4 5 166 230 3
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 8 166 678 3
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 7 70 838 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 26 122 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 594
cert_cover_2 5 3 0 5 8 82 594 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coverFacet 9 848
cert_cover_2 9 5 3 7 8 336 848 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0458

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0459.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0459

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 283, 899, 537, 425, 713, 118, 550, 370, 802, 236, 724, 932, 344, 600, 360, 19, 259, 515, 25, 137, 265, 521, 529, 385, 641, 22, 38, 518, 114, 274, 290, 546, 770, 84, 532, 100, 164, 548, 196, 644, 88, 280, 536, 104, 168, 296, 200, 328, 584, 336, 592, 352, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_283, vertices_899, vertices_537, vertices_425, vertices_713, vertices_118, vertices_550, vertices_370, vertices_802, vertices_236, vertices_724, vertices_932, vertices_344, vertices_600, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_25, vertices_137, vertices_265, vertices_521, vertices_529, vertices_385, vertices_641, vertices_22, vertices_38, vertices_518, vertices_114, vertices_274, vertices_290, vertices_546, vertices_770, vertices_84, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_88, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_336, vertices_592, vertices_352, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_283), (false, vertices_899), (false, vertices_537), (false, vertices_425), (false, vertices_713), (true, vertices_38), (true, vertices_114), (true, vertices_290), (true, vertices_546), (true, vertices_84), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_336), (true, vertices_592), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 18 else
  if p.val = (false, vertices_283) then 20 else
  if p.val = (false, vertices_899) then 21 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_114) then 22 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
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
cert_row_2 0 0 3 4 5 114
cert_row_4 1 1 2 4 5 6 236 100 1
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 550
cert_cover_2 1 1 0 4 8 38 550 3
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 7 114 370 3
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 5 100 236 1
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 84 724 3
cert_coverFacet 6 932
cert_cover_5 6 3 1 4 6 7 164 932 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0459

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0460.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0460

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 307, 163, 707, 589, 805, 673, 186, 402, 450, 220, 540, 468, 788, 824, 744, 35, 67, 131, 259, 69, 261, 517, 161, 289, 545, 577, 641, 50, 146, 274, 162, 194, 322, 386, 28, 76, 524, 212, 276, 532, 324, 772, 56, 152, 536, 168, 552, 200, 584, 304, 400, 784, 672, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_307, vertices_163, vertices_707, vertices_589, vertices_805, vertices_673, vertices_186, vertices_402, vertices_450, vertices_220, vertices_540, vertices_468, vertices_788, vertices_824, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_259, vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_577, vertices_641, vertices_50, vertices_146, vertices_274, vertices_162, vertices_194, vertices_322, vertices_386, vertices_28, vertices_76, vertices_524, vertices_212, vertices_276, vertices_532, vertices_324, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_304, vertices_400, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_307), (false, vertices_163), (false, vertices_707), (false, vertices_589), (false, vertices_805), (false, vertices_673), (true, vertices_146), (true, vertices_386), (true, vertices_28), (true, vertices_212), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_400), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 17 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_212) then 23 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 163 673 146 386 28 276 532 56 152 536 168 552 200 400 784 448 327 307 707 589 805 212
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 6 212
cert_row_4 1 0 2 3 4 6 186 50 1
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 1 0 2 3 4 50 186 1
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 28 220 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 468
cert_cover_5 5 0 1 3 5 7 212 468 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 824
cert_cover_5 7 2 2 3 4 7 56 824 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 168 744 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0460

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0461.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0461

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 557, 421, 837, 345, 297, 182, 566, 902, 218, 538, 706, 312, 568, 496, 960, 37, 261, 517, 41, 73, 265, 521, 289, 321, 577, 54, 134, 518, 26, 74, 522, 146, 530, 194, 578, 642, 164, 548, 388, 772, 56, 88, 280, 536, 296, 552, 176, 304, 560, 208, 336, 416, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_557, vertices_421, vertices_837, vertices_345, vertices_297, vertices_182, vertices_566, vertices_902, vertices_218, vertices_538, vertices_706, vertices_312, vertices_568, vertices_496, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_289, vertices_321, vertices_577, vertices_54, vertices_134, vertices_518, vertices_26, vertices_74, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_164, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_416, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_557), (false, vertices_421), (false, vertices_837), (false, vertices_345), (false, vertices_297), (true, vertices_54), (true, vertices_134), (true, vertices_518), (true, vertices_26), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_56), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_345) then 25 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (true, vertices_54) then 19 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_448) then 14 else
  if p.val = (true, vertices_704) then 15 else
  if p.val = (true, vertices_896) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 297 134 518 26 146 530 194 642 56 536 176 304 560 208 448 704 896 587 54 557 421 837 345
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_2 1 0 1 3 4 54
cert_row_4 2 0 2 3 5 6 218 26 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 6 54 182 3
cert_coverFacet 1 566
cert_cover_5 1 1 0 1 3 8 54 566 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 7 134 902 3
cert_coverFacet 3 218
cert_cover_5 3 2 0 2 3 5 26 218 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coverFacet 9 960
cert_cover_2 9 6 5 7 8 448 960 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0461

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0462.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0462

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 597, 405, 901, 617, 241, 286, 558, 774, 298, 482, 898, 540, 472, 600, 360, 21, 389, 517, 81, 145, 97, 161, 545, 577, 641, 14, 262, 518, 42, 266, 162, 290, 546, 386, 642, 770, 28, 524, 276, 532, 772, 88, 280, 536, 104, 296, 552, 328, 584, 208, 592, 400, 224, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_597, vertices_405, vertices_901, vertices_617, vertices_241, vertices_286, vertices_558, vertices_774, vertices_298, vertices_482, vertices_898, vertices_540, vertices_472, vertices_600, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_389, vertices_517, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_577, vertices_641, vertices_14, vertices_262, vertices_518, vertices_42, vertices_266, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_524, vertices_276, vertices_532, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_208, vertices_592, vertices_400, vertices_224, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_597), (false, vertices_405), (false, vertices_901), (false, vertices_617), (false, vertices_241), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_524), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_901) then 22 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_4 1 0 1 2 3 7 286 14 3
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 14 558 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 162 482 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0462

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0463.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0463

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 157, 269, 565, 357, 681, 297, 838, 218, 346, 786, 738, 284, 788, 612, 488, 13, 21, 37, 261, 41, 137, 265, 145, 529, 289, 545, 641, 90, 146, 274, 530, 194, 322, 578, 642, 770, 28, 268, 276, 532, 100, 548, 324, 580, 772, 152, 280, 168, 296, 200, 328, 784, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_157, vertices_269, vertices_565, vertices_357, vertices_681, vertices_297, vertices_838, vertices_218, vertices_346, vertices_786, vertices_738, vertices_284, vertices_788, vertices_612, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_261, vertices_41, vertices_137, vertices_265, vertices_145, vertices_529, vertices_289, vertices_545, vertices_641, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_268, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_157), (false, vertices_269), (false, vertices_565), (false, vertices_357), (false, vertices_681), (false, vertices_297), (true, vertices_90), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_276), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_784), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_157) then 20 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 269 1 297 274 194 322 578 770 276 580 772 280 200 328 784 224 608 659 90 157 565 357 681
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 168 488 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0463

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0464.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0464

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 299, 523, 451, 553, 369, 737, 158, 526, 410, 316, 620, 116, 596, 660, 976, 11, 131, 259, 515, 41, 521, 97, 289, 545, 193, 321, 641, 14, 134, 518, 154, 266, 522, 386, 28, 44, 524, 52, 84, 148, 532, 100, 580, 644, 280, 296, 552, 112, 304, 336, 592, 400, 656, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_299, vertices_523, vertices_451, vertices_553, vertices_369, vertices_737, vertices_158, vertices_526, vertices_410, vertices_316, vertices_620, vertices_116, vertices_596, vertices_660, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_41, vertices_521, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_14, vertices_134, vertices_518, vertices_154, vertices_266, vertices_522, vertices_386, vertices_28, vertices_44, vertices_524, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_580, vertices_644, vertices_280, vertices_296, vertices_552, vertices_112, vertices_304, vertices_336, vertices_592, vertices_400, vertices_656, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_299), (false, vertices_523), (false, vertices_451), (false, vertices_553), (false, vertices_369), (false, vertices_737), (true, vertices_14), (true, vertices_154), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_280), (true, vertices_592), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 16 22 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_299) then 19 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_154) then 21 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 3 5 6 7 8 976 336 2
cert_row_4 2 1 2 3 4 7 316 28 3
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 0 6 3 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 316
cert_cover_5 3 2 1 2 3 4 28 316 3
cert_coverFacet 4 620
cert_cover_5 4 3 1 2 4 5 44 620 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 976
cert_cover_5 8 1 3 5 6 7 336 976 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0464

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0465.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0465

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 233, 297, 369, 961, 158, 526, 310, 838, 186, 298, 340, 596, 660, 752, 41, 137, 265, 521, 97, 289, 193, 321, 641, 769, 14, 22, 262, 518, 154, 42, 266, 522, 50, 290, 770, 140, 524, 84, 148, 276, 532, 324, 580, 644, 168, 296, 112, 176, 304, 336, 592, 656, 224, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_233, vertices_297, vertices_369, vertices_961, vertices_158, vertices_526, vertices_310, vertices_838, vertices_186, vertices_298, vertices_340, vertices_596, vertices_660, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_154, vertices_42, vertices_266, vertices_522, vertices_50, vertices_290, vertices_770, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_168, vertices_296, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_656, vertices_224, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_233), (false, vertices_297), (false, vertices_369), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_154), (true, vertices_42), (true, vertices_50), (true, vertices_290), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_580), (true, vertices_176), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 27 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_961) then 28 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_154) then 19 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 3 4 5 6 8 752 112 3
cert_row_4 2 0 1 3 4 7 310 22 3
cert_row_4 3 0 1 5 7 8 838 262 2
cert_rows
cert_pivot_2 2 6 3 0
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 310
cert_cover_5 2 2 0 1 3 4 22 310 3
cert_coverFacet 3 838
cert_cover_5 3 3 0 1 5 7 262 838 2
cert_coverFacet 4 186
cert_cover_5 4 0 0 2 3 4 154 186 3
cert_coverFacet 5 298
cert_cover_2 5 2 0 4 7 42 298 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 752
cert_cover_5 9 1 3 4 5 6 112 752 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0465

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0466.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0466

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 307, 147, 185, 297, 841, 214, 278, 646, 716, 628, 820, 488, 240, 864, 19, 131, 259, 515, 41, 137, 265, 521, 49, 145, 289, 769, 22, 134, 262, 518, 146, 274, 642, 564, 84, 276, 196, 580, 644, 772, 168, 296, 200, 328, 584, 648, 112, 176, 304, 208, 224, 352, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_307, vertices_147, vertices_185, vertices_297, vertices_841, vertices_214, vertices_278, vertices_646, vertices_716, vertices_628, vertices_820, vertices_488, vertices_240, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_41, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_642, vertices_564, vertices_84, vertices_276, vertices_196, vertices_580, vertices_644, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_208, vertices_224, vertices_352, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_307), (false, vertices_147), (false, vertices_185), (false, vertices_297), (false, vertices_841), (true, vertices_22), (true, vertices_134), (true, vertices_564), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_200), (true, vertices_112), (true, vertices_208), (true, vertices_224), (true, vertices_352), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_307) then 19 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_564) then 21 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_564), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 1 3 4 8 564
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 716
cert_cover_5 3 2 1 2 5 6 196 716 1
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 564 628 3
cert_coverFacet 5 820
cert_cover_5 5 1 1 3 4 7 564 820 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0466

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4323 : Certifies 4323 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0436.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4324 : Certifies 4324 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0437.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4325 : Certifies 4325 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0438.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4326 : Certifies 4326 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0439.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4327 : Certifies 4327 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0440.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4328 : Certifies 4328 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0441.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4329 : Certifies 4329 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0442.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4330 : Certifies 4330 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0443.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4331 : Certifies 4331 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0444.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4332 : Certifies 4332 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0445.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4333 : Certifies 4333 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0446.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4334 : Certifies 4334 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0447.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4335 : Certifies 4335 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0448.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4336 : Certifies 4336 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0449.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4337 : Certifies 4337 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0450.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4338 : Certifies 4338 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0451.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4339 : Certifies 4339 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0453.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4340 : Certifies 4340 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0454.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4341 : Certifies 4341 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0455.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4342 : Certifies 4342 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0456.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4343 : Certifies 4343 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0457.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4344 : Certifies 4344 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0458.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4345 : Certifies 4345 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0459.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4346 : Certifies 4346 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0460.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4347 : Certifies 4347 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0461.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4348 : Certifies 4348 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0462.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4349 : Certifies 4349 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0463.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4350 : Certifies 4350 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0464.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4351 : Certifies 4351 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0465.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4352 : Certifies 4352 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0466.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B143 (j : Fin 30) :
    Certifies (4323 + j.val) := by
  fin_cases j
  · exact projection_4323
  · exact projection_4324
  · exact projection_4325
  · exact projection_4326
  · exact projection_4327
  · exact projection_4328
  · exact projection_4329
  · exact projection_4330
  · exact projection_4331
  · exact projection_4332
  · exact projection_4333
  · exact projection_4334
  · exact projection_4335
  · exact projection_4336
  · exact projection_4337
  · exact projection_4338
  · exact projection_4339
  · exact projection_4340
  · exact projection_4341
  · exact projection_4342
  · exact projection_4343
  · exact projection_4344
  · exact projection_4345
  · exact projection_4346
  · exact projection_4347
  · exact projection_4348
  · exact projection_4349
  · exact projection_4350
  · exact projection_4351
  · exact projection_4352

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
