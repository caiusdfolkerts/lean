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
/- Source: ProjectionCertificates/P0_030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 587, 339, 147, 557, 181, 121, 434, 962, 364, 908, 420, 840, 368, 19, 67, 131, 515, 37, 133, 517, 41, 73, 521, 49, 81, 145, 146, 274, 322, 578, 386, 642, 44, 268, 524, 164, 292, 388, 644, 104, 328, 584, 776, 112, 176, 304, 336, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_587, vertices_339, vertices_147, vertices_557, vertices_181, vertices_121, vertices_434, vertices_962, vertices_364, vertices_908, vertices_420, vertices_840, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_49, vertices_81, vertices_145, vertices_146, vertices_274, vertices_322, vertices_578, vertices_386, vertices_642, vertices_44, vertices_268, vertices_524, vertices_164, vertices_292, vertices_388, vertices_644, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_587), (false, vertices_339), (false, vertices_147), (false, vertices_557), (false, vertices_181), (false, vertices_121), (true, vertices_386), (true, vertices_268), (true, vertices_292), (true, vertices_388), (true, vertices_328), (true, vertices_776), (true, vertices_304), (true, vertices_352), (true, vertices_416), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_147) then 11 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 3 434 386 1
cert_row_4 1 5 6 7 8 0 962 832 1
cert_row_4 2 1 2 5 7 4 364 268 2
cert_row_4 3 2 6 7 8 1 908 776 1
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 434
cert_cover_5 0 0 0 3 4 6 146 434 2
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 322 962 2
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 44 364 3
cert_coverFacet 3 908
cert_cover_5 3 3 1 2 6 7 268 908 2
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_030

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_031.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_031

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 539, 339, 173, 213, 325, 553, 689, 810, 786, 364, 740, 976, 864, 11, 19, 259, 13, 69, 133, 261, 41, 521, 81, 145, 529, 161, 545, 321, 266, 522, 274, 530, 770, 44, 268, 100, 164, 196, 324, 296, 552, 208, 336, 656, 784, 352, 608, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_539, vertices_339, vertices_173, vertices_213, vertices_325, vertices_553, vertices_689, vertices_810, vertices_786, vertices_364, vertices_740, vertices_976, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_13, vertices_69, vertices_133, vertices_261, vertices_41, vertices_521, vertices_81, vertices_145, vertices_529, vertices_161, vertices_545, vertices_321, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_44, vertices_268, vertices_100, vertices_164, vertices_196, vertices_324, vertices_296, vertices_552, vertices_208, vertices_336, vertices_656, vertices_784, vertices_352, vertices_608, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_539), (false, vertices_339), (false, vertices_173), (false, vertices_213), (false, vertices_325), (false, vertices_553), (false, vertices_689), (true, vertices_770), (true, vertices_100), (true, vertices_296), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 12 else
  if p.val = (false, vertices_539) then 13 else
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_325) then 9 else
  if p.val = (false, vertices_553) then 10 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_784) then 3 else
  if p.val = (true, vertices_352) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 7 8 0 810 296 3
cert_row_4 1 1 4 5 7 2 364 100 3
cert_row_4 2 4 5 6 8 1 740 608 2
cert_row_4 3 5 6 7 8 3 976 704 2
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 0 0 2 4 7 266 810 2
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 5 44 364 3
cert_coverFacet 3 740
cert_cover_5 3 2 1 4 5 6 100 740 3
cert_coverFacet 4 976
cert_cover_5 4 3 3 5 6 7 208 976 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_031

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 173, 661, 613, 409, 809, 710, 346, 210, 658, 866, 228, 248, 360, 37, 133, 517, 41, 137, 265, 145, 273, 529, 545, 769, 82, 146, 274, 530, 194, 322, 578, 642, 770, 100, 164, 196, 580, 644, 88, 152, 280, 104, 168, 296, 328, 208, 656, 224, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_173, vertices_661, vertices_613, vertices_409, vertices_809, vertices_710, vertices_346, vertices_210, vertices_658, vertices_866, vertices_228, vertices_248, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_41, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_545, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_328, vertices_208, vertices_656, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_173), (false, vertices_661), (false, vertices_613), (false, vertices_409), (false, vertices_809), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_196), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_208), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 82 1 146 2 194 322 578 642 196 88 104 328 208 224 352 787 173 661 613 409 809
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 8 1 710 194 3
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_4 2 2 3 5 7 0 346 88 3
cert_row_4 3 3 4 5 6 2 248 208 1
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 82 346 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 322 866 1
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_032

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 587, 659, 355, 157, 109, 293, 649, 850, 684, 436, 872, 912, 928, 19, 67, 259, 515, 13, 21, 37, 261, 73, 137, 521, 145, 97, 289, 641, 274, 530, 322, 578, 44, 140, 148, 276, 164, 292, 104, 552, 584, 648, 400, 656, 784, 352, 416, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_587, vertices_659, vertices_355, vertices_157, vertices_109, vertices_293, vertices_649, vertices_850, vertices_684, vertices_436, vertices_872, vertices_912, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_13, vertices_21, vertices_37, vertices_261, vertices_73, vertices_137, vertices_521, vertices_145, vertices_97, vertices_289, vertices_641, vertices_274, vertices_530, vertices_322, vertices_578, vertices_44, vertices_140, vertices_148, vertices_276, vertices_164, vertices_292, vertices_104, vertices_552, vertices_584, vertices_648, vertices_400, vertices_656, vertices_784, vertices_352, vertices_416, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_587), (false, vertices_659), (false, vertices_355), (false, vertices_157), (false, vertices_109), (false, vertices_293), (false, vertices_649), (true, vertices_164), (true, vertices_552), (true, vertices_400), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 19 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 12 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_157) then 13 else
  if p.val = (false, vertices_109) then 14 else
  if p.val = (false, vertices_293) then 9 else
  if p.val = (false, vertices_649) then 10 else
  if p.val = (true, vertices_164) then 0 else
  if p.val = (true, vertices_552) then 1 else
  if p.val = (true, vertices_400) then 2 else
  if p.val = (true, vertices_784) then 3 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_832) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 5 7 8 0 850 784 1
cert_row_4 1 1 4 6 7 3 436 164 3
cert_row_4 2 2 4 6 8 1 684 552 2
cert_row_4 3 4 5 7 8 2 872 352 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 850
cert_cover_5 0 0 0 3 5 7 274 850 2
cert_coverFacet 1 684
cert_cover_5 1 2 1 2 4 6 44 684 3
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 148 436 2
cert_coverFacet 3 872
cert_cover_5 3 3 2 4 5 7 104 872 3
cert_coverFacet 4 912
cert_cover_2 4 6 3 7 8 400 912 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_033

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 563, 227, 285, 537, 457, 369, 614, 962, 572, 908, 308, 356, 836, 35, 131, 515, 25, 137, 265, 521, 49, 273, 529, 97, 193, 321, 98, 546, 194, 578, 642, 28, 268, 524, 52, 276, 100, 292, 548, 324, 580, 772, 536, 392, 648, 304, 560, 352, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_563, vertices_227, vertices_285, vertices_537, vertices_457, vertices_369, vertices_614, vertices_962, vertices_572, vertices_908, vertices_308, vertices_356, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_97, vertices_193, vertices_321, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_276, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_536, vertices_392, vertices_648, vertices_304, vertices_560, vertices_352, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_563), (false, vertices_227), (false, vertices_285), (false, vertices_537), (false, vertices_457), (false, vertices_369), (true, vertices_578), (true, vertices_524), (true, vertices_52), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_537) then 11 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 1 2 4 8 3 572 524 2
cert_row_4 1 0 1 5 8 4 614 578 1
cert_row_4 2 5 6 7 8 0 962 448 3
cert_row_4 3 2 6 7 8 1 908 392 3
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 194 962 3
cert_coverFacet 2 572
cert_cover_5 2 0 1 2 3 4 28 572 3
cert_coverFacet 3 908
cert_cover_5 3 3 1 2 6 7 268 908 2
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_034

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 651, 595, 709, 233, 297, 369, 790, 810, 684, 340, 596, 484, 804, 11, 19, 515, 41, 137, 265, 81, 273, 97, 289, 193, 577, 641, 266, 522, 274, 530, 770, 84, 276, 532, 164, 292, 548, 196, 324, 580, 644, 772, 168, 296, 552, 648, 336, 592, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_651, vertices_595, vertices_709, vertices_233, vertices_297, vertices_369, vertices_790, vertices_810, vertices_684, vertices_340, vertices_596, vertices_484, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_41, vertices_137, vertices_265, vertices_81, vertices_273, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_84, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_168, vertices_296, vertices_552, vertices_648, vertices_336, vertices_592, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_651), (false, vertices_595), (false, vertices_709), (false, vertices_233), (false, vertices_297), (false, vertices_369), (true, vertices_770), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_772), (true, vertices_552), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_297) then 11 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 7 8 3 790 770 1
cert_row_4 1 2 4 7 8 0 810 296 3
cert_row_4 2 1 4 6 8 2 684 164 3
cert_row_4 3 4 5 6 7 1 484 224 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 266 810 2
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 164 684 1
cert_coverFacet 3 340
cert_cover_2 3 3 1 5 7 84 340 3
cert_coverFacet 4 596
cert_cover_2 4 3 1 5 8 84 596 3
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 164 484 2
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_036

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 59, 395, 99, 157, 117, 901, 298, 866, 724, 836, 248, 936, 736, 11, 35, 67, 259, 21, 69, 133, 261, 25, 137, 49, 97, 385, 42, 266, 98, 290, 322, 84, 148, 324, 580, 644, 772, 56, 152, 168, 296, 392, 112, 208, 224, 608, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_59, vertices_395, vertices_99, vertices_157, vertices_117, vertices_901, vertices_298, vertices_866, vertices_724, vertices_836, vertices_248, vertices_936, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_67, vertices_259, vertices_21, vertices_69, vertices_133, vertices_261, vertices_25, vertices_137, vertices_49, vertices_97, vertices_385, vertices_42, vertices_266, vertices_98, vertices_290, vertices_322, vertices_84, vertices_148, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_152, vertices_168, vertices_296, vertices_392, vertices_112, vertices_208, vertices_224, vertices_608, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_59), (false, vertices_395), (false, vertices_99), (false, vertices_157), (false, vertices_117), (false, vertices_901), (true, vertices_290), (true, vertices_580), (true, vertices_168), (true, vertices_296), (true, vertices_208), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_59) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_99) then 11 else
  if p.val = (false, vertices_157) then 17 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (true, vertices_290) then 0 else
  if p.val = (true, vertices_580) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_208) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
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
cert_row_4 0 4 5 7 8 0 866 608 2
cert_row_4 1 3 5 6 8 1 724 208 3
cert_row_4 2 2 4 5 6 3 248 168 2
cert_row_4 3 4 6 7 8 2 936 672 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 298
cert_cover_2 0 2 0 4 7 42 298 3
cert_coverFacet 1 866
cert_cover_5 1 0 0 4 5 7 98 866 3
cert_coverFacet 2 724
cert_cover_5 2 1 1 3 5 6 84 724 3
cert_coverFacet 3 836
cert_cover_2 3 5 1 7 8 324 836 3
cert_coverFacet 4 248
cert_cover_5 4 2 2 3 4 5 56 248 3
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 168 936 3
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_038

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 331, 651, 291, 205, 661, 357, 810, 628, 212, 920, 456, 496, 816, 11, 35, 259, 515, 37, 69, 133, 517, 73, 137, 289, 321, 641, 266, 522, 290, 546, 84, 148, 532, 100, 548, 196, 200, 328, 392, 648, 776, 112, 304, 560, 208, 400, 656, 784, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_331, vertices_651, vertices_291, vertices_205, vertices_661, vertices_357, vertices_810, vertices_628, vertices_212, vertices_920, vertices_456, vertices_496, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_37, vertices_69, vertices_133, vertices_517, vertices_73, vertices_137, vertices_289, vertices_321, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_656, vertices_784, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_331), (false, vertices_651), (false, vertices_291), (false, vertices_205), (false, vertices_661), (false, vertices_357), (true, vertices_84), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_784), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_291) then 11 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (true, vertices_84) then 0 else
  if p.val = (true, vertices_392) then 1 else
  if p.val = (true, vertices_776) then 2 else
  if p.val = (true, vertices_112) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
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
cert_row_4 0 2 4 7 8 0 810 776 1
cert_row_4 1 3 4 5 8 1 628 112 3
cert_row_4 2 3 6 7 8 2 920 400 3
cert_row_4 3 4 5 6 7 3 496 352 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 0 0 2 4 7 266 810 2
cert_coverFacet 1 628
cert_cover_5 1 1 1 3 4 5 84 628 2
cert_coverFacet 2 212
cert_cover_2 2 3 1 5 6 84 212 3
cert_coverFacet 3 920
cert_cover_5 3 2 2 3 6 7 392 920 1
cert_coverFacet 4 456
cert_cover_2 4 5 2 6 7 200 456 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_039

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 595, 675, 341, 229, 293, 713, 806, 794, 908, 676, 452, 472, 600, 19, 35, 515, 37, 69, 261, 81, 273, 161, 289, 193, 577, 641, 274, 530, 290, 546, 770, 164, 292, 548, 196, 324, 388, 644, 772, 88, 280, 536, 200, 584, 392, 648, 776, 336, 592, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_595, vertices_675, vertices_341, vertices_229, vertices_293, vertices_713, vertices_806, vertices_794, vertices_908, vertices_676, vertices_452, vertices_472, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_37, vertices_69, vertices_261, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_577, vertices_641, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_336, vertices_592, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_595), (false, vertices_675), (false, vertices_341), (false, vertices_229), (false, vertices_293), (false, vertices_713), (true, vertices_770), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_776), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 13 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_293) then 11 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_388) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 4 806 770 1
cert_row_4 1 2 3 7 8 0 794 280 3
cert_row_4 2 2 6 7 8 1 908 392 3
cert_row_4 3 3 5 6 7 2 472 336 2
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 908
cert_cover_5 2 2 1 2 6 7 388 908 1
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 88 472 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_041

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 283, 563, 109, 549, 457, 241, 401, 842, 914, 588, 692, 228, 964, 11, 19, 515, 13, 37, 517, 73, 265, 49, 145, 273, 97, 545, 193, 385, 266, 522, 274, 530, 770, 76, 524, 100, 164, 548, 196, 580, 644, 328, 584, 176, 560, 400, 656, 224, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_283, vertices_563, vertices_109, vertices_549, vertices_457, vertices_241, vertices_401, vertices_842, vertices_914, vertices_588, vertices_692, vertices_228, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_13, vertices_37, vertices_517, vertices_73, vertices_265, vertices_49, vertices_145, vertices_273, vertices_97, vertices_545, vertices_193, vertices_385, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_76, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_328, vertices_584, vertices_176, vertices_560, vertices_400, vertices_656, vertices_224, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_283), (false, vertices_563), (false, vertices_109), (false, vertices_549), (false, vertices_457), (false, vertices_241), (false, vertices_401), (true, vertices_770), (true, vertices_164), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_584), (true, vertices_656), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 12 else
  if p.val = (false, vertices_283) then 13 else
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_109) then 16 else
  if p.val = (false, vertices_549) then 9 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (false, vertices_401) then 10 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_832) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 7 8 2 842 770 1
cert_row_4 1 3 6 7 8 0 914 400 3
cert_row_4 2 1 4 6 8 3 692 164 3
cert_row_4 3 5 6 7 8 1 964 448 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 0 0 2 5 7 266 842 2
cert_coverFacet 1 914
cert_cover_5 1 1 0 3 6 7 274 914 2
cert_coverFacet 2 588
cert_cover_2 2 2 1 5 8 76 588 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 164 692 1
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 964
cert_cover_5 5 3 1 5 6 7 196 964 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_042

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 227, 803, 357, 793, 465, 614, 714, 412, 812, 204, 588, 452, 664, 35, 131, 515, 145, 273, 529, 97, 289, 193, 321, 769, 98, 546, 194, 578, 642, 76, 140, 268, 524, 100, 292, 548, 196, 324, 580, 388, 152, 280, 536, 200, 584, 648, 776, 400, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_227, vertices_803, vertices_357, vertices_793, vertices_465, vertices_614, vertices_714, vertices_412, vertices_812, vertices_204, vertices_588, vertices_452, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_193, vertices_321, vertices_769, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_648, vertices_776, vertices_400, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_227), (false, vertices_803), (false, vertices_357), (false, vertices_793), (false, vertices_465), (true, vertices_578), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 6 7 3 412 140 3
cert_row_4 1 0 2 5 8 6 714 578 1
cert_row_4 2 1 4 5 8 0 614 100 3
cert_row_4 3 2 4 7 8 1 812 776 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 194 714 1
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 140 412 2
cert_coverFacet 3 812
cert_cover_5 3 3 1 2 4 7 268 812 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_043

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_047.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_047

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 403, 613, 293, 453, 713, 689, 806, 666, 458, 778, 562, 844, 275, 37, 69, 261, 49, 145, 289, 545, 193, 577, 385, 641, 138, 266, 522, 50, 146, 530, 290, 546, 386, 770, 292, 548, 324, 580, 772, 200, 328, 584, 648, 776, 560, 656, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_403, vertices_613, vertices_293, vertices_453, vertices_713, vertices_689, vertices_806, vertices_666, vertices_458, vertices_778, vertices_562, vertices_844] (by decide +kernel)
  polygons := literalFinset [vertices_275, vertices_37, vertices_69, vertices_261, vertices_49, vertices_145, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_290, vertices_546, vertices_386, vertices_770, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_560, vertices_656, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_403), (false, vertices_613), (false, vertices_293), (false, vertices_453), (false, vertices_713), (false, vertices_689), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_772), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 11 else
  if p.val = (false, vertices_403) then 12 else
  if p.val = (false, vertices_613) then 14 else
  if p.val = (false, vertices_293) then 9 else
  if p.val = (false, vertices_453) then 15 else
  if p.val = (false, vertices_713) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_776) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 4 806 770 1
cert_row_4 1 0 2 6 8 3 666 138 3
cert_row_4 2 2 5 6 7 0 458 200 3
cert_row_4 3 2 5 7 8 1 844 328 3
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 138 666 2
cert_coverFacet 2 458
cert_cover_5 2 2 0 2 5 6 138 458 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 844
cert_cover_5 5 3 1 2 5 7 324 844 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_047

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 793, 713, 465, 678, 370, 818, 226, 706, 812, 652, 484, 137, 265, 521, 81, 273, 529, 193, 577, 385, 306, 82, 530, 98, 162, 546, 194, 578, 642, 140, 268, 524, 164, 292, 548, 388, 644, 648, 776, 336, 784, 224, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_793, vertices_713, vertices_465, vertices_678, vertices_370, vertices_818, vertices_226, vertices_706, vertices_812, vertices_652, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_306, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_648, vertices_776, vertices_336, vertices_784, vertices_224, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_793), (false, vertices_713), (false, vertices_465), (true, vertices_306), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_224), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_306) then 15 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_306), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 7 8 2 812 292 3
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 4 5 6 7 1 484 224 3
cert_row_2 3 3 4 7 0 306
cert_rows
cert_pivot_2 2 8 1 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 370
cert_cover_5 1 3 0 3 4 5 306 370 3
cert_coverFacet 2 818
cert_cover_5 2 3 0 3 4 8 306 818 3
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 812
cert_cover_5 5 0 1 2 4 7 268 812 2
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 484
cert_cover_5 7 2 1 4 5 6 164 484 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_048

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_049.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_049

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 837, 601, 153, 809, 465, 174, 806, 454, 298, 684, 724, 664, 25, 137, 265, 521, 81, 145, 321, 577, 385, 769, 38, 134, 262, 42, 138, 266, 290, 386, 172, 548, 196, 324, 580, 644, 772, 152, 536, 296, 552, 648, 208, 592, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_837, vertices_601, vertices_153, vertices_809, vertices_465, vertices_174, vertices_806, vertices_454, vertices_298, vertices_684, vertices_724, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_321, vertices_577, vertices_385, vertices_769, vertices_38, vertices_134, vertices_262, vertices_42, vertices_138, vertices_266, vertices_290, vertices_386, vertices_172, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_536, vertices_296, vertices_552, vertices_648, vertices_208, vertices_592, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_837), (false, vertices_601), (false, vertices_153), (false, vertices_809), (false, vertices_465), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_42), (true, vertices_290), (true, vertices_172), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_648), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_837) then 14 else
  if p.val = (false, vertices_601) then 17 else
  if p.val = (false, vertices_153) then 10 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_172) then 15 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_656) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 5 6 8 3 724 196 3
cert_row_4 1 0 1 4 7 8 806 38 3
cert_row_4 2 1 5 6 7 0 454 196 3
cert_row_2 3 2 4 6 1 172
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 3 0 1 2 4 38 174 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 38 806 3
cert_coverFacet 2 454
cert_cover_5 2 2 0 1 5 6 134 454 2
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 684
cert_cover_5 4 3 1 2 4 8 172 684 3
cert_coverFacet 5 724
cert_cover_5 5 0 1 3 5 6 196 724 1
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_049

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_050.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_050

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 93, 789, 709, 345, 481, 794, 426, 554, 738, 540, 620, 360, 21, 69, 517, 89, 273, 193, 321, 385, 641, 769, 42, 266, 522, 162, 546, 386, 642, 770, 28, 76, 524, 532, 580, 280, 536, 104, 296, 552, 328, 784, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_93, vertices_789, vertices_709, vertices_345, vertices_481, vertices_794, vertices_426, vertices_554, vertices_738, vertices_540, vertices_620, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_89, vertices_273, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_532, vertices_580, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_93), (false, vertices_789), (false, vertices_709), (false, vertices_345), (false, vertices_481), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_524), (true, vertices_536), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_709) then 15 else
  if p.val = (false, vertices_345) then 18 else
  if p.val = (false, vertices_481) then 21 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_608) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 3 794 266 3
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_4 2 4 5 6 8 0 738 224 3
cert_row_4 3 2 4 5 8 1 620 104 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 266 794 2
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 162 738 2
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 76 620 2
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_050

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_051.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_051

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 837, 361, 169, 713, 817, 566, 406, 710, 434, 460, 788, 424, 41, 73, 137, 161, 289, 545, 321, 577, 641, 769, 22, 134, 518, 50, 402, 162, 546, 642, 276, 532, 196, 324, 580, 388, 772, 168, 296, 200, 328, 392, 304, 560, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_837, vertices_361, vertices_169, vertices_713, vertices_817, vertices_566, vertices_406, vertices_710, vertices_434, vertices_460, vertices_788, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_134, vertices_518, vertices_50, vertices_402, vertices_162, vertices_546, vertices_642, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_304, vertices_560, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_837), (false, vertices_361), (false, vertices_169), (false, vertices_713), (false, vertices_817), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_402), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_388), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 12 else
  if p.val = (false, vertices_837) then 15 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_169) then 10 else
  if p.val = (false, vertices_713) then 18 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_402) then 13 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_402), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 8 4 566 22 3
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_4 2 2 5 6 7 1 460 200 3
cert_row_2 3 3 6 7 0 402
cert_rows
cert_pivot_2 4 8 1 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 406
cert_cover_5 1 3 0 1 3 6 22 406 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 134 710 2
cert_coverFacet 3 434
cert_cover_5 3 3 0 3 4 6 50 434 3
cert_coverFacet 4 460
cert_cover_5 4 2 1 2 5 6 196 460 1
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_051

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 355, 547, 333, 397, 677, 433, 842, 690, 306, 786, 716, 920, 35, 67, 515, 269, 69, 133, 517, 161, 289, 545, 321, 385, 50, 274, 530, 290, 546, 322, 578, 770, 76, 140, 580, 644, 328, 584, 392, 648, 776, 176, 304, 400, 656, 784, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_355, vertices_547, vertices_333, vertices_397, vertices_677, vertices_433, vertices_842, vertices_690, vertices_306, vertices_786, vertices_716, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_269, vertices_69, vertices_133, vertices_517, vertices_161, vertices_289, vertices_545, vertices_321, vertices_385, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_580, vertices_644, vertices_328, vertices_584, vertices_392, vertices_648, vertices_776, vertices_176, vertices_304, vertices_400, vertices_656, vertices_784, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_355), (false, vertices_547), (false, vertices_333), (false, vertices_397), (false, vertices_677), (false, vertices_433), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 11 else
  if p.val = (false, vertices_355) then 12 else
  if p.val = (false, vertices_547) then 9 else
  if p.val = (false, vertices_333) then 15 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_677) then 14 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_784) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 8 4 690 530 2
cert_row_4 1 2 5 7 8 0 842 328 3
cert_row_4 2 2 5 6 8 1 716 584 2
cert_row_4 3 3 6 7 8 2 920 400 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 1 0 2 5 7 322 842 1
cert_coverFacet 1 690
cert_cover_5 1 0 0 3 4 6 50 690 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 76 716 3
cert_coverFacet 5 920
cert_cover_5 5 3 2 3 6 7 392 920 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_052

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_053.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_053

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 205, 781, 597, 457, 369, 906, 690, 306, 482, 652, 740, 624, 13, 69, 517, 201, 265, 81, 273, 529, 321, 769, 50, 274, 530, 162, 290, 386, 642, 770, 140, 524, 196, 580, 644, 392, 648, 776, 112, 304, 560, 592, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_205, vertices_781, vertices_597, vertices_457, vertices_369, vertices_906, vertices_690, vertices_306, vertices_482, vertices_652, vertices_740, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_201, vertices_265, vertices_81, vertices_273, vertices_529, vertices_321, vertices_769, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_140, vertices_524, vertices_196, vertices_580, vertices_644, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_592, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_205), (false, vertices_781), (false, vertices_597), (false, vertices_457), (false, vertices_369), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_644), (true, vertices_648), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 12 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
cert_nodeAtPriority_59 0 50 1 162 2 290 386 642 644 648 560 224 608 672 787 781 597 205 457 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 6 7 8 2 906 386 3
cert_row_4 1 0 4 6 8 3 690 162 3
cert_row_4 2 4 5 6 7 0 482 224 3
cert_row_4 3 4 5 6 8 1 740 224 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 906
cert_cover_5 0 0 0 2 6 7 386 906 1
cert_coverFacet 1 690
cert_cover_5 1 1 0 3 4 6 50 690 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 162 482 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 196 740 1
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_053

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 395, 99, 163, 653, 269, 613, 689, 626, 434, 850, 844, 920, 35, 67, 131, 259, 13, 69, 261, 517, 137, 265, 97, 161, 545, 641, 50, 594, 274, 98, 162, 322, 386, 268, 524, 324, 580, 392, 648, 776, 176, 560, 400, 656, 784, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_395, vertices_99, vertices_163, vertices_653, vertices_269, vertices_613, vertices_689, vertices_626, vertices_434, vertices_850, vertices_844, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_259, vertices_13, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_641, vertices_50, vertices_594, vertices_274, vertices_98, vertices_162, vertices_322, vertices_386, vertices_268, vertices_524, vertices_324, vertices_580, vertices_392, vertices_648, vertices_776, vertices_176, vertices_560, vertices_400, vertices_656, vertices_784, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_395), (false, vertices_99), (false, vertices_163), (false, vertices_653), (false, vertices_269), (false, vertices_613), (false, vertices_689), (true, vertices_50), (true, vertices_594), (true, vertices_274), (true, vertices_776), (true, vertices_400), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 9 16 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_99) then 6 else
  if p.val = (false, vertices_163) then 7 else
  if p.val = (false, vertices_653) then 11 else
  if p.val = (false, vertices_269) then 8 else
  if p.val = (false, vertices_613) then 12 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_594) then 15 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_776) then 2 else
  if p.val = (true, vertices_400) then 3 else
  if p.val = (true, vertices_784) then 4 else
  if p.val = (true, vertices_832) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 6 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_594), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 4 434 274 2
cert_row_4 1 2 5 7 8 1 844 776 1
cert_row_4 2 3 6 7 8 2 920 400 3
cert_row_2 3 3 5 8 0 594
cert_rows
cert_pivot_2 4 1 2 0
cert_heightProof 4
cert_coverFacet 0 626
cert_cover_5 0 3 0 3 4 5 50 626 3
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 50 434 3
cert_coverFacet 2 850
cert_cover_5 2 3 0 3 5 7 594 850 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 268 844 2
cert_coverFacet 4 920
cert_cover_5 4 2 2 3 6 7 392 920 1
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_054

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_055.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_055

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 709, 361, 681, 585, 433, 406, 790, 198, 582, 842, 692, 824, 41, 73, 521, 161, 289, 193, 321, 577, 385, 641, 278, 70, 134, 518, 194, 322, 578, 386, 770, 148, 532, 196, 580, 644, 296, 552, 328, 584, 776, 176, 304, 560, 400, 784, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_709, vertices_361, vertices_681, vertices_585, vertices_433, vertices_406, vertices_790, vertices_198, vertices_582, vertices_842, vertices_692, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_278, vertices_70, vertices_134, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_560, vertices_400, vertices_784, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_709), (false, vertices_361), (false, vertices_681), (false, vertices_585), (false, vertices_433), (true, vertices_278), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_578), (true, vertices_770), (true, vertices_148), (true, vertices_532), (true, vertices_776), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 12 else
  if p.val = (false, vertices_709) then 15 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_585) then 10 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (true, vertices_278) then 13 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_278), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 5 842 770 1
cert_row_4 1 1 3 4 8 6 692 532 2
cert_row_4 2 3 4 7 8 2 824 304 3
cert_row_2 3 1 3 7 0 278
cert_rows
cert_pivot_2 5 6 2 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 3 0 1 3 6 278 406 3
cert_coverFacet 1 790
cert_cover_5 1 3 0 1 3 8 278 790 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 842
cert_cover_5 4 0 0 2 5 7 322 842 1
cert_coverFacet 5 692
cert_cover_5 5 1 1 3 4 6 148 692 2
cert_coverFacet 6 824
cert_cover_5 6 2 2 3 4 7 296 824 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_055

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 781, 661, 185, 601, 425, 710, 774, 842, 482, 376, 240, 720, 133, 261, 517, 25, 169, 265, 521, 145, 529, 385, 134, 262, 518, 194, 322, 578, 386, 770, 644, 772, 56, 88, 296, 328, 584, 776, 112, 176, 208, 592, 656, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_781, vertices_661, vertices_185, vertices_601, vertices_425, vertices_710, vertices_774, vertices_842, vertices_482, vertices_376, vertices_240, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_169, vertices_265, vertices_521, vertices_145, vertices_529, vertices_385, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_781), (false, vertices_661), (false, vertices_185), (false, vertices_601), (false, vertices_425), (true, vertices_518), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_224), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_185) then 18 else
  if p.val = (false, vertices_601) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 8 1 710 194 3
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 4 5 6 7 0 482 224 3
cert_row_4 3 3 4 5 7 2 376 112 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 134 710 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 322 842 1
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 194 482 1
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 240
cert_cover_2 5 4 3 5 6 112 240 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_057

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 789, 57, 409, 681, 625, 598, 454, 774, 738, 340, 376, 488, 25, 41, 137, 49, 273, 529, 545, 385, 641, 769, 70, 262, 518, 194, 578, 386, 642, 770, 84, 276, 532, 324, 772, 56, 280, 360, 168, 392, 112, 336, 592, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_789, vertices_57, vertices_409, vertices_681, vertices_625, vertices_598, vertices_454, vertices_774, vertices_738, vertices_340, vertices_376, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_49, vertices_273, vertices_529, vertices_545, vertices_385, vertices_641, vertices_769, vertices_70, vertices_262, vertices_518, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_56, vertices_280, vertices_360, vertices_168, vertices_392, vertices_112, vertices_336, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_789), (false, vertices_57), (false, vertices_409), (false, vertices_681), (false, vertices_625), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_194), (true, vertices_578), (true, vertices_84), (true, vertices_324), (true, vertices_360), (true, vertices_336), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 18 15 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_57) then 10 else
  if p.val = (false, vertices_409) then 16 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_625) then 17 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_360) then 20 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 8 3 598 70 3
cert_row_4 1 0 5 6 7 1 454 194 3
cert_row_4 2 4 5 6 8 0 738 224 3
cert_row_2 3 4 5 7 2 360
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 70 598 2
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 194 738 1
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 360 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_058

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_060.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_060

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 651, 803, 181, 357, 689, 842, 394, 460, 116, 724, 712, 880, 131, 259, 515, 37, 133, 261, 177, 289, 545, 641, 138, 266, 522, 386, 770, 52, 84, 148, 100, 196, 324, 388, 200, 328, 584, 392, 648, 112, 560, 592, 656, 352, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_651, vertices_803, vertices_181, vertices_357, vertices_689, vertices_842, vertices_394, vertices_460, vertices_116, vertices_724, vertices_712, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_133, vertices_261, vertices_177, vertices_289, vertices_545, vertices_641, vertices_138, vertices_266, vertices_522, vertices_386, vertices_770, vertices_52, vertices_84, vertices_148, vertices_100, vertices_196, vertices_324, vertices_388, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_560, vertices_592, vertices_656, vertices_352, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_651), (false, vertices_803), (false, vertices_181), (false, vertices_357), (false, vertices_689), (true, vertices_266), (true, vertices_84), (true, vertices_196), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_112), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 5 7 8 0 842 328 3
cert_row_4 1 1 5 6 7 2 460 196 3
cert_row_4 2 3 5 6 8 1 724 592 2
cert_row_4 3 4 5 7 8 3 880 352 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 0 0 2 5 7 266 842 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 460
cert_cover_5 2 1 1 2 5 6 196 460 1
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_060

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_061.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_061

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 301, 789, 677, 241, 369, 842, 466, 786, 738, 620, 780, 360, 37, 261, 517, 113, 145, 273, 529, 161, 289, 641, 146, 274, 530, 194, 322, 578, 642, 770, 44, 268, 524, 548, 772, 104, 296, 328, 584, 776, 208, 336, 784, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_301, vertices_789, vertices_677, vertices_241, vertices_369, vertices_842, vertices_466, vertices_786, vertices_738, vertices_620, vertices_780, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_113, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_548, vertices_772, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_301), (false, vertices_789), (false, vertices_677), (false, vertices_241), (false, vertices_369), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_524), (true, vertices_104), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 12 else
  if p.val = (false, vertices_301) then 14 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_608) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 3 466 194 3
cert_row_4 1 0 2 5 8 7 842 578 1
cert_row_4 2 4 5 6 8 0 738 224 3
cert_row_4 3 2 4 5 8 1 620 104 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 1 0 2 5 7 322 842 1
cert_coverFacet 1 466
cert_cover_5 1 0 0 3 5 6 146 466 2
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 194 738 1
cert_coverFacet 4 620
cert_cover_5 4 3 1 2 4 5 44 620 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_061

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 115, 403, 547, 333, 397, 613, 337, 906, 818, 716, 872, 368, 19, 35, 131, 515, 269, 69, 133, 517, 81, 273, 97, 545, 321, 385, 50, 274, 546, 386, 642, 770, 76, 140, 580, 644, 328, 584, 392, 648, 776, 112, 304, 336, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_115, vertices_403, vertices_547, vertices_333, vertices_397, vertices_613, vertices_337, vertices_906, vertices_818, vertices_716, vertices_872, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_269, vertices_69, vertices_133, vertices_517, vertices_81, vertices_273, vertices_97, vertices_545, vertices_321, vertices_385, vertices_50, vertices_274, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_580, vertices_644, vertices_328, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_336, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_115), (false, vertices_403), (false, vertices_547), (false, vertices_333), (false, vertices_397), (false, vertices_613), (false, vertices_337), (true, vertices_770), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 17 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 10 else
  if p.val = (false, vertices_115) then 11 else
  if p.val = (false, vertices_403) then 12 else
  if p.val = (false, vertices_547) then 7 else
  if p.val = (false, vertices_333) then 15 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_613) then 14 else
  if p.val = (false, vertices_337) then 8 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_584) then 1 else
  if p.val = (true, vertices_648) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_800) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 7 8 3 818 546 2
cert_row_4 1 2 6 7 8 0 906 392 3
cert_row_4 2 2 5 6 8 1 716 584 2
cert_row_4 3 4 5 7 8 2 872 352 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 906
cert_cover_5 0 1 0 2 6 7 386 906 1
cert_coverFacet 1 818
cert_cover_5 1 0 0 3 4 7 50 818 3
cert_coverFacet 2 716
cert_cover_5 2 2 1 2 5 6 76 716 3
cert_coverFacet 3 872
cert_cover_5 3 3 2 4 5 7 328 872 1
cert_coverFacet 4 368
cert_cover_2 4 4 3 5 7 112 368 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_063

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 179, 803, 781, 405, 369, 242, 610, 706, 716, 396, 472, 872, 35, 131, 515, 133, 261, 517, 49, 145, 273, 289, 769, 178, 98, 546, 194, 578, 642, 140, 268, 524, 388, 644, 200, 328, 584, 392, 776, 112, 208, 336, 400, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_179, vertices_803, vertices_781, vertices_405, vertices_369, vertices_242, vertices_610, vertices_706, vertices_716, vertices_396, vertices_472, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_289, vertices_769, vertices_178, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_388, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_179), (false, vertices_803), (false, vertices_781), (false, vertices_405), (false, vertices_369), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_140), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_208), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_179) then 14 else
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 5 6 8 1 716 200 3
cert_row_4 1 2 4 5 7 8 872 328 1
cert_row_4 2 3 5 6 7 2 472 208 3
cert_row_2 3 3 4 6 0 178
cert_rows
cert_pivot_2 1 8 2 0
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 3 0 3 4 5 178 242 3
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 716
cert_cover_5 3 0 1 2 5 6 140 716 2
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 200 472 1
cert_coverFacet 6 872
cert_cover_5 6 1 2 4 5 7 328 872 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_064

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_066.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_066

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 115, 211, 803, 781, 405, 305, 714, 610, 460, 652, 872, 496, 83, 35, 131, 515, 133, 261, 517, 49, 145, 273, 289, 769, 98, 546, 194, 578, 642, 140, 268, 524, 388, 644, 200, 328, 584, 648, 776, 112, 304, 208, 400, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_115, vertices_211, vertices_803, vertices_781, vertices_405, vertices_305, vertices_714, vertices_610, vertices_460, vertices_652, vertices_872, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_35, vertices_131, vertices_515, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_289, vertices_769, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_388, vertices_644, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_115), (false, vertices_211), (false, vertices_803), (false, vertices_781), (false, vertices_405), (false, vertices_305), (true, vertices_578), (true, vertices_140), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_352), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 10 18 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_211) then 17 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_781) then 12 else
  if p.val = (false, vertices_405) then 13 else
  if p.val = (false, vertices_305) then 9 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_200) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 5 6 8 0 714 200 3
cert_row_4 1 2 5 6 7 1 460 200 3
cert_row_4 2 4 5 7 8 2 872 352 3
cert_row_4 3 4 5 6 7 3 496 352 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 0 0 2 5 6 194 714 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 460
cert_cover_5 2 1 1 2 5 6 140 460 2
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 328 872 1
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_066

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 115, 339, 163, 653, 789, 689, 458, 226, 844, 396, 744, 880, 83, 35, 131, 259, 133, 261, 517, 49, 273, 529, 161, 641, 98, 162, 194, 322, 386, 140, 268, 524, 388, 772, 200, 328, 584, 392, 648, 112, 560, 336, 784, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_115, vertices_339, vertices_163, vertices_653, vertices_789, vertices_689, vertices_458, vertices_226, vertices_844, vertices_396, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_35, vertices_131, vertices_259, vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_641, vertices_98, vertices_162, vertices_194, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_388, vertices_772, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_115), (false, vertices_339), (false, vertices_163), (false, vertices_653), (false, vertices_789), (false, vertices_689), (true, vertices_194), (true, vertices_268), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_224), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_115) then 12 else
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_163) then 9 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (true, vertices_194) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_200) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 5 6 7 0 458 200 3
cert_row_4 1 2 5 7 8 1 844 328 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_4 3 4 5 7 8 3 880 608 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 458
cert_cover_5 0 0 0 2 5 6 194 458 1
cert_coverFacet 1 226
cert_cover_2 1 4 0 5 6 98 226 3
cert_coverFacet 2 844
cert_cover_5 2 1 1 2 5 7 268 844 2
cert_coverFacet 3 396
cert_cover_2 3 2 1 6 7 140 396 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 200 744 1
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_068

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_070.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_070

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 539, 589, 213, 533, 457, 433, 842, 306, 562, 930, 692, 964, 27, 21, 69, 517, 73, 265, 521, 145, 273, 529, 193, 385, 266, 522, 50, 274, 530, 290, 546, 770, 148, 532, 196, 580, 644, 328, 584, 176, 304, 560, 416, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_539, vertices_589, vertices_213, vertices_533, vertices_457, vertices_433, vertices_842, vertices_306, vertices_562, vertices_930, vertices_692, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_21, vertices_69, vertices_517, vertices_73, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_385, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_416, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_539), (false, vertices_589), (false, vertices_213), (false, vertices_533), (false, vertices_457), (false, vertices_433), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_644), (true, vertices_560), (true, vertices_672), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 11 else
  if p.val = (false, vertices_539) then 12 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_533) then 9 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_832) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 7 8 2 842 770 1
cert_row_4 1 4 6 7 8 0 930 416 3
cert_row_4 2 1 4 6 8 3 692 644 1
cert_row_4 3 5 6 7 8 1 964 448 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 0 0 2 5 7 266 842 2
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 930
cert_cover_5 3 1 0 4 6 7 290 930 2
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 148 692 2
cert_coverFacet 5 964
cert_cover_5 5 3 1 5 6 7 196 964 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_070

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 563, 227, 397, 793, 241, 401, 710, 610, 844, 652, 468, 880, 35, 131, 515, 137, 265, 521, 49, 145, 273, 529, 225, 385, 98, 546, 194, 578, 642, 140, 268, 524, 196, 324, 580, 388, 644, 648, 776, 112, 560, 208, 336, 400, 784, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_563, vertices_227, vertices_397, vertices_793, vertices_241, vertices_401, vertices_710, vertices_610, vertices_844, vertices_652, vertices_468, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_529, vertices_225, vertices_385, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_563), (false, vertices_227), (false, vertices_397), (false, vertices_793), (false, vertices_241), (false, vertices_401), (true, vertices_578), (true, vertices_524), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_336), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 17 18 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 11 else
  if p.val = (false, vertices_563) then 12 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_793) then 16 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (false, vertices_401) then 9 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 5 6 8 0 710 196 3
cert_row_4 1 1 5 7 8 2 844 324 3
cert_row_4 2 3 5 6 7 1 468 208 3
cert_row_4 3 4 5 7 8 3 880 608 2
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 844
cert_cover_5 2 1 1 2 5 7 268 844 2
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 196 468 1
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_071

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0030 : Certifies 30 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0031 : Certifies 31 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_031.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0032 : Certifies 32 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0033 : Certifies 33 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0034 : Certifies 34 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0035 : Certifies 35 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0036 : Certifies 36 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0037 : Certifies 37 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0038 : Certifies 38 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0039 : Certifies 39 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0040 : Certifies 40 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0041 : Certifies 41 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_047.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0042 : Certifies 42 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0043 : Certifies 43 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_049.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0044 : Certifies 44 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_050.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0045 : Certifies 45 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_051.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0046 : Certifies 46 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0047 : Certifies 47 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_053.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0048 : Certifies 48 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0049 : Certifies 49 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_055.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0050 : Certifies 50 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0051 : Certifies 51 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0052 : Certifies 52 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_060.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0053 : Certifies 53 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_061.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0054 : Certifies 54 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0055 : Certifies 55 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0056 : Certifies 56 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_066.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0057 : Certifies 57 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0058 : Certifies 58 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_070.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0059 : Certifies 59 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B001 (j : Fin 30) :
    Certifies (30 + j.val) := by
  fin_cases j
  · exact projection_0030
  · exact projection_0031
  · exact projection_0032
  · exact projection_0033
  · exact projection_0034
  · exact projection_0035
  · exact projection_0036
  · exact projection_0037
  · exact projection_0038
  · exact projection_0039
  · exact projection_0040
  · exact projection_0041
  · exact projection_0042
  · exact projection_0043
  · exact projection_0044
  · exact projection_0045
  · exact projection_0046
  · exact projection_0047
  · exact projection_0048
  · exact projection_0049
  · exact projection_0050
  · exact projection_0051
  · exact projection_0052
  · exact projection_0053
  · exact projection_0054
  · exact projection_0055
  · exact projection_0056
  · exact projection_0057
  · exact projection_0058
  · exact projection_0059

end Nonrational.TerminalVerification
