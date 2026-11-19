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
/- Source: ProjectionCertificates/P0_021.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_021

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 587, 211, 285, 557, 457, 401, 914, 738, 364, 788, 932, 616, 480, 19, 67, 515, 13, 21, 517, 73, 265, 521, 145, 273, 193, 385, 146, 530, 194, 578, 642, 44, 268, 276, 532, 292, 548, 772, 104, 552, 328, 584, 400, 784, 224, 352, 608, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_587, vertices_211, vertices_285, vertices_557, vertices_457, vertices_401, vertices_914, vertices_738, vertices_364, vertices_788, vertices_932, vertices_616, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_515, vertices_13, vertices_21, vertices_517, vertices_73, vertices_265, vertices_521, vertices_145, vertices_273, vertices_193, vertices_385, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_400, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_587), (false, vertices_211), (false, vertices_285), (false, vertices_557), (false, vertices_457), (false, vertices_401), (true, vertices_642), (true, vertices_292), (true, vertices_772), (true, vertices_104), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_401) then 11 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_784) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 6 7 8 3 914 642 2
cert_row_4 1 4 5 6 8 0 738 224 3
cert_row_4 2 1 4 5 7 2 364 292 2
cert_row_4 3 4 6 7 8 1 932 416 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 0 0 3 6 7 146 914 3
cert_coverFacet 1 738
cert_cover_5 1 1 0 4 5 6 194 738 1
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 44 364 3
cert_coverFacet 3 788
cert_cover_2 3 3 1 7 8 276 788 3
cert_coverFacet 4 932
cert_cover_5 4 3 1 4 6 7 292 932 2
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 480
cert_cover_2 6 5 4 6 7 224 480 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_021

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 587, 179, 339, 557, 165, 121, 402, 962, 364, 908, 436, 840, 368, 19, 67, 131, 515, 37, 133, 517, 41, 73, 521, 49, 81, 161, 146, 274, 322, 578, 386, 642, 44, 268, 524, 164, 292, 388, 644, 104, 328, 584, 776, 112, 176, 304, 336, 400, 352, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_587, vertices_179, vertices_339, vertices_557, vertices_165, vertices_121, vertices_402, vertices_962, vertices_364, vertices_908, vertices_436, vertices_840, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_49, vertices_81, vertices_161, vertices_146, vertices_274, vertices_322, vertices_578, vertices_386, vertices_642, vertices_44, vertices_268, vertices_524, vertices_164, vertices_292, vertices_388, vertices_644, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_587), (false, vertices_179), (false, vertices_339), (false, vertices_557), (false, vertices_165), (false, vertices_121), (true, vertices_386), (true, vertices_268), (true, vertices_292), (true, vertices_388), (true, vertices_328), (true, vertices_776), (true, vertices_304), (true, vertices_400), (true, vertices_352), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_557) then 14 else
  if p.val = (false, vertices_165) then 11 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_352) then 8 else
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
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
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
cert_row_4 0 5 6 7 8 0 962 832 1
cert_row_4 1 1 2 4 7 5 364 44 3
cert_row_4 2 1 6 7 8 2 908 388 3
cert_row_4 3 3 4 6 7 1 436 176 3
cert_rows
cert_pivot_2 0 5 2 1
cert_heightProof 4
cert_coverFacet 0 402
cert_cover_2 0 3 0 6 7 146 402 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 322 962 2
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 5 44 364 3
cert_coverFacet 3 908
cert_cover_5 3 2 1 2 6 7 268 908 2
cert_coverFacet 4 436
cert_cover_5 4 3 1 3 4 6 164 436 1
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_029

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 331, 307, 659, 109, 181, 645, 353, 794, 716, 484, 840, 432, 976, 11, 19, 259, 515, 13, 37, 133, 517, 73, 49, 145, 97, 289, 321, 641, 266, 522, 274, 530, 76, 524, 100, 164, 196, 644, 328, 584, 776, 176, 304, 400, 656, 784, 352, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_331, vertices_307, vertices_659, vertices_109, vertices_181, vertices_645, vertices_353, vertices_794, vertices_716, vertices_484, vertices_840, vertices_432, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_515, vertices_13, vertices_37, vertices_133, vertices_517, vertices_73, vertices_49, vertices_145, vertices_97, vertices_289, vertices_321, vertices_641, vertices_266, vertices_522, vertices_274, vertices_530, vertices_76, vertices_524, vertices_100, vertices_164, vertices_196, vertices_644, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_400, vertices_656, vertices_784, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_331), (false, vertices_307), (false, vertices_659), (false, vertices_109), (false, vertices_181), (false, vertices_645), (false, vertices_353), (true, vertices_196), (true, vertices_584), (true, vertices_776), (true, vertices_400), (true, vertices_784), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 19 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 12 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_109) then 13 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_645) then 9 else
  if p.val = (false, vertices_353) then 10 else
  if p.val = (true, vertices_196) then 0 else
  if p.val = (true, vertices_584) then 1 else
  if p.val = (true, vertices_776) then 2 else
  if p.val = (true, vertices_400) then 3 else
  if p.val = (true, vertices_784) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
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
cert_row_4 0 2 3 7 8 0 794 776 1
cert_row_4 1 1 5 6 8 2 716 196 3
cert_row_4 2 4 5 6 7 1 484 352 2
cert_row_4 3 5 6 7 8 3 976 448 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 266 794 2
cert_coverFacet 1 716
cert_cover_5 1 1 1 2 5 6 76 716 3
cert_coverFacet 2 484
cert_cover_5 2 2 1 4 5 6 100 484 3
cert_coverFacet 3 840
cert_cover_2 3 5 2 7 8 328 840 3
cert_coverFacet 4 432
cert_cover_2 4 4 3 6 7 176 432 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 400 976 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_035

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 539, 147, 419, 301, 589, 409, 722, 674, 348, 740, 356, 600, 496, 19, 35, 131, 515, 13, 37, 517, 25, 265, 521, 145, 289, 385, 146, 530, 162, 546, 642, 76, 268, 100, 292, 548, 324, 580, 88, 280, 536, 584, 208, 336, 592, 400, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_539, vertices_147, vertices_419, vertices_301, vertices_589, vertices_409, vertices_722, vertices_674, vertices_348, vertices_740, vertices_356, vertices_600, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_13, vertices_37, vertices_517, vertices_25, vertices_265, vertices_521, vertices_145, vertices_289, vertices_385, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_76, vertices_268, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_88, vertices_280, vertices_536, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_539), (false, vertices_147), (false, vertices_419), (false, vertices_301), (false, vertices_589), (false, vertices_409), (true, vertices_642), (true, vertices_100), (true, vertices_324), (true, vertices_88), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_352), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_147) then 11 else
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_208) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
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
cert_row_4 0 3 5 6 8 0 722 208 3
cert_row_4 1 1 3 5 7 2 348 324 1
cert_row_4 2 4 5 6 8 1 740 224 3
cert_row_4 3 4 5 6 7 3 496 224 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 0 0 3 5 6 146 722 2
cert_coverFacet 1 674
cert_cover_2 1 4 0 6 8 162 674 3
cert_coverFacet 2 348
cert_cover_5 2 1 1 2 3 5 76 348 2
cert_coverFacet 3 740
cert_cover_5 3 2 1 4 5 6 100 740 3
cert_coverFacet 4 356
cert_cover_2 4 4 1 5 7 100 356 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 208 496 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_037

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 331, 651, 291, 205, 661, 357, 810, 628, 212, 472, 904, 368, 944, 11, 35, 259, 515, 37, 69, 133, 517, 73, 137, 289, 321, 641, 266, 522, 290, 546, 84, 148, 532, 100, 548, 196, 200, 328, 392, 648, 776, 112, 304, 560, 208, 336, 400, 656, 352, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_331, vertices_651, vertices_291, vertices_205, vertices_661, vertices_357, vertices_810, vertices_628, vertices_212, vertices_472, vertices_904, vertices_368, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_37, vertices_69, vertices_133, vertices_517, vertices_73, vertices_137, vertices_289, vertices_321, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_331), (false, vertices_651), (false, vertices_291), (false, vertices_205), (false, vertices_661), (false, vertices_357), (true, vertices_84), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_896) then 10 else
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
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
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
cert_row_4 2 3 5 6 7 2 472 208 3
cert_row_4 3 4 6 7 8 3 944 800 1
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 0 0 2 4 7 266 810 2
cert_coverFacet 1 628
cert_cover_5 1 1 1 3 4 5 84 628 2
cert_coverFacet 2 212
cert_cover_2 2 3 1 5 6 84 212 3
cert_coverFacet 3 472
cert_cover_5 3 2 2 3 5 6 200 472 1
cert_coverFacet 4 904
cert_cover_2 4 6 2 7 8 392 904 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_040

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_044.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_044

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 555, 163, 451, 589, 341, 233, 434, 802, 820, 724, 696, 712, 464, 35, 131, 259, 515, 69, 261, 517, 41, 73, 521, 161, 193, 321, 162, 290, 546, 386, 770, 84, 276, 532, 580, 772, 168, 552, 200, 584, 648, 176, 304, 560, 208, 336, 400, 656, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_555, vertices_163, vertices_451, vertices_589, vertices_341, vertices_233, vertices_434, vertices_802, vertices_820, vertices_724, vertices_696, vertices_712, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_521, vertices_161, vertices_193, vertices_321, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_555), (false, vertices_163), (false, vertices_451), (false, vertices_589), (false, vertices_341), (false, vertices_233), (true, vertices_290), (true, vertices_532), (true, vertices_648), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_163) then 11 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (true, vertices_290) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_648) then 2 else
  if p.val = (true, vertices_176) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 4 6 7 0 434 176 3
cert_row_4 1 1 3 4 8 7 820 532 2
cert_row_4 2 3 5 6 8 1 724 208 3
cert_row_4 3 3 4 6 8 2 696 176 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 434
cert_cover_5 0 0 0 3 4 6 162 434 1
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 276 820 2
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 168 696 1
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_044

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 837, 665, 465, 737, 614, 294, 774, 314, 538, 682, 484, 440, 145, 273, 529, 193, 321, 577, 641, 769, 38, 262, 518, 26, 42, 522, 274, 530, 290, 546, 770, 100, 292, 324, 580, 772, 312, 152, 536, 168, 648, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_837, vertices_665, vertices_465, vertices_737, vertices_614, vertices_294, vertices_774, vertices_314, vertices_538, vertices_682, vertices_484, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_312, vertices_152, vertices_536, vertices_168, vertices_648, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_837), (false, vertices_665), (false, vertices_465), (false, vertices_737), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_292), (true, vertices_312), (true, vertices_168), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 16 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 13 else
  if p.val = (false, vertices_837) then 15 else
  if p.val = (false, vertices_665) then 17 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_312) then 18 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_312), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 7 3 312
cert_row_4 1 0 4 6 8 2 682 546 2
cert_row_4 2 1 4 5 8 0 614 100 3
cert_row_4 3 4 5 6 7 1 484 224 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 38 614 3
cert_coverFacet 1 294
cert_cover_2 1 1 0 4 7 38 294 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 314
cert_cover_5 3 0 0 2 3 4 26 314 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 682
cert_cover_5 5 1 0 2 4 6 42 682 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 440
cert_cover_5 7 0 2 3 4 6 312 440 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_046

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_056.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_056

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 653, 421, 793, 361, 710, 346, 594, 786, 482, 604, 228, 13, 37, 133, 105, 265, 521, 289, 385, 641, 769, 82, 274, 530, 194, 322, 578, 386, 642, 770, 76, 524, 100, 164, 196, 580, 644, 88, 280, 536, 328, 592, 784, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_653, vertices_421, vertices_793, vertices_361, vertices_710, vertices_346, vertices_594, vertices_786, vertices_482, vertices_604, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_105, vertices_265, vertices_521, vertices_289, vertices_385, vertices_641, vertices_769, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_536, vertices_328, vertices_592, vertices_784, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_653), (false, vertices_421), (false, vertices_793), (false, vertices_361), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_793) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_224) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 4 482 194 3
cert_row_4 1 0 1 5 8 6 710 578 1
cert_row_4 2 2 3 5 7 0 346 88 3
cert_row_4 3 2 3 5 8 1 604 88 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 82 346 1
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 482
cert_cover_5 4 0 0 4 5 6 194 482 1
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 76 604 2
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_056

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 901, 617, 689, 481, 662, 278, 774, 314, 602, 362, 436, 568, 97, 161, 545, 321, 577, 385, 641, 769, 22, 262, 518, 26, 298, 74, 274, 530, 322, 578, 770, 148, 276, 388, 644, 772, 56, 536, 104, 552, 584, 176, 304, 560, 656, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_901, vertices_617, vertices_689, vertices_481, vertices_662, vertices_278, vertices_774, vertices_314, vertices_602, vertices_362, vertices_436, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_26, vertices_298, vertices_74, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_148, vertices_276, vertices_388, vertices_644, vertices_772, vertices_56, vertices_536, vertices_104, vertices_552, vertices_584, vertices_176, vertices_304, vertices_560, vertices_656, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_901), (false, vertices_617), (false, vertices_689), (false, vertices_481), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_298), (true, vertices_74), (true, vertices_274), (true, vertices_530), (true, vertices_148), (true, vertices_276), (true, vertices_56), (true, vertices_536), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_298) then 14 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_304) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_298), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 8 5 602 26 3
cert_row_4 1 0 1 3 6 8 662 22 3
cert_row_4 2 3 4 6 7 1 436 176 3
cert_row_2 3 2 4 7 0 298
cert_rows
cert_pivot_2 5 8 1 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 22 662 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 314
cert_cover_5 3 3 0 2 3 4 26 314 3
cert_coverFacet 4 602
cert_cover_5 4 0 0 2 3 5 26 602 3
cert_coverFacet 5 362
cert_cover_5 5 3 0 2 4 5 298 362 3
cert_coverFacet 6 436
cert_cover_5 6 2 1 3 4 6 148 436 2
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_059

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_062.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_062

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 211, 835, 781, 409, 369, 678, 242, 610, 428, 652, 868, 432, 67, 131, 515, 137, 265, 521, 81, 145, 273, 321, 769, 210, 98, 162, 546, 578, 642, 140, 268, 524, 164, 292, 548, 644, 772, 392, 648, 112, 176, 304, 400, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_211, vertices_835, vertices_781, vertices_409, vertices_369, vertices_678, vertices_242, vertices_610, vertices_428, vertices_652, vertices_868, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_321, vertices_769, vertices_210, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_211), (false, vertices_835), (false, vertices_781), (false, vertices_409), (false, vertices_369), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_140), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_176), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_211) then 14 else
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_409) then 18 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 1 4 6 7 2 428 164 3
cert_row_4 1 1 4 5 8 7 868 548 2
cert_row_4 2 0 4 6 8 1 678 162 3
cert_row_2 3 3 5 6 0 210
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 162 678 1
cert_coverFacet 1 242
cert_cover_5 1 3 0 3 4 5 210 242 2
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 140 428 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 868
cert_cover_5 5 1 1 4 5 7 292 868 2
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_062

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_065.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_065

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 395, 51, 595, 707, 653, 269, 565, 114, 482, 812, 968, 880, 19, 35, 579, 131, 259, 13, 37, 261, 517, 137, 265, 49, 529, 641, 50, 82, 98, 290, 194, 386, 268, 524, 292, 548, 392, 648, 776, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_395, vertices_51, vertices_595, vertices_707, vertices_653, vertices_269, vertices_565, vertices_114, vertices_482, vertices_812, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_579, vertices_131, vertices_259, vertices_13, vertices_37, vertices_261, vertices_517, vertices_137, vertices_265, vertices_49, vertices_529, vertices_641, vertices_50, vertices_82, vertices_98, vertices_290, vertices_194, vertices_386, vertices_268, vertices_524, vertices_292, vertices_548, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_395), (false, vertices_51), (false, vertices_595), (false, vertices_707), (false, vertices_653), (false, vertices_269), (false, vertices_565), (true, vertices_98), (true, vertices_776), (true, vertices_112), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 9 17 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 10 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_51) then 7 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_653) then 11 else
  if p.val = (false, vertices_269) then 8 else
  if p.val = (false, vertices_565) then 12 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_776) then 1 else
  if p.val = (true, vertices_112) then 2 else
  if p.val = (true, vertices_352) then 3 else
  if p.val = (true, vertices_800) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_832) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
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
cert_row_4 0 4 5 6 7 0 482 352 2
cert_row_4 1 2 4 7 8 1 812 776 1
cert_row_4 2 5 6 7 8 2 968 448 3
cert_row_4 3 4 5 7 8 3 880 352 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 114
cert_cover_2 0 3 0 4 5 50 114 3
cert_coverFacet 1 482
cert_cover_5 1 0 0 4 5 6 98 482 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 268 812 2
cert_coverFacet 3 968
cert_cover_5 3 2 2 5 6 7 392 968 1
cert_coverFacet 4 880
cert_cover_5 4 3 3 4 5 7 112 880 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_065

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_067.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_067

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 707, 653, 409, 841, 369, 678, 114, 178, 866, 812, 396, 436, 195, 137, 265, 521, 81, 145, 273, 321, 577, 641, 50, 82, 146, 98, 162, 546, 578, 642, 140, 268, 524, 164, 292, 548, 388, 644, 392, 776, 112, 176, 304, 400, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_707, vertices_653, vertices_409, vertices_841, vertices_369, vertices_678, vertices_114, vertices_178, vertices_866, vertices_812, vertices_396, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_195, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_321, vertices_577, vertices_641, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_707), (false, vertices_653), (false, vertices_409), (false, vertices_841), (false, vertices_369), (true, vertices_50), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_176), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 12 else
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_409) then 17 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 4 7 8 5 866 546 2
cert_row_4 1 1 4 6 8 0 678 164 3
cert_row_4 2 1 4 7 8 2 812 292 3
cert_row_4 3 3 4 6 7 1 436 176 3
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 114
cert_cover_2 1 3 0 4 5 50 114 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 866
cert_cover_5 3 0 0 4 5 7 98 866 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 268 812 2
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_067

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_069.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_069

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 395, 275, 531, 109, 173, 597, 345, 850, 930, 868, 676, 488, 19, 131, 259, 515, 45, 69, 133, 517, 73, 137, 265, 81, 273, 529, 274, 530, 386, 642, 770, 100, 164, 548, 580, 644, 104, 168, 328, 392, 336, 592, 352, 416, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_395, vertices_275, vertices_531, vertices_109, vertices_173, vertices_597, vertices_345, vertices_850, vertices_930, vertices_868, vertices_676, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_45, vertices_69, vertices_133, vertices_517, vertices_73, vertices_137, vertices_265, vertices_81, vertices_273, vertices_529, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_104, vertices_168, vertices_328, vertices_392, vertices_336, vertices_592, vertices_352, vertices_416, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_395), (false, vertices_275), (false, vertices_531), (false, vertices_109), (false, vertices_173), (false, vertices_597), (false, vertices_345), (true, vertices_770), (true, vertices_548), (true, vertices_352), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 10 else
  if p.val = (false, vertices_395) then 11 else
  if p.val = (false, vertices_275) then 7 else
  if p.val = (false, vertices_531) then 8 else
  if p.val = (false, vertices_109) then 14 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_345) then 17 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_352) then 2 else
  if p.val = (true, vertices_416) then 3 else
  if p.val = (true, vertices_672) then 4 else
  if p.val = (true, vertices_800) then 5 else
  if p.val = (true, vertices_832) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 7 8 3 850 770 1
cert_row_4 1 4 6 7 8 0 930 416 3
cert_row_4 2 4 5 7 8 1 868 352 3
cert_row_4 3 4 5 6 7 2 488 352 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 850
cert_cover_5 0 0 0 3 5 7 274 850 2
cert_coverFacet 1 930
cert_cover_5 1 1 0 4 6 7 386 930 1
cert_coverFacet 2 868
cert_cover_5 2 2 1 4 5 7 100 868 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 488
cert_cover_5 4 3 2 4 5 6 104 488 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_069

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 651, 835, 217, 617, 465, 806, 646, 684, 436, 376, 184, 864, 131, 259, 515, 73, 137, 521, 209, 321, 577, 385, 134, 262, 518, 642, 770, 164, 292, 548, 388, 644, 56, 88, 152, 104, 168, 552, 648, 176, 304, 336, 400, 352, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_651, vertices_835, vertices_217, vertices_617, vertices_465, vertices_806, vertices_646, vertices_684, vertices_436, vertices_376, vertices_184, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_209, vertices_321, vertices_577, vertices_385, vertices_134, vertices_262, vertices_518, vertices_642, vertices_770, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_104, vertices_168, vertices_552, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_651), (false, vertices_835), (false, vertices_217), (false, vertices_617), (false, vertices_465), (true, vertices_518), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_56), (true, vertices_168), (true, vertices_176), (true, vertices_304), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_617) then 17 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 7 8 0 806 292 3
cert_row_4 1 1 2 4 6 8 684 164 1
cert_row_4 2 3 4 6 7 1 436 176 3
cert_row_4 3 3 4 5 7 2 376 304 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 262 806 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 164 684 1
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 164 436 1
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_072

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_080.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_080

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 541, 301, 341, 425, 713, 593, 790, 722, 338, 930, 684, 804, 13, 21, 261, 297, 137, 521, 81, 529, 193, 321, 577, 385, 82, 274, 530, 194, 322, 386, 642, 770, 44, 524, 276, 532, 292, 548, 772, 168, 648, 336, 592, 416, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_541, vertices_301, vertices_341, vertices_425, vertices_713, vertices_593, vertices_790, vertices_722, vertices_338, vertices_930, vertices_684, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_297, vertices_137, vertices_521, vertices_81, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_168, vertices_648, vertices_336, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_541), (false, vertices_301), (false, vertices_341), (false, vertices_425), (false, vertices_713), (false, vertices_593), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_548), (true, vertices_772), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 11 else
  if p.val = (false, vertices_541) then 13 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_713) then 16 else
  if p.val = (false, vertices_593) then 9 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 8 5 722 530 2
cert_row_4 1 0 1 7 8 3 790 770 1
cert_row_4 2 4 6 7 8 0 930 416 3
cert_row_4 3 2 4 6 8 1 684 168 3
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 722
cert_cover_5 1 0 0 3 5 6 82 722 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 930
cert_cover_5 3 2 0 4 6 7 386 930 1
cert_coverFacet 4 684
cert_cover_5 4 3 1 2 4 6 44 684 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_080

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_082.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_082

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 805, 233, 297, 841, 689, 566, 342, 838, 210, 658, 436, 472, 424, 41, 73, 265, 161, 289, 545, 193, 577, 641, 769, 22, 326, 518, 82, 146, 530, 194, 578, 642, 52, 276, 292, 548, 772, 168, 296, 200, 328, 392, 176, 560, 208, 336, 400, 656, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_805, vertices_233, vertices_297, vertices_841, vertices_689, vertices_566, vertices_342, vertices_838, vertices_210, vertices_658, vertices_436, vertices_472, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_22, vertices_326, vertices_518, vertices_82, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_805), (false, vertices_233), (false, vertices_297), (false, vertices_841), (false, vertices_689), (true, vertices_22), (true, vertices_326), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_52), (true, vertices_276), (true, vertices_392), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_297) then 12 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_326) then 15 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 22 518 82 146 530 52 276 392 208 336 400 416 297 707 326 805 233 841 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_4 1 1 3 6 7 4 436 276 2
cert_row_4 2 3 5 6 7 2 472 208 3
cert_row_2 3 1 5 7 0 326
cert_rows
cert_pivot_2 8 4 2 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 342
cert_cover_5 1 3 0 1 3 5 22 342 3
cert_coverFacet 2 838
cert_cover_5 2 3 0 1 5 8 326 838 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 52 436 3
cert_coverFacet 6 472
cert_cover_5 6 2 2 3 5 6 200 472 1
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_082

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_086.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_086

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 597, 809, 369, 689, 398, 782, 214, 582, 450, 684, 660, 440, 464, 49, 81, 529, 289, 545, 321, 577, 769, 270, 70, 134, 518, 194, 322, 578, 386, 770, 140, 524, 84, 148, 532, 580, 644, 168, 296, 552, 392, 776, 176, 304, 208, 336, 400, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_597, vertices_809, vertices_369, vertices_689, vertices_398, vertices_782, vertices_214, vertices_582, vertices_450, vertices_684, vertices_660, vertices_440, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_270, vertices_70, vertices_134, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_597), (false, vertices_809), (false, vertices_369), (false, vertices_689), (true, vertices_270), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 5 214 134 2
cert_row_4 1 1 2 4 6 8 684 140 2
cert_row_4 2 2 4 6 7 3 440 168 3
cert_row_2 3 1 2 7 0 270
cert_rows
cert_pivot_2 5 8 3 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 270 398 3
cert_coverFacet 1 782
cert_cover_5 1 3 0 1 2 8 270 782 3
cert_coverFacet 2 214
cert_cover_5 2 0 0 1 3 5 70 214 2
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 684
cert_cover_5 5 1 1 2 4 6 140 684 2
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 440
cert_cover_5 7 2 2 3 4 6 168 440 1
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_086

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 837, 793, 465, 737, 302, 782, 614, 154, 538, 170, 674, 484, 440, 145, 273, 529, 193, 321, 577, 641, 769, 270, 38, 518, 26, 42, 138, 522, 146, 530, 162, 546, 642, 100, 292, 324, 580, 772, 152, 280, 536, 168, 296, 776, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_837, vertices_793, vertices_465, vertices_737, vertices_302, vertices_782, vertices_614, vertices_154, vertices_538, vertices_170, vertices_674, vertices_484, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_270, vertices_38, vertices_518, vertices_26, vertices_42, vertices_138, vertices_522, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_776, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_837), (false, vertices_793), (false, vertices_465), (false, vertices_737), (true, vertices_270), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_100), (true, vertices_292), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 38 3
cert_row_4 1 1 4 6 7 5 484 292 2
cert_row_4 2 2 4 6 7 3 440 168 3
cert_row_2 3 1 2 7 0 270
cert_rows
cert_pivot_2 8 5 3 0
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 3 0 1 2 4 270 302 3
cert_coverFacet 1 782
cert_cover_5 1 3 0 1 2 8 270 782 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 38 614 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 170
cert_cover_2 5 2 0 4 6 42 170 3
cert_coverFacet 6 674
cert_cover_2 6 4 0 6 8 162 674 3
cert_coverFacet 7 484
cert_cover_5 7 1 1 4 5 6 100 484 3
cert_coverFacet 8 440
cert_cover_5 8 2 2 3 4 6 152 440 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_087

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_088.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_088

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 789, 613, 421, 345, 361, 902, 218, 402, 786, 738, 676, 440, 232, 37, 261, 517, 329, 81, 273, 529, 97, 289, 577, 82, 146, 274, 530, 194, 578, 386, 642, 770, 164, 548, 388, 644, 772, 88, 152, 280, 104, 168, 296, 200, 400, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_789, vertices_613, vertices_421, vertices_345, vertices_361, vertices_902, vertices_218, vertices_402, vertices_786, vertices_738, vertices_676, vertices_440, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_329, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_400, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_789), (false, vertices_613), (false, vertices_421), (false, vertices_345), (false, vertices_361), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_400), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 146 1 274 2 194 386 642 770 644 152 168 200 400 224 672 595 789 613 421 345 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 6 7 8 1 902 386 3
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 2 3 5 6 0 218 88 3
cert_row_4 3 3 4 6 7 2 440 400 1
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 5 82 218 1
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 152 440 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_088

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_089.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_089

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 405, 421, 601, 281, 361, 689, 662, 358, 166, 774, 842, 674, 796, 389, 25, 73, 265, 145, 273, 529, 97, 161, 289, 545, 577, 38, 134, 262, 518, 98, 162, 546, 322, 578, 642, 770, 148, 276, 532, 164, 292, 772, 280, 536, 328, 584, 776, 656, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_405, vertices_421, vertices_601, vertices_281, vertices_361, vertices_689, vertices_662, vertices_358, vertices_166, vertices_774, vertices_842, vertices_674, vertices_796] (by decide +kernel)
  polygons := literalFinset [vertices_389, vertices_25, vertices_73, vertices_265, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_38, vertices_134, vertices_262, vertices_518, vertices_98, vertices_162, vertices_546, vertices_322, vertices_578, vertices_642, vertices_770, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_772, vertices_280, vertices_536, vertices_328, vertices_584, vertices_776, vertices_656, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_405), (false, vertices_421), (false, vertices_601), (false, vertices_281), (false, vertices_361), (false, vertices_689), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_162), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_772), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 13 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_601) then 18 else
  if p.val = (false, vertices_281) then 11 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_776) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 8 6 662 518 2
cert_row_4 1 0 1 5 7 4 358 262 2
cert_row_4 2 2 5 7 8 0 842 328 3
cert_row_4 3 2 3 7 8 1 796 280 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 38 358 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 842
cert_cover_5 4 2 0 2 5 7 322 842 1
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 276 796 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_089

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_091.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_091

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 155, 395, 803, 29, 557, 361, 914, 156, 108, 460, 724, 612, 992, 139, 19, 259, 515, 13, 21, 517, 25, 41, 265, 289, 545, 146, 530, 386, 770, 28, 44, 76, 140, 148, 532, 100, 548, 196, 580, 152, 104, 328, 392, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_155, vertices_395, vertices_803, vertices_29, vertices_557, vertices_361, vertices_914, vertices_156, vertices_108, vertices_460, vertices_724, vertices_612, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_19, vertices_259, vertices_515, vertices_13, vertices_21, vertices_517, vertices_25, vertices_41, vertices_265, vertices_289, vertices_545, vertices_146, vertices_530, vertices_386, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_152, vertices_104, vertices_328, vertices_392, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_155), (false, vertices_395), (false, vertices_803), (false, vertices_29), (false, vertices_557), (false, vertices_361), (true, vertices_76), (true, vertices_140), (true, vertices_148), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_656), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 13 else
  if p.val = (false, vertices_155) then 17 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_29) then 11 else
  if p.val = (false, vertices_557) then 14 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (true, vertices_76) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 6 7 8 0 914 656 2
cert_row_4 1 1 5 6 7 2 460 196 3
cert_row_4 2 3 5 6 8 1 724 656 1
cert_row_4 3 5 6 7 8 4 992 448 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 0 0 3 6 7 146 914 3
cert_coverFacet 1 156
cert_cover_2 1 2 1 3 6 28 156 3
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 460
cert_cover_5 3 1 1 2 5 6 76 460 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 148 724 2
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_091

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_092.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_092

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 291, 451, 709, 313, 409, 681, 838, 570, 306, 786, 668, 468, 788, 35, 67, 259, 281, 41, 137, 289, 545, 193, 577, 385, 641, 50, 274, 530, 290, 546, 322, 578, 770, 148, 276, 532, 196, 324, 580, 644, 772, 56, 152, 536, 552, 648, 304, 400, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_291, vertices_451, vertices_709, vertices_313, vertices_409, vertices_681, vertices_838, vertices_570, vertices_306, vertices_786, vertices_668, vertices_468, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_281, vertices_41, vertices_137, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_552, vertices_648, vertices_304, vertices_400, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_291), (false, vertices_451), (false, vertices_709), (false, vertices_313), (false, vertices_409), (false, vertices_681), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_772), (true, vertices_536), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 13 else
  if p.val = (false, vertices_291) then 11 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_4 0 0 2 3 8 4 570 530 1
cert_row_4 1 1 5 7 8 0 838 324 3
cert_row_4 2 1 3 6 8 2 668 148 3
cert_row_4 3 3 5 6 7 1 468 400 1
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 570
cert_cover_5 1 0 0 2 3 4 50 570 1
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 668
cert_cover_5 4 2 1 2 3 6 148 668 1
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 148 468 2
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_092

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_093.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_093

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 781, 213, 389, 313, 601, 401, 230, 422, 774, 810, 626, 568, 496, 69, 133, 261, 517, 25, 265, 521, 81, 145, 273, 577, 385, 166, 70, 262, 518, 98, 290, 546, 578, 770, 196, 388, 772, 56, 536, 296, 552, 776, 112, 304, 560, 208, 592, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_781, vertices_213, vertices_389, vertices_313, vertices_601, vertices_401, vertices_230, vertices_422, vertices_774, vertices_810, vertices_626, vertices_568, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_385, vertices_166, vertices_70, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_196, vertices_388, vertices_772, vertices_56, vertices_536, vertices_296, vertices_552, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_781), (false, vertices_213), (false, vertices_389), (false, vertices_313), (false, vertices_601), (false, vertices_401), (true, vertices_166), (true, vertices_262), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_389) then 10 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_401) then 11 else
  if p.val = (true, vertices_166) then 14 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 7 8 2 810 290 3
cert_row_4 1 0 3 4 5 8 626 98 1
cert_row_4 2 4 5 6 7 3 496 224 3
cert_row_2 3 1 4 6 0 166
cert_rows
cert_pivot_2 2 8 3 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 3 0 1 4 5 166 230 3
cert_coverFacet 1 422
cert_cover_5 1 3 0 1 4 7 166 422 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 810
cert_cover_5 3 0 0 2 4 7 290 810 1
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 98 626 1
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 496
cert_cover_5 6 2 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_093

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_094.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_094

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 781, 677, 453, 409, 169, 838, 122, 346, 778, 738, 708, 184, 496, 133, 261, 517, 41, 137, 265, 521, 161, 545, 385, 90, 42, 266, 522, 98, 546, 322, 578, 770, 196, 324, 580, 644, 772, 56, 152, 280, 168, 776, 112, 176, 336, 400, 224, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_781, vertices_677, vertices_453, vertices_409, vertices_169, vertices_838, vertices_122, vertices_346, vertices_778, vertices_738, vertices_708, vertices_184, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_385, vertices_90, vertices_42, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_781), (false, vertices_677), (false, vertices_453), (false, vertices_409), (false, vertices_169), (true, vertices_90), (true, vertices_266), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_580), (true, vertices_56), (true, vertices_112), (true, vertices_176), (true, vertices_336), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_169) then 12 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 266 98 322 578 770 580 56 112 176 336 224 704 169 555 90 781 677 453 409
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 7 8 1 838 322 3
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_4 2 3 5 6 7 4 496 336 2
cert_row_2 3 2 3 5 0 90
cert_rows
cert_pivot_2 1 8 4 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 122
cert_cover_5 1 3 0 2 3 4 90 122 3
cert_coverFacet 2 346
cert_cover_5 2 3 0 2 3 7 90 346 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 98 738 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 496
cert_cover_5 7 2 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_094

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_095.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_095

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 541, 269, 709, 121, 457, 593, 782, 678, 810, 482, 568, 360, 752, 13, 133, 261, 517, 25, 73, 265, 81, 529, 193, 577, 385, 134, 262, 518, 778, 162, 290, 546, 386, 268, 524, 644, 56, 536, 104, 296, 552, 328, 112, 560, 592, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_541, vertices_269, vertices_709, vertices_121, vertices_457, vertices_593, vertices_782, vertices_678, vertices_810, vertices_482, vertices_568, vertices_360, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_25, vertices_73, vertices_265, vertices_81, vertices_529, vertices_193, vertices_577, vertices_385, vertices_134, vertices_262, vertices_518, vertices_778, vertices_162, vertices_290, vertices_546, vertices_386, vertices_268, vertices_524, vertices_644, vertices_56, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_112, vertices_560, vertices_592, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_541), (false, vertices_269), (false, vertices_709), (false, vertices_121), (false, vertices_457), (false, vertices_593), (true, vertices_518), (true, vertices_778), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_296), (true, vertices_552), (true, vertices_560), (true, vertices_224), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_269) then 10 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_593) then 11 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_778) then 14 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 4 6 8 1 678 162 3
cert_row_4 1 4 5 6 8 3 752 224 3
cert_row_4 2 0 5 6 7 4 482 386 1
cert_row_2 3 2 7 8 0 778
cert_rows
cert_pivot_2 1 3 4 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 3 0 1 2 7 262 782 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 134 678 2
cert_coverFacet 2 810
cert_cover_5 2 3 0 2 4 7 778 810 2
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 162 482 2
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 360
cert_cover_2 5 4 2 5 7 104 360 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_095

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_096.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_096

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 331, 707, 661, 409, 481, 558, 362, 610, 284, 540, 300, 436, 740, 11, 67, 515, 25, 265, 145, 529, 193, 321, 385, 641, 42, 330, 522, 98, 546, 578, 28, 44, 268, 524, 148, 276, 532, 164, 292, 548, 644, 280, 536, 296, 400, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_331, vertices_707, vertices_661, vertices_409, vertices_481, vertices_558, vertices_362, vertices_610, vertices_284, vertices_540, vertices_300, vertices_436, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_515, vertices_25, vertices_265, vertices_145, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_42, vertices_330, vertices_522, vertices_98, vertices_546, vertices_578, vertices_28, vertices_44, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_280, vertices_536, vertices_296, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_331), (false, vertices_707), (false, vertices_661), (false, vertices_409), (false, vertices_481), (true, vertices_42), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_296), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 1 4 6 7 3 436 164 3
cert_row_4 1 1 4 5 8 6 740 548 2
cert_row_4 2 0 2 4 8 1 558 42 3
cert_row_2 3 2 5 7 0 330
cert_rows
cert_pivot_2 3 6 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 362
cert_cover_5 1 3 0 2 4 5 42 362 3
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 436
cert_cover_5 6 0 1 3 4 6 148 436 2
cert_coverFacet 7 740
cert_cover_5 7 1 1 4 5 6 164 740 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_096

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_097.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_097

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 707, 387, 589, 345, 241, 401, 806, 434, 674, 124, 316, 780, 740, 131, 259, 515, 73, 265, 521, 81, 145, 273, 193, 577, 385, 162, 290, 546, 386, 642, 770, 60, 76, 268, 524, 100, 292, 548, 580, 772, 88, 280, 776, 112, 176, 304, 400, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_707, vertices_387, vertices_589, vertices_345, vertices_241, vertices_401, vertices_806, vertices_434, vertices_674, vertices_124, vertices_316, vertices_780, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_193, vertices_577, vertices_385, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_88, vertices_280, vertices_776, vertices_112, vertices_176, vertices_304, vertices_400, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_707), (false, vertices_387), (false, vertices_589), (false, vertices_345), (false, vertices_241), (false, vertices_401), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_60), (true, vertices_268), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_304), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_387) then 10 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_401) then 11 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 6 8 5 740 548 2
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 3 4 6 7 0 434 176 3
cert_row_2 3 2 3 4 1 60
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 434
cert_cover_5 1 2 0 3 4 6 162 434 1
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 124
cert_cover_5 3 3 1 2 3 5 60 124 3
cert_coverFacet 4 316
cert_cover_5 4 3 1 2 3 7 60 316 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 740
cert_cover_5 6 0 1 4 5 6 100 740 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_097

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_098.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_098

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 803, 707, 613, 217, 369, 782, 394, 650, 124, 316, 716, 804, 408, 131, 259, 515, 81, 145, 273, 97, 289, 545, 193, 577, 138, 266, 522, 386, 642, 770, 60, 76, 268, 524, 100, 292, 548, 580, 772, 88, 152, 280, 200, 392, 648, 112, 304, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_803, vertices_707, vertices_613, vertices_217, vertices_369, vertices_782, vertices_394, vertices_650, vertices_124, vertices_316, vertices_716, vertices_804, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_392, vertices_648, vertices_112, vertices_304, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_803), (false, vertices_707), (false, vertices_613), (false, vertices_217), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_60), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_772), (true, vertices_280), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 12 else
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 1 2 7 8 0 782 268 3
cert_row_4 1 1 2 6 8 5 716 524 2
cert_row_2 2 2 3 4 1 60
cert_rows_3
cert_pivot_3 5 0 1
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 316
cert_cover_5 4 2 1 2 3 7 60 316 3
cert_coverFacet 5 716
cert_cover_5 5 1 1 2 5 6 76 716 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_098

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_099.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_099

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 653, 269, 565, 277, 457, 433, 598, 714, 370, 562, 482, 348, 588, 13, 21, 261, 517, 137, 265, 49, 273, 161, 545, 385, 641, 50, 82, 530, 354, 162, 546, 194, 578, 642, 76, 268, 524, 84, 276, 532, 580, 200, 328, 584, 648, 304, 560, 336, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_653, vertices_269, vertices_565, vertices_277, vertices_457, vertices_433, vertices_598, vertices_714, vertices_370, vertices_562, vertices_482, vertices_348, vertices_588] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_137, vertices_265, vertices_49, vertices_273, vertices_161, vertices_545, vertices_385, vertices_641, vertices_50, vertices_82, vertices_530, vertices_354, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_560, vertices_336, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_653), (false, vertices_269), (false, vertices_565), (false, vertices_277), (false, vertices_457), (false, vertices_433), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_354), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_84), (true, vertices_580), (true, vertices_584), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_269) then 10 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_277) then 11 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_354) then 14 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_336) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 50 1 82 2 530 194 578 76 84 580 584 336 269 277 675 354 653 565 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 8 6 714 578 1
cert_row_4 1 0 1 3 5 8 598 82 1
cert_row_4 2 2 3 5 7 1 348 328 1
cert_row_2 3 4 5 7 0 354
cert_rows
cert_pivot_2 6 8 1 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 82 598 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 194 714 1
cert_coverFacet 2 370
cert_cover_5 2 3 0 3 4 5 50 370 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 354 482 3
cert_coverFacet 5 348
cert_cover_5 5 2 1 2 3 5 76 348 2
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_099

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_100.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_100

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 803, 195, 643, 677, 313, 241, 710, 842, 188, 220, 812, 588, 344, 67, 131, 259, 515, 49, 81, 273, 161, 289, 545, 193, 641, 194, 322, 578, 642, 770, 156, 44, 76, 524, 164, 548, 196, 580, 644, 56, 88, 280, 296, 328, 584, 776, 176, 208, 336, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_803, vertices_195, vertices_643, vertices_677, vertices_313, vertices_241, vertices_710, vertices_842, vertices_188, vertices_220, vertices_812, vertices_588, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_545, vertices_193, vertices_641, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_156, vertices_44, vertices_76, vertices_524, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_336, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_803), (false, vertices_195), (false, vertices_643), (false, vertices_677), (false, vertices_313), (false, vertices_241), (true, vertices_578), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_328), (true, vertices_584), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_195) then 10 else
  if p.val = (false, vertices_643) then 11 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_156) then 17 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_776) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 7 8 4 812 524 2
cert_row_4 1 0 2 5 8 7 842 578 1
cert_row_4 2 1 5 6 8 0 710 196 3
cert_row_2 3 2 3 6 1 156
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 188
cert_cover_5 2 3 1 2 3 4 156 188 3
cert_coverFacet 3 220
cert_cover_5 3 3 1 2 3 5 156 220 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 44 812 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_100

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2043 : Certifies 2043 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_021.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2044 : Certifies 2044 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2045 : Certifies 2045 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2046 : Certifies 2046 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2047 : Certifies 2047 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2048 : Certifies 2048 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_044.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2049 : Certifies 2049 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2050 : Certifies 2050 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_056.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2051 : Certifies 2051 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2052 : Certifies 2052 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_062.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2053 : Certifies 2053 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_065.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2054 : Certifies 2054 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_067.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2055 : Certifies 2055 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_069.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2056 : Certifies 2056 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2057 : Certifies 2057 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_080.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2058 : Certifies 2058 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_082.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2059 : Certifies 2059 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_086.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2060 : Certifies 2060 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2061 : Certifies 2061 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_088.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2062 : Certifies 2062 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_089.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2063 : Certifies 2063 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_091.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2064 : Certifies 2064 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_092.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2065 : Certifies 2065 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_093.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2066 : Certifies 2066 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_094.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2067 : Certifies 2067 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_095.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2068 : Certifies 2068 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_096.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2069 : Certifies 2069 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_097.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2070 : Certifies 2070 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_098.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2071 : Certifies 2071 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_099.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2072 : Certifies 2072 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_100.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B067 (j : Fin 30) :
    Certifies (2043 + j.val) := by
  fin_cases j
  · exact projection_2043
  · exact projection_2044
  · exact projection_2045
  · exact projection_2046
  · exact projection_2047
  · exact projection_2048
  · exact projection_2049
  · exact projection_2050
  · exact projection_2051
  · exact projection_2052
  · exact projection_2053
  · exact projection_2054
  · exact projection_2055
  · exact projection_2056
  · exact projection_2057
  · exact projection_2058
  · exact projection_2059
  · exact projection_2060
  · exact projection_2061
  · exact projection_2062
  · exact projection_2063
  · exact projection_2064
  · exact projection_2065
  · exact projection_2066
  · exact projection_2067
  · exact projection_2068
  · exact projection_2069
  · exact projection_2070
  · exact projection_2071
  · exact projection_2072

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
