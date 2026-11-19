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
/- Source: ProjectionCertificates/R_m16e10q1_0619.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0619

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 397, 661, 837, 681, 598, 570, 234, 458, 114, 834, 372, 404, 432, 688, 480, 133, 261, 517, 137, 265, 521, 641, 769, 42, 202, 266, 522, 50, 82, 530, 98, 322, 578, 770, 84, 148, 276, 532, 324, 580, 388, 168, 552, 392, 112, 176, 304, 560, 400, 656, 224, 352, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_397, vertices_661, vertices_837, vertices_681, vertices_598, vertices_570, vertices_234, vertices_458, vertices_114, vertices_834, vertices_372, vertices_404, vertices_432, vertices_688, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_641, vertices_769, vertices_42, vertices_202, vertices_266, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_388, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_397), (false, vertices_661), (false, vertices_837), (false, vertices_681), (true, vertices_42), (true, vertices_202), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_400), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 25 27 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_397) then 22 else
  if p.val = (false, vertices_661) then 23 else
  if p.val = (false, vertices_837) then 24 else
  if p.val = (false, vertices_681) then 26 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_416) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 25 => Sum.inl 2
  | 26 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 27 => Sum.inl 3
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 1 3 5 8 598 82 1
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 82 598 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 42 570 2
cert_coverFacet 2 234
cert_cover_5 2 0 0 2 4 5 42 234 3
cert_coverFacet 3 458
cert_cover_5 3 0 0 2 5 7 202 458 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 84 372 2
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coverFacet 9 688
cert_cover_2 9 4 3 6 8 176 688 3
cert_coverFacet 10 480
cert_cover_2 10 5 4 6 7 224 480 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0619

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0620.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0620

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 653, 425, 841, 689, 590, 566, 86, 114, 482, 834, 348, 412, 660, 240, 464, 137, 265, 521, 161, 289, 545, 641, 769, 22, 70, 518, 50, 82, 98, 290, 546, 322, 578, 770, 284, 76, 140, 524, 84, 148, 532, 644, 328, 584, 392, 112, 176, 560, 208, 336, 400, 656, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_653, vertices_425, vertices_841, vertices_689, vertices_590, vertices_566, vertices_86, vertices_114, vertices_482, vertices_834, vertices_348, vertices_412, vertices_660, vertices_240, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_50, vertices_82, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_284, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_644, vertices_328, vertices_584, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_653), (false, vertices_425), (false, vertices_841), (false, vertices_689), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_284), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 23 26 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_841) then 25 else
  if p.val = (false, vertices_689) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_284) then 22 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_224) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 98 3
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 1 2 5 8 590 70 2
cert_row_4 3 0 1 3 4 8 566 22 3
cert_rows
cert_pivot_2 6 7 2 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 70 590 2
cert_coverFacet 1 566
cert_cover_5 1 3 0 1 3 4 22 566 3
cert_coverFacet 2 86
cert_cover_2 2 1 0 3 5 22 86 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 482
cert_cover_5 4 0 0 4 5 6 98 482 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 348
cert_cover_5 6 1 1 2 3 5 284 348 3
cert_coverFacet 7 412
cert_cover_5 7 1 1 2 3 6 284 412 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coverFacet 10 464
cert_cover_2 10 5 3 6 7 208 464 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0620

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0621.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0621

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 665, 425, 841, 118, 602, 562, 482, 834, 348, 412, 564, 660, 228, 452, 137, 265, 521, 161, 289, 545, 641, 769, 50, 82, 530, 98, 290, 546, 322, 578, 770, 284, 52, 84, 148, 532, 100, 164, 548, 196, 324, 388, 644, 88, 152, 536, 328, 584, 392, 560, 656, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_665, vertices_425, vertices_841, vertices_118, vertices_602, vertices_562, vertices_482, vertices_834, vertices_348, vertices_412, vertices_564, vertices_660, vertices_228, vertices_452] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_284, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_88, vertices_152, vertices_536, vertices_328, vertices_584, vertices_392, vertices_560, vertices_656, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_665), (false, vertices_425), (false, vertices_841), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_284), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_88), (true, vertices_560), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 23 27 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (false, vertices_841) then 26 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_284) then 22 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_388) then 13 else
  if p.val = (true, vertices_88) then 14 else
  if p.val = (true, vertices_560) then 15 else
  if p.val = (true, vertices_224) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 27 => Sum.inl 3
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 82 1
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 1 3 4 5 118 50 1
cert_row_4 3 0 4 5 6 7 482 98 3
cert_rows
cert_pivot_2 8 2 1 0
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 50 118 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 82 602 1
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 98 482 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 348
cert_cover_5 5 1 1 2 3 5 284 348 3
cert_coverFacet 6 412
cert_cover_5 6 1 1 2 3 6 284 412 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 228
cert_cover_2 9 4 1 5 6 100 228 3
cert_coverFacet 10 452
cert_cover_2 10 5 1 6 7 196 452 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0621

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0622.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0622

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 665, 425, 841, 118, 566, 602, 482, 834, 412, 340, 660, 228, 452, 344, 137, 265, 521, 161, 289, 545, 641, 769, 54, 82, 530, 98, 290, 546, 322, 578, 770, 84, 148, 276, 532, 100, 164, 548, 196, 324, 388, 644, 88, 152, 280, 536, 328, 584, 392, 336, 656, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_665, vertices_425, vertices_841, vertices_118, vertices_566, vertices_602, vertices_482, vertices_834, vertices_412, vertices_340, vertices_660, vertices_228, vertices_452, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_54, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_584, vertices_392, vertices_336, vertices_656, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_665), (false, vertices_425), (false, vertices_841), (true, vertices_54), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 23 27 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (false, vertices_841) then 26 else
  if p.val = (true, vertices_54) then 20 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_224) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 27 => Sum.inl 3
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 82 1
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_2 2 0 1 3 4 54
cert_row_4 3 1 2 3 6 7 412 148 1
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 5 54 118 3
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 8 54 566 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 82 602 1
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 412
cert_cover_5 5 3 1 2 3 6 148 412 1
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coverFacet 9 452
cert_cover_2 9 5 1 6 7 196 452 3
cert_coverFacet 10 344
cert_cover_2 10 3 2 5 7 88 344 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0622

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0623.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0623

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 597, 617, 241, 913, 302, 558, 790, 482, 898, 92, 412, 588, 216, 360, 456, 81, 145, 529, 97, 161, 545, 577, 641, 46, 262, 518, 162, 290, 546, 386, 642, 770, 28, 76, 268, 524, 84, 276, 532, 580, 88, 152, 104, 296, 552, 200, 328, 584, 392, 208, 400, 784, 224, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_597, vertices_617, vertices_241, vertices_913, vertices_302, vertices_558, vertices_790, vertices_482, vertices_898, vertices_92, vertices_412, vertices_588, vertices_216, vertices_360, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_545, vertices_577, vertices_641, vertices_46, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_88, vertices_152, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_208, vertices_400, vertices_784, vertices_224, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_597), (false, vertices_617), (false, vertices_241), (false, vertices_913), (true, vertices_46), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_88), (true, vertices_152), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 23 25 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_597) then 22 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (false, vertices_913) then 27 else
  if p.val = (true, vertices_46) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_352) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 27 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 262 2
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_2 2 0 1 2 4 46
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 2 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 2 0 1 2 8 46 558 3
cert_coverFacet 2 790
cert_cover_5 2 0 0 1 3 7 262 790 2
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 162 482 2
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coverFacet 10 456
cert_cover_2 10 5 2 6 7 200 456 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0623

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0624.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0624

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 613, 601, 361, 905, 182, 566, 666, 482, 898, 412, 340, 596, 228, 452, 344, 73, 265, 521, 97, 289, 545, 577, 769, 54, 146, 530, 162, 290, 546, 386, 642, 770, 84, 148, 276, 532, 100, 164, 548, 196, 324, 580, 388, 88, 152, 280, 536, 328, 392, 648, 336, 592, 224, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_613, vertices_601, vertices_361, vertices_905, vertices_182, vertices_566, vertices_666, vertices_482, vertices_898, vertices_412, vertices_340, vertices_596, vertices_228, vertices_452, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_54, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_392, vertices_648, vertices_336, vertices_592, vertices_224, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_613), (false, vertices_601), (false, vertices_361), (false, vertices_905), (true, vertices_54), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_336), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 23 27 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (false, vertices_905) then 26 else
  if p.val = (true, vertices_54) then 20 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_224) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 27 => Sum.inl 3
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_2 2 0 1 3 4 54
cert_row_4 3 1 2 3 6 7 412 148 1
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 2 0 1 3 6 54 182 3
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 8 54 566 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 146 666 1
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 162 482 2
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 412
cert_cover_5 5 3 1 2 3 6 148 412 1
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coverFacet 9 452
cert_cover_2 9 5 1 6 7 196 452 3
cert_coverFacet 10 344
cert_cover_2 10 3 2 5 7 88 344 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0624

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0625.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0625

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 789, 809, 433, 721, 110, 558, 598, 482, 706, 92, 412, 780, 216, 360, 456, 145, 273, 529, 161, 289, 545, 641, 769, 46, 70, 518, 98, 162, 546, 194, 578, 642, 28, 76, 268, 524, 84, 276, 532, 772, 88, 152, 104, 296, 552, 200, 328, 392, 776, 208, 592, 400, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_789, vertices_809, vertices_433, vertices_721, vertices_110, vertices_558, vertices_598, vertices_482, vertices_706, vertices_92, vertices_412, vertices_780, vertices_216, vertices_360, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_46, vertices_70, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_88, vertices_152, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_208, vertices_592, vertices_400, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_789), (false, vertices_809), (false, vertices_433), (false, vertices_721), (true, vertices_46), (true, vertices_70), (true, vertices_518), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 23 25 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (false, vertices_721) then 27 else
  if p.val = (true, vertices_46) then 20 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_352) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_2 2 0 1 2 4 46
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 2 0 1 2 5 46 110 3
cert_coverFacet 1 558
cert_cover_5 1 2 0 1 2 8 46 558 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 70 598 2
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coverFacet 10 456
cert_cover_2 10 5 2 6 7 200 456 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0625

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0626.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0626

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 339, 707, 653, 233, 361, 790, 626, 396, 780, 180, 564, 404, 740, 440, 368, 67, 259, 515, 105, 137, 265, 521, 193, 321, 641, 82, 274, 530, 578, 770, 140, 268, 524, 52, 148, 276, 532, 164, 548, 388, 644, 772, 168, 296, 392, 776, 112, 176, 304, 560, 336, 400, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_339, vertices_707, vertices_653, vertices_233, vertices_361, vertices_790, vertices_626, vertices_396, vertices_780, vertices_180, vertices_564, vertices_404, vertices_740, vertices_440, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_105, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_168, vertices_296, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_400, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_339), (false, vertices_707), (false, vertices_653), (false, vertices_233), (false, vertices_361), (true, vertices_530), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_388), (true, vertices_772), (true, vertices_392), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_339) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_653) then 22 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_608) then 16 else
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
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 2 3 4 6 7 440 168 1
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
cert_coverFacet 2 396
cert_cover_2 2 2 1 6 7 140 396 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 164 740 2
cert_coverFacet 8 440
cert_cover_5 8 0 2 3 4 6 168 440 1
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0626

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0627.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0627

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 611, 451, 565, 121, 345, 902, 714, 620, 172, 652, 436, 788, 184, 408, 456, 67, 259, 515, 89, 49, 273, 529, 97, 545, 321, 194, 578, 386, 642, 770, 44, 140, 524, 52, 276, 532, 164, 548, 388, 644, 772, 56, 152, 280, 104, 168, 200, 328, 584, 392, 648, 176, 400, 784, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_611, vertices_451, vertices_565, vertices_121, vertices_345, vertices_902, vertices_714, vertices_620, vertices_172, vertices_652, vertices_436, vertices_788, vertices_184, vertices_408, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_89, vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_176, vertices_400, vertices_784, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_611), (false, vertices_451), (false, vertices_565), (false, vertices_121), (false, vertices_345), (true, vertices_642), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_276), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_121) then 24 else
  if p.val = (false, vertices_345) then 25 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
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
cert_row_4 0 1 3 4 6 7 436 52 3
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 194 714 1
cert_coverFacet 2 620
cert_cover_5 2 3 1 2 4 5 44 620 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 436
cert_cover_5 5 0 1 3 4 6 52 436 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0627

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0628.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0628

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 709, 681, 849, 481, 94, 654, 310, 774, 58, 554, 204, 596, 788, 440, 472, 161, 289, 545, 193, 321, 577, 641, 769, 14, 22, 262, 518, 26, 42, 522, 50, 290, 546, 770, 76, 140, 84, 276, 532, 196, 580, 644, 772, 56, 88, 408, 168, 552, 200, 648, 304, 336, 592, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_709, vertices_681, vertices_849, vertices_481, vertices_94, vertices_654, vertices_310, vertices_774, vertices_58, vertices_554, vertices_204, vertices_596, vertices_788, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_50, vertices_290, vertices_546, vertices_770, vertices_76, vertices_140, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_408, vertices_168, vertices_552, vertices_200, vertices_648, vertices_304, vertices_336, vertices_592, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_709), (false, vertices_681), (false, vertices_849), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_76), (true, vertices_140), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_200), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 22 25 27 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (false, vertices_481) then 28 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_50) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_56) then 14 else
  if p.val = (true, vertices_88) then 15 else
  if p.val = (true, vertices_408) then 24 else
  if p.val = (true, vertices_200) then 16 else
  if p.val = (true, vertices_304) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 5 94 14 3
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_2 2 2 3 6 7 408
cert_row_4 3 0 1 3 4 7 310 22 3
cert_rows
cert_pivot_2 5 8 2 0
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 654
cert_cover_5 1 1 0 1 2 6 14 654 3
cert_coverFacet 2 310
cert_cover_5 2 3 0 1 3 4 22 310 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 58
cert_cover_2 4 2 0 3 4 26 58 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coverFacet 9 440
cert_cover_5 9 2 2 3 4 6 56 440 3
cert_coverFacet 10 472
cert_cover_5 10 2 2 3 5 6 88 472 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0628

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0629.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0629

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 539, 147, 835, 217, 617, 449, 182, 310, 786, 236, 612, 804, 964, 184, 824, 19, 131, 259, 515, 25, 73, 521, 145, 193, 321, 577, 385, 54, 134, 262, 146, 274, 530, 770, 100, 164, 292, 548, 196, 580, 388, 772, 56, 152, 536, 104, 168, 552, 200, 176, 304, 784, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_539, vertices_147, vertices_835, vertices_217, vertices_617, vertices_449, vertices_182, vertices_310, vertices_786, vertices_236, vertices_612, vertices_804, vertices_964, vertices_184, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_25, vertices_73, vertices_521, vertices_145, vertices_193, vertices_321, vertices_577, vertices_385, vertices_54, vertices_134, vertices_262, vertices_146, vertices_274, vertices_530, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_176, vertices_304, vertices_784, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_539), (false, vertices_147), (false, vertices_835), (false, vertices_217), (false, vertices_617), (false, vertices_449), (true, vertices_54), (true, vertices_274), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_772), (true, vertices_56), (true, vertices_168), (true, vertices_176), (true, vertices_304), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_539) then 20 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_835) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 1 147 0 449 274 100 164 292 548 196 580 772 56 168 176 304 784 800 391 54 539 835 217 617
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_4 2 1 2 4 5 6 236 100 1
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 7 54 310 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 100 236 1
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 964
cert_cover_5 6 3 1 5 6 7 196 964 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 824
cert_cover_5 8 1 2 3 4 7 56 824 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0629

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0630.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0630

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 595, 275, 405, 645, 713, 241, 810, 434, 562, 364, 204, 652, 780, 484, 632, 19, 259, 515, 133, 261, 517, 81, 145, 273, 193, 577, 641, 50, 274, 530, 290, 546, 770, 76, 140, 268, 524, 356, 196, 388, 644, 772, 104, 296, 552, 200, 584, 648, 776, 112, 176, 560, 592, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_595, vertices_275, vertices_405, vertices_645, vertices_713, vertices_241, vertices_810, vertices_434, vertices_562, vertices_364, vertices_204, vertices_652, vertices_780, vertices_484, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_193, vertices_577, vertices_641, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_356, vertices_196, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_552, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_176, vertices_560, vertices_592, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_595), (false, vertices_275), (false, vertices_405), (false, vertices_645), (false, vertices_713), (false, vertices_241), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_356), (true, vertices_196), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_356) then 21 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 275 1 645 50 290 546 76 140 268 524 196 104 296 552 776 560 416 775 595 405 356 713 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 3 4 6 7 434 50 3
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 2 0 2 4 7 290 810 1
cert_coverFacet 1 434
cert_cover_5 1 1 0 3 4 6 50 434 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 364
cert_cover_5 3 0 1 2 4 5 76 364 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 484
cert_cover_5 7 0 1 4 5 6 356 484 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 104 632 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0630

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0631.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0631

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 611, 195, 771, 805, 217, 369, 902, 714, 60, 604, 428, 652, 628, 312, 408, 67, 131, 259, 515, 81, 145, 273, 97, 289, 545, 193, 769, 194, 578, 386, 642, 770, 28, 44, 140, 524, 52, 596, 292, 548, 388, 644, 772, 56, 88, 152, 280, 296, 200, 584, 392, 648, 112, 304, 400, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_611, vertices_195, vertices_771, vertices_805, vertices_217, vertices_369, vertices_902, vertices_714, vertices_60, vertices_604, vertices_428, vertices_652, vertices_628, vertices_312, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_769, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_52, vertices_596, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_400, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_611), (false, vertices_195), (false, vertices_771), (false, vertices_805), (false, vertices_217), (false, vertices_369), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_596), (true, vertices_388), (true, vertices_644), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_584), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_596) then 21 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_648) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 195 1 771 642 28 44 140 524 52 388 644 56 280 296 584 392 648 403 611 805 596 217 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 194 714 1
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 28 604 3
cert_coverFacet 4 428
cert_cover_5 4 3 1 2 4 6 44 428 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 628
cert_cover_5 6 0 1 3 4 5 52 628 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0631

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0632.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0632

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 837, 681, 817, 481, 590, 346, 154, 650, 434, 450, 188, 348, 556, 564, 788, 161, 289, 545, 193, 321, 577, 641, 769, 26, 74, 138, 522, 146, 274, 194, 322, 578, 386, 642, 28, 44, 76, 524, 52, 276, 532, 548, 324, 580, 772, 344, 152, 168, 552, 648, 176, 304, 560, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_837, vertices_681, vertices_817, vertices_481, vertices_590, vertices_346, vertices_154, vertices_650, vertices_434, vertices_450, vertices_188, vertices_348, vertices_556, vertices_564, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_26, vertices_74, vertices_138, vertices_522, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_276, vertices_532, vertices_548, vertices_324, vertices_580, vertices_772, vertices_344, vertices_152, vertices_168, vertices_552, vertices_648, vertices_176, vertices_304, vertices_560, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_837), (false, vertices_681), (false, vertices_817), (false, vertices_481), (true, vertices_26), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_386), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_344), (true, vertices_152), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 22 25 27 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_817) then 26 else
  if p.val = (false, vertices_481) then 28 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_52) then 12 else
  if p.val = (true, vertices_276) then 13 else
  if p.val = (true, vertices_532) then 14 else
  if p.val = (true, vertices_548) then 15 else
  if p.val = (true, vertices_344) then 24 else
  if p.val = (true, vertices_152) then 16 else
  if p.val = (true, vertices_176) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 74 1
cert_row_2 1 2 3 5 7 344
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 1 2 3 4 6 188 28 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 74 590 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 26 346 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 146 434 2
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 188
cert_cover_5 6 3 1 2 3 4 28 188 3
cert_coverFacet 7 348
cert_cover_5 7 1 1 2 3 5 28 348 3
cert_coverFacet 8 556
cert_cover_2 8 2 1 4 8 44 556 3
cert_coverFacet 9 564
cert_cover_2 9 3 1 4 8 52 564 3
cert_coverFacet 10 788
cert_cover_2 10 3 1 7 8 276 788 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0632

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0633.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0633

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 709, 665, 809, 457, 598, 570, 114, 482, 802, 316, 412, 116, 660, 228, 420, 137, 265, 521, 193, 321, 577, 641, 769, 50, 82, 530, 98, 290, 546, 322, 578, 770, 284, 52, 84, 148, 532, 100, 164, 292, 196, 580, 388, 644, 56, 152, 536, 296, 552, 392, 112, 656, 224, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_709, vertices_665, vertices_809, vertices_457, vertices_598, vertices_570, vertices_114, vertices_482, vertices_802, vertices_316, vertices_412, vertices_116, vertices_660, vertices_228, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_284, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_292, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_152, vertices_536, vertices_296, vertices_552, vertices_392, vertices_112, vertices_656, vertices_224, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_709), (false, vertices_665), (false, vertices_809), (false, vertices_457), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_284), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_56), (true, vertices_112), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 23 27 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_809) then 25 else
  if p.val = (false, vertices_457) then 26 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_284) then 22 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_388) then 13 else
  if p.val = (true, vertices_56) then 14 else
  if p.val = (true, vertices_112) then 15 else
  if p.val = (true, vertices_224) then 16 else
  if p.val = (true, vertices_416) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 27 => Sum.inl 3
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 98 3
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 1 3 5 8 598 82 1
cert_row_4 3 0 2 3 4 8 570 50 1
cert_rows
cert_pivot_2 6 7 1 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 82 598 1
cert_coverFacet 1 570
cert_cover_5 1 3 0 2 3 4 50 570 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 482
cert_cover_5 3 0 0 4 5 6 98 482 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 4 284 316 3
cert_coverFacet 6 412
cert_cover_5 6 1 1 2 3 6 284 412 3
cert_coverFacet 7 116
cert_cover_2 7 3 1 4 5 52 116 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 228
cert_cover_2 9 4 1 5 6 100 228 3
cert_coverFacet 10 420
cert_cover_2 10 4 1 6 7 164 420 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0633

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0634.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0634

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 589, 361, 905, 625, 654, 182, 534, 562, 482, 898, 348, 412, 596, 240, 464, 73, 265, 521, 97, 289, 545, 577, 769, 22, 134, 518, 50, 530, 162, 290, 546, 386, 642, 770, 284, 76, 140, 524, 84, 148, 532, 580, 328, 392, 648, 112, 176, 560, 208, 336, 592, 400, 224, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_589, vertices_361, vertices_905, vertices_625, vertices_654, vertices_182, vertices_534, vertices_562, vertices_482, vertices_898, vertices_348, vertices_412, vertices_596, vertices_240, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_22, vertices_134, vertices_518, vertices_50, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_284, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_580, vertices_328, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_589), (false, vertices_361), (false, vertices_905), (false, vertices_625), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_284), (true, vertices_140), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_176), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 23 26 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_905) then 25 else
  if p.val = (false, vertices_625) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_284) then 22 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_224) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 1 3 4 6 182 22 3
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 8 2 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 182
cert_cover_5 1 2 0 1 3 4 22 182 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 162 482 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 348
cert_cover_5 6 1 1 2 3 5 284 348 3
cert_coverFacet 7 412
cert_cover_5 7 1 1 2 3 6 284 412 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coverFacet 10 464
cert_cover_2 10 5 3 6 7 208 464 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0634

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0635.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0635

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 275, 451, 557, 613, 169, 713, 433, 598, 906, 786, 706, 796, 428, 116, 308, 19, 67, 259, 549, 41, 137, 521, 49, 273, 97, 161, 193, 577, 385, 82, 274, 530, 194, 578, 386, 642, 770, 44, 268, 524, 52, 84, 276, 532, 100, 292, 580, 168, 392, 648, 776, 112, 304, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_275, vertices_451, vertices_557, vertices_613, vertices_169, vertices_713, vertices_433, vertices_598, vertices_906, vertices_786, vertices_706, vertices_796, vertices_428, vertices_116, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_549, vertices_41, vertices_137, vertices_521, vertices_49, vertices_273, vertices_97, vertices_161, vertices_193, vertices_577, vertices_385, vertices_82, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_580, vertices_168, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_275), (false, vertices_451), (false, vertices_557), (false, vertices_613), (false, vertices_169), (false, vertices_713), (false, vertices_433), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_392), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 5 0 3 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 386 906 1
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 796
cert_cover_5 4 2 1 2 3 7 268 796 2
cert_coverFacet 5 428
cert_cover_5 5 3 1 2 4 6 44 428 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0635

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0636.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0636

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 595, 675, 323, 173, 553, 841, 342, 402, 658, 412, 812, 116, 180, 868, 752, 67, 131, 259, 515, 41, 137, 265, 521, 161, 545, 321, 577, 82, 146, 274, 530, 322, 386, 642, 44, 140, 268, 52, 84, 148, 276, 100, 164, 804, 324, 552, 392, 776, 112, 176, 592, 400, 656, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_595, vertices_675, vertices_323, vertices_173, vertices_553, vertices_841, vertices_342, vertices_402, vertices_658, vertices_412, vertices_812, vertices_116, vertices_180, vertices_868, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_41, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_321, vertices_577, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_386, vertices_642, vertices_44, vertices_140, vertices_268, vertices_52, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_804, vertices_324, vertices_552, vertices_392, vertices_776, vertices_112, vertices_176, vertices_592, vertices_400, vertices_656, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_595), (false, vertices_675), (false, vertices_323), (false, vertices_173), (false, vertices_553), (false, vertices_841), (true, vertices_146), (true, vertices_274), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_804), (true, vertices_324), (true, vertices_112), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_173) then 21 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_804) then 22 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 323 553 146 274 268 52 84 148 276 100 324 112 176 400 656 608 395 595 675 173 804 841
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 82 1
cert_row_4 1 1 2 3 6 7 412 140 2
cert_row_2 2 1 4 7 8 804
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 82 342 1
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 412
cert_cover_5 3 1 1 2 3 6 140 412 2
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 44 812 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 868
cert_cover_5 7 2 1 4 5 7 100 868 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0636

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0637.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0637

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 651, 787, 569, 345, 457, 230, 582, 774, 706, 620, 820, 420, 120, 712, 496, 131, 259, 515, 25, 329, 137, 521, 273, 529, 385, 70, 134, 262, 518, 194, 578, 642, 770, 100, 164, 292, 548, 580, 388, 772, 56, 88, 104, 552, 200, 584, 648, 112, 304, 560, 336, 784, 224, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_651, vertices_787, vertices_569, vertices_345, vertices_457, vertices_230, vertices_582, vertices_774, vertices_706, vertices_620, vertices_820, vertices_420, vertices_120, vertices_712, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_25, vertices_329, vertices_137, vertices_521, vertices_273, vertices_529, vertices_385, vertices_70, vertices_134, vertices_262, vertices_518, vertices_194, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_224, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_651), (false, vertices_787), (false, vertices_569), (false, vertices_345), (false, vertices_457), (true, vertices_70), (true, vertices_518), (true, vertices_194), (true, vertices_578), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_104), (true, vertices_584), (true, vertices_112), (true, vertices_304), (true, vertices_224), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_787) then 20 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 6 230 70 2
cert_row_4 1 1 2 4 5 8 620 100 1
cert_row_4 2 1 3 4 7 8 820 292 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 5 70 230 2
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 620
cert_cover_5 4 1 1 2 4 5 100 620 1
cert_coverFacet 5 820
cert_cover_5 5 2 1 3 4 7 292 820 1
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0637

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0638.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0638

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 787, 675, 195, 569, 305, 481, 206, 646, 774, 684, 588, 852, 440, 472, 600, 67, 131, 259, 515, 49, 273, 529, 161, 289, 545, 193, 321, 70, 134, 262, 518, 194, 642, 770, 76, 140, 524, 324, 580, 644, 772, 56, 88, 408, 536, 168, 552, 200, 584, 304, 336, 592, 784, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_787, vertices_675, vertices_195, vertices_569, vertices_305, vertices_481, vertices_206, vertices_646, vertices_774, vertices_684, vertices_588, vertices_852, vertices_440, vertices_472, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_70, vertices_134, vertices_262, vertices_518, vertices_194, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_408, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_304, vertices_336, vertices_592, vertices_784, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_787), (false, vertices_675), (false, vertices_195), (false, vertices_569), (false, vertices_305), (false, vertices_481), (true, vertices_134), (true, vertices_518), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_580), (true, vertices_644), (true, vertices_772), (true, vertices_88), (true, vertices_408), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 21 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 17 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 6 206 70 2
cert_row_4 1 1 2 4 6 8 684 140 2
cert_row_2 2 2 3 6 7 408
cert_row_4 3 1 3 5 7 8 852 324 1
cert_rows
cert_pivot_2 0 4 2 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 70 206 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 140 684 2
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 852
cert_cover_5 5 3 1 3 5 7 324 852 1
cert_coverFacet 6 440
cert_cover_5 6 2 2 3 4 6 56 440 3
cert_coverFacet 7 472
cert_cover_5 7 2 2 3 5 6 88 472 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0638

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0639.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0639

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 781, 309, 661, 345, 721, 806, 234, 394, 778, 434, 610, 180, 740, 216, 408, 21, 261, 517, 73, 265, 521, 81, 657, 273, 577, 74, 138, 266, 522, 98, 162, 290, 546, 578, 386, 770, 52, 148, 164, 292, 548, 644, 772, 88, 152, 280, 200, 392, 776, 176, 304, 208, 400, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_781, vertices_309, vertices_661, vertices_345, vertices_721, vertices_806, vertices_234, vertices_394, vertices_778, vertices_434, vertices_610, vertices_180, vertices_740, vertices_216, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_657, vertices_273, vertices_577, vertices_74, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_578, vertices_386, vertices_770, vertices_52, vertices_148, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_781), (false, vertices_309), (false, vertices_661), (false, vertices_345), (false, vertices_721), (true, vertices_138), (true, vertices_266), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_770), (true, vertices_164), (true, vertices_548), (true, vertices_152), (true, vertices_200), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_661) then 25 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 6 234 74 2
cert_row_4 1 0 3 4 6 7 434 162 1
cert_row_4 2 0 1 4 7 8 806 290 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 290 806 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 5 74 234 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 434
cert_cover_5 4 1 0 3 4 6 162 434 1
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 164 740 2
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0639

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0640.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0640

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 787, 611, 713, 913, 481, 558, 662, 278, 220, 284, 300, 652, 376, 616, 464, 35, 259, 515, 785, 97, 289, 193, 577, 385, 641, 22, 38, 262, 518, 274, 530, 546, 28, 44, 140, 268, 524, 148, 276, 292, 644, 88, 280, 104, 296, 552, 200, 584, 648, 208, 336, 400, 656, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_787, vertices_611, vertices_713, vertices_913, vertices_481, vertices_558, vertices_662, vertices_278, vertices_220, vertices_284, vertices_300, vertices_652, vertices_376, vertices_616, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_785, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_22, vertices_38, vertices_262, vertices_518, vertices_274, vertices_530, vertices_546, vertices_28, vertices_44, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_292, vertices_644, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_787), (false, vertices_611), (false, vertices_713), (false, vertices_913), (false, vertices_481), (true, vertices_22), (true, vertices_518), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_644), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 21 23 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 18 else
  if p.val = (false, vertices_787) then 24 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_913) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 7 376 88 2
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 2 3 5 6 220 28 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 220
cert_cover_5 3 3 1 2 3 5 28 220 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 376
cert_cover_5 7 0 2 3 4 5 88 376 2
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0640

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0641.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0641

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 787, 355, 653, 421, 913, 618, 722, 338, 220, 284, 300, 556, 404, 376, 712, 35, 259, 515, 37, 133, 517, 785, 289, 385, 641, 82, 274, 530, 98, 546, 322, 578, 28, 44, 140, 268, 524, 148, 276, 292, 548, 388, 88, 280, 104, 296, 552, 200, 584, 648, 208, 336, 400, 656, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_787, vertices_355, vertices_653, vertices_421, vertices_913, vertices_618, vertices_722, vertices_338, vertices_220, vertices_284, vertices_300, vertices_556, vertices_404, vertices_376, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_37, vertices_133, vertices_517, vertices_785, vertices_289, vertices_385, vertices_641, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_28, vertices_44, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_292, vertices_548, vertices_388, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_787), (false, vertices_355), (false, vertices_653), (false, vertices_421), (false, vertices_913), (true, vertices_82), (true, vertices_578), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_208), (true, vertices_336), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_787) then 25 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_913) then 26 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 6 220 28 3
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_5 0 2 0 2 4 5 98 618 1
cert_coverFacet 1 722
cert_cover_5 1 1 0 3 5 6 82 722 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 28 220 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 88 376 2
cert_coverFacet 9 712
cert_cover_2 9 5 2 6 8 200 712 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0641

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0642.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0642

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 285, 661, 837, 369, 689, 782, 234, 554, 394, 466, 834, 156, 684, 408, 240, 21, 261, 517, 49, 657, 273, 97, 545, 321, 577, 42, 138, 266, 522, 98, 546, 194, 322, 578, 386, 770, 28, 140, 268, 524, 148, 644, 772, 152, 280, 168, 552, 392, 112, 176, 208, 336, 400, 224, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_285, vertices_661, vertices_837, vertices_369, vertices_689, vertices_782, vertices_234, vertices_554, vertices_394, vertices_466, vertices_834, vertices_156, vertices_684, vertices_408, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_49, vertices_657, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_42, vertices_138, vertices_266, vertices_522, vertices_98, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_644, vertices_772, vertices_152, vertices_280, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_285), (false, vertices_661), (false, vertices_837), (false, vertices_369), (false, vertices_689), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_524), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
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
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
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
cert_row_4 0 0 3 5 6 7 466 194 1
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 4 5 6 234 42 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 234
cert_cover_5 1 2 0 2 4 5 42 234 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 6 194 466 1
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 684
cert_cover_5 7 3 1 2 4 6 140 684 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0642

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0643.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0643

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 563, 147, 405, 357, 549, 313, 218, 602, 962, 620, 836, 900, 568, 408, 488, 19, 131, 515, 37, 133, 261, 517, 49, 145, 273, 289, 545, 90, 146, 530, 194, 578, 642, 100, 548, 324, 580, 388, 644, 772, 56, 152, 280, 536, 104, 296, 552, 200, 584, 392, 560, 400, 352, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_563, vertices_147, vertices_405, vertices_357, vertices_549, vertices_313, vertices_218, vertices_602, vertices_962, vertices_620, vertices_836, vertices_900, vertices_568, vertices_408, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_37, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_289, vertices_545, vertices_90, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_100, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_560, vertices_400, vertices_352, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_563), (false, vertices_147), (false, vertices_405), (false, vertices_357), (false, vertices_549), (false, vertices_313), (true, vertices_90), (true, vertices_194), (true, vertices_578), (true, vertices_580), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_313) then 24 else
  if p.val = (true, vertices_90) then 19 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_832) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 0 0 2 3 6 90 218 3
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 8 90 602 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 100 620 1
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0643

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0644.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0644

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 541, 173, 613, 345, 361, 902, 794, 210, 402, 738, 396, 780, 676, 424, 496, 13, 37, 517, 25, 41, 329, 81, 529, 97, 577, 82, 146, 274, 530, 194, 578, 386, 642, 770, 140, 268, 524, 164, 548, 388, 644, 772, 280, 536, 168, 296, 392, 776, 208, 336, 400, 224, 352, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_541, vertices_173, vertices_613, vertices_345, vertices_361, vertices_902, vertices_794, vertices_210, vertices_402, vertices_738, vertices_396, vertices_780, vertices_676, vertices_424, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_25, vertices_41, vertices_329, vertices_81, vertices_529, vertices_97, vertices_577, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_541), (false, vertices_173), (false, vertices_613), (false, vertices_345), (false, vertices_361), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_173) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 208 496 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0644

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0645.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0645

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 837, 313, 177, 721, 929, 206, 526, 326, 774, 218, 282, 810, 188, 556, 740, 49, 81, 145, 273, 161, 289, 321, 577, 641, 769, 14, 70, 262, 518, 26, 202, 266, 522, 82, 274, 322, 770, 44, 140, 524, 164, 548, 196, 324, 580, 772, 56, 152, 280, 296, 552, 176, 208, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_837, vertices_313, vertices_177, vertices_721, vertices_929, vertices_206, vertices_526, vertices_326, vertices_774, vertices_218, vertices_282, vertices_810, vertices_188, vertices_556, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_145, vertices_273, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_26, vertices_202, vertices_266, vertices_522, vertices_82, vertices_274, vertices_322, vertices_770, vertices_44, vertices_140, vertices_524, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_296, vertices_552, vertices_176, vertices_208, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_837), (false, vertices_313), (false, vertices_177), (false, vertices_721), (false, vertices_929), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_770), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_152), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_196) then 14 else
  if p.val = (true, vertices_152) then 15 else
  if p.val = (true, vertices_552) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 177 14 70 262 518 26 266 522 770 44 140 524 164 548 196 152 552 339 202 837 313 721 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_2 1 0 2 5 6 202
cert_row_4 2 1 2 3 4 6 188 44 2
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 218
cert_cover_5 4 1 0 2 3 5 26 218 3
cert_coverFacet 5 282
cert_cover_2 5 2 0 3 7 26 282 3
cert_coverFacet 6 810
cert_cover_5 6 0 0 2 4 7 266 810 2
cert_coverFacet 7 188
cert_cover_5 7 2 1 2 3 4 44 188 2
cert_coverFacet 8 556
cert_cover_2 8 2 1 4 8 44 556 3
cert_coverFacet 9 740
cert_cover_5 9 3 1 4 5 6 164 740 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0645

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0646.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0646

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 213, 421, 837, 297, 777, 737, 790, 218, 282, 234, 778, 626, 412, 596, 424, 69, 133, 261, 41, 265, 521, 161, 289, 545, 193, 577, 769, 26, 42, 202, 266, 522, 82, 274, 530, 98, 546, 770, 84, 148, 276, 532, 580, 388, 772, 152, 280, 168, 296, 392, 776, 208, 592, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_213, vertices_421, vertices_837, vertices_297, vertices_777, vertices_737, vertices_790, vertices_218, vertices_282, vertices_234, vertices_778, vertices_626, vertices_412, vertices_596, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_41, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_26, vertices_42, vertices_202, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_580, vertices_388, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_776, vertices_208, vertices_592, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_213), (false, vertices_421), (false, vertices_837), (false, vertices_297), (false, vertices_777), (false, vertices_737), (true, vertices_26), (true, vertices_202), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_770), (true, vertices_276), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 82 2
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 2 3 6 7 412 148 1
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 26 218 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 5 42 234 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 626
cert_cover_5 5 0 0 3 4 5 82 626 2
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 148 412 1
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0646

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0647.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0647

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 357, 165, 709, 185, 281, 457, 806, 218, 282, 586, 778, 562, 722, 844, 692, 37, 69, 133, 25, 137, 265, 49, 273, 161, 289, 193, 321, 26, 74, 266, 522, 50, 210, 274, 530, 290, 546, 578, 770, 164, 292, 548, 324, 580, 644, 772, 152, 280, 200, 328, 584, 776, 176, 560, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_357, vertices_165, vertices_709, vertices_185, vertices_281, vertices_457, vertices_806, vertices_218, vertices_282, vertices_586, vertices_778, vertices_562, vertices_722, vertices_844, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_25, vertices_137, vertices_265, vertices_49, vertices_273, vertices_161, vertices_289, vertices_193, vertices_321, vertices_26, vertices_74, vertices_266, vertices_522, vertices_50, vertices_210, vertices_274, vertices_530, vertices_290, vertices_546, vertices_578, vertices_770, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_357), (false, vertices_165), (false, vertices_709), (false, vertices_185), (false, vertices_281), (false, vertices_457), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_210), (true, vertices_530), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_548), (true, vertices_772), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_210) then 18 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 165 1 281 26 74 266 522 530 546 578 770 548 772 584 776 560 656 307 210 357 709 185 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 7 8 844 324 1
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 4 7 8 806 290 1
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 290 806 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 26 218 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 562
cert_cover_2 5 3 0 4 8 50 562 3
cert_coverFacet 6 722
cert_cover_5 6 1 0 3 5 8 210 722 3
cert_coverFacet 7 844
cert_cover_5 7 0 1 2 5 7 324 844 1
cert_coverFacet 8 692
cert_cover_5 8 3 1 3 4 6 164 692 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0647

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0648.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0648

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 285, 661, 421, 537, 297, 737, 342, 282, 538, 234, 458, 626, 596, 964, 424, 21, 133, 261, 25, 41, 265, 521, 529, 161, 289, 545, 641, 26, 42, 202, 266, 522, 82, 274, 530, 98, 546, 322, 84, 276, 532, 324, 580, 388, 644, 280, 536, 168, 296, 392, 592, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_285, vertices_661, vertices_421, vertices_537, vertices_297, vertices_737, vertices_342, vertices_282, vertices_538, vertices_234, vertices_458, vertices_626, vertices_596, vertices_964, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_25, vertices_41, vertices_265, vertices_521, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_26, vertices_42, vertices_202, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_592, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_285), (false, vertices_661), (false, vertices_421), (false, vertices_537), (false, vertices_297), (false, vertices_737), (true, vertices_26), (true, vertices_202), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_84), (true, vertices_324), (true, vertices_580), (true, vertices_168), (true, vertices_392), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 0 1 3 5 7 342 82 1
cert_row_4 3 1 5 6 7 8 964 324 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 2 0 1 3 5 82 342 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 5 42 234 3
cert_coverFacet 4 458
cert_cover_5 4 0 0 2 5 7 202 458 3
cert_coverFacet 5 626
cert_cover_5 5 1 0 3 4 5 82 626 2
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 964
cert_cover_5 7 3 1 5 6 7 324 964 2
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0648

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4503 : Certifies 4503 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0619.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4504 : Certifies 4504 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0620.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4505 : Certifies 4505 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0621.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4506 : Certifies 4506 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0622.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4507 : Certifies 4507 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0623.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4508 : Certifies 4508 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0624.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4509 : Certifies 4509 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0625.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4510 : Certifies 4510 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0626.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4511 : Certifies 4511 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0627.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4512 : Certifies 4512 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0628.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4513 : Certifies 4513 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0629.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4514 : Certifies 4514 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0630.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4515 : Certifies 4515 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0631.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4516 : Certifies 4516 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0632.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4517 : Certifies 4517 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0633.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4518 : Certifies 4518 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0634.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4519 : Certifies 4519 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0635.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4520 : Certifies 4520 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0636.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4521 : Certifies 4521 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0637.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4522 : Certifies 4522 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0638.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4523 : Certifies 4523 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0639.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4524 : Certifies 4524 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0640.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4525 : Certifies 4525 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0641.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4526 : Certifies 4526 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0642.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4527 : Certifies 4527 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0643.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4528 : Certifies 4528 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0644.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4529 : Certifies 4529 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0645.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4530 : Certifies 4530 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0646.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4531 : Certifies 4531 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0647.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4532 : Certifies 4532 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0648.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B149 (j : Fin 30) :
    Certifies (4503 + j.val) := by
  fin_cases j
  · exact projection_4503
  · exact projection_4504
  · exact projection_4505
  · exact projection_4506
  · exact projection_4507
  · exact projection_4508
  · exact projection_4509
  · exact projection_4510
  · exact projection_4511
  · exact projection_4512
  · exact projection_4513
  · exact projection_4514
  · exact projection_4515
  · exact projection_4516
  · exact projection_4517
  · exact projection_4518
  · exact projection_4519
  · exact projection_4520
  · exact projection_4521
  · exact projection_4522
  · exact projection_4523
  · exact projection_4524
  · exact projection_4525
  · exact projection_4526
  · exact projection_4527
  · exact projection_4528
  · exact projection_4529
  · exact projection_4530
  · exact projection_4531
  · exact projection_4532

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
