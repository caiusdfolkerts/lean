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
/- Source: ProjectionCertificates/R_one_six_1339.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1339

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 465, 897, 590, 684, 376, 808, 840, 944, 7, 27, 67, 515, 53, 133, 81, 145, 321, 385, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 296, 552, 328, 584, 776, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_465, vertices_897, vertices_590, vertices_684, vertices_376, vertices_808, vertices_840, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (false, vertices_897), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 897 1 524 296 552 328 584 776 304 672 800 647 181 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 376
cert_cover_5 2 2 2 3 4 5 56 376 3
cert_coverFacet 3 808
cert_cover_2 3 4 2 7 8 296 808 3
cert_coverFacet 4 840
cert_cover_2 4 5 2 7 8 328 840 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1339

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1340.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1340

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 465, 897, 590, 684, 376, 616, 944, 864, 7, 27, 67, 515, 53, 133, 81, 145, 321, 385, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 104, 552, 584, 176, 304, 336, 400, 352, 608, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_465, vertices_897, vertices_590, vertices_684, vertices_376, vertices_616, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (false, vertices_897), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 897 1 524 104 552 584 304 352 608 672 800 647 181 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 376
cert_cover_5 2 2 2 3 4 5 56 376 3
cert_coverFacet 3 616
cert_cover_2 3 4 2 5 8 104 616 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1340

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1341.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1341

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 465, 897, 590, 684, 120, 872, 368, 944, 7, 27, 67, 515, 53, 133, 81, 145, 321, 385, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 104, 552, 584, 112, 176, 304, 336, 400, 352, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_465, vertices_897, vertices_590, vertices_684, vertices_120, vertices_872, vertices_368, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (false, vertices_897), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_112), (true, vertices_304), (true, vertices_352), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 897 1 524 104 552 584 112 304 352 672 800 647 181 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 120
cert_cover_2 2 3 2 4 5 56 120 3
cert_coverFacet 3 872
cert_cover_5 3 2 2 4 5 7 104 872 3
cert_coverFacet 4 368
cert_cover_2 4 4 3 5 7 112 368 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1341

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1342.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1342

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 465, 897, 590, 684, 312, 344, 872, 944, 7, 27, 67, 515, 53, 133, 81, 145, 321, 385, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 280, 296, 552, 328, 584, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_465, vertices_897, vertices_590, vertices_684, vertices_312, vertices_344, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (false, vertices_897), (true, vertices_524), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 897 1 524 280 296 552 328 584 304 672 800 647 181 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 4 5 7 8 872 296 2
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 312
cert_cover_2 2 3 2 4 7 56 312 3
cert_coverFacet 3 344
cert_cover_2 3 3 2 5 7 88 344 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 296 872 2
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1342

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1343.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1343

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 465, 897, 590, 108, 868, 676, 376, 944, 7, 27, 67, 515, 53, 133, 81, 145, 321, 385, 641, 769, 14, 518, 74, 578, 44, 76, 100, 164, 548, 580, 644, 56, 88, 104, 176, 304, 336, 400, 352, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_465, vertices_897, vertices_590, vertices_108, vertices_868, vertices_676, vertices_376, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_76, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_56, vertices_88, vertices_104, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (false, vertices_897), (true, vertices_76), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_104), (true, vertices_304), (true, vertices_352), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 897 1 76 100 548 580 104 304 352 672 800 647 181 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 4 5 7 8 868 100 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 108
cert_cover_2 1 2 1 4 5 44 108 3
cert_coverFacet 2 868
cert_cover_5 2 1 1 4 5 7 100 868 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1343

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1344.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1344

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 782, 586, 428, 632, 808, 944, 848, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 262, 74, 522, 578, 770, 44, 268, 164, 388, 56, 88, 296, 552, 584, 776, 176, 560, 336, 592, 400, 784, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_782, vertices_586, vertices_428, vertices_632, vertices_808, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_74, vertices_522, vertices_578, vertices_770, vertices_44, vertices_268, vertices_164, vertices_388, vertices_56, vertices_88, vertices_296, vertices_552, vertices_584, vertices_776, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_522), (true, vertices_268), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_181) then 13 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 522 1 268 296 552 584 776 560 592 784 416 800 391 181 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 14 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 428
cert_cover_5 2 1 1 2 4 6 44 428 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 808
cert_cover_2 4 4 2 7 8 296 808 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1344

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1345.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1345

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 590, 774, 812, 420, 632, 944, 848, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 262, 518, 74, 578, 770, 44, 524, 164, 292, 388, 772, 56, 88, 552, 584, 176, 560, 336, 592, 400, 784, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_774, vertices_812, vertices_420, vertices_632, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_578, vertices_770, vertices_44, vertices_524, vertices_164, vertices_292, vertices_388, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_524), (true, vertices_292), (true, vertices_772), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_181) then 13 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 518 1 524 292 772 552 584 560 592 784 416 800 391 181 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 420
cert_cover_2 3 4 1 6 7 164 420 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1345

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1346.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1346

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 428, 908, 120, 872, 496, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 396, 524, 164, 644, 56, 88, 104, 296, 584, 776, 112, 176, 336, 400, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_428, vertices_908, vertices_120, vertices_872, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_396, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_296, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_396), (true, vertices_524), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_112), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 9 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_396) then 11 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_2 1 1 2 6 7 396
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 428
cert_cover_5 1 1 1 2 4 6 44 428 3
cert_coverFacet 2 908
cert_cover_5 2 1 1 2 6 8 396 908 3
cert_coverFacet 3 120
cert_cover_2 3 3 2 4 5 56 120 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1346

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1347.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1347

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 364, 740, 440, 344, 992, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 76, 100, 164, 580, 644, 56, 88, 280, 296, 328, 176, 336, 400, 736, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_364, vertices_740, vertices_440, vertices_344, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_76, vertices_100, vertices_164, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_736, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_76), (true, vertices_100), (true, vertices_580), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_736), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 9 16 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_647) then 10 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_181) then 11 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 18 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_736) then 20 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_2 1 4 5 6 8 736
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 364
cert_cover_5 1 2 1 2 4 5 44 364 3
cert_coverFacet 2 740
cert_cover_5 2 1 1 4 5 6 100 740 3
cert_coverFacet 3 440
cert_cover_5 3 3 2 3 4 6 56 440 3
cert_coverFacet 4 344
cert_cover_2 4 3 2 5 7 88 344 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 736 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1347

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1348.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1348

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 590, 790, 338, 962, 716, 692, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 82, 274, 322, 578, 770, 588, 140, 52, 532, 164, 644, 200, 304, 560, 336, 784, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_590, vertices_790, vertices_338, vertices_962, vertices_716, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_588, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_588), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 18 20 12 14 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_369) then 13 else
  if p.val = (false, vertices_929) then 17 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_588) then 19 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 14 => Sum.inl 4
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 322 962 2
cert_coverFacet 4 716
cert_cover_5 4 0 1 2 5 6 588 716 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1348

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1349.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1349

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 267, 425, 241, 721, 865, 126, 270, 662, 186, 364, 852, 11, 259, 515, 137, 265, 209, 97, 161, 289, 577, 641, 769, 14, 22, 262, 518, 58, 138, 266, 146, 642, 108, 268, 84, 532, 324, 772, 168, 296, 112, 176, 592, 656, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_267, vertices_425, vertices_241, vertices_721, vertices_865, vertices_126, vertices_270, vertices_662, vertices_186, vertices_364, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_137, vertices_265, vertices_209, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_58, vertices_138, vertices_266, vertices_146, vertices_642, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_592, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_267), (false, vertices_425), (false, vertices_241), (false, vertices_721), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_532), (true, vertices_324)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 12 14 16 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_425) then 15 else
  if p.val = (false, vertices_241) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (false, vertices_865) then 20 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_58) then 11 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_108) then 13 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_324) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 186
cert_cover 3 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 4 364
cert_cover 4 4 1 1 2 3 0 7 2 108 364 108 14 126 3
cert_coverFacet 5 852
cert_cover_5 5 3 1 3 5 7 84 852 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1349

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1350.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1350

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 775, 651, 269, 425, 241, 721, 865, 126, 662, 186, 364, 852, 7, 11, 515, 13, 261, 137, 265, 209, 97, 161, 289, 577, 641, 769, 14, 22, 518, 58, 138, 146, 642, 108, 268, 84, 532, 324, 772, 168, 296, 112, 176, 592, 656, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_775, vertices_651, vertices_269, vertices_425, vertices_241, vertices_721, vertices_865, vertices_126, vertices_662, vertices_186, vertices_364, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_13, vertices_261, vertices_137, vertices_265, vertices_209, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_138, vertices_146, vertices_642, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_592, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_775), (false, vertices_651), (false, vertices_269), (false, vertices_425), (false, vertices_241), (false, vertices_721), (false, vertices_865), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_108), (true, vertices_84), (true, vertices_532), (true, vertices_324)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 11 13 15 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_775) then 8 else
  if p.val = (false, vertices_651) then 9 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_425) then 14 else
  if p.val = (false, vertices_241) then 16 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (false, vertices_865) then 19 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_58) then 10 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_108) then 12 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_324) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 186
cert_cover 2 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 3 364
cert_cover 3 4 1 1 2 3 0 7 2 108 364 108 14 126 3
cert_coverFacet 4 852
cert_cover_5 4 3 1 3 5 7 84 852 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1350

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1351.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1351

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 590, 774, 684, 900, 376, 872, 944, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 262, 518, 74, 578, 770, 44, 524, 164, 388, 644, 772, 56, 88, 360, 552, 584, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_774, vertices_684, vertices_900, vertices_376, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_578, vertices_770, vertices_44, vertices_524, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_360, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_524), (true, vertices_644), (true, vertices_772), (true, vertices_360), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_360) then 18 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_2 1 2 4 5 7 360
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 5 1 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 376
cert_cover_5 4 1 2 3 4 5 56 376 3
cert_coverFacet 5 872
cert_cover_5 5 1 2 4 5 8 360 872 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1351

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1352.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1352

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 590, 646, 898, 684, 376, 872, 944, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 134, 518, 74, 578, 386, 642, 770, 44, 524, 164, 644, 56, 88, 360, 552, 584, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_646, vertices_898, vertices_684, vertices_376, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_134, vertices_518, vertices_74, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_360, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_642), (true, vertices_524), (true, vertices_644), (true, vertices_360), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_360) then 18 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_2 1 2 4 5 7 360
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 5 1 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 376
cert_cover_5 4 1 2 3 4 5 56 376 3
cert_coverFacet 5 872
cert_cover_5 5 1 2 4 5 8 360 872 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1352

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1832.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1832

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 75, 805, 709, 361, 961, 214, 794, 458, 658, 898, 692, 824, 7, 11, 67, 37, 69, 517, 41, 73, 289, 705, 321, 769, 22, 70, 26, 74, 266, 146, 530, 194, 386, 642, 770, 52, 148, 548, 196, 644, 56, 792, 296, 328, 560, 656, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_75, vertices_805, vertices_709, vertices_361, vertices_961, vertices_214, vertices_794, vertices_458, vertices_658, vertices_898, vertices_692, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_517, vertices_41, vertices_73, vertices_289, vertices_705, vertices_321, vertices_769, vertices_22, vertices_70, vertices_26, vertices_74, vertices_266, vertices_146, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_548, vertices_196, vertices_644, vertices_56, vertices_792, vertices_296, vertices_328, vertices_560, vertices_656, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_75), (false, vertices_805), (false, vertices_709), (false, vertices_361), (false, vertices_961), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_148), (true, vertices_792), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 13 16 19 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_792) then 18 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 8 692 52 3
cert_row_2 1 2 3 7 8 792
cert_row_4 2 0 1 3 5 6 214 22 3
cert_row_4 3 0 2 5 6 7 458 74 3
cert_rows
cert_pivot_2 4 8 1 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 26 794 3
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 74 458 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 692
cert_cover_5 5 0 1 3 4 6 52 692 3
cert_coverFacet 6 824
cert_cover_5 6 1 2 3 4 7 56 824 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1832

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1833.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1833

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 75, 213, 793, 457, 913, 358, 554, 842, 930, 692, 484, 568, 7, 11, 67, 21, 69, 25, 73, 265, 145, 785, 193, 385, 38, 70, 42, 74, 522, 290, 546, 322, 770, 52, 148, 356, 164, 196, 56, 536, 552, 328, 776, 560, 656, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_75, vertices_213, vertices_793, vertices_457, vertices_913, vertices_358, vertices_554, vertices_842, vertices_930, vertices_692, vertices_484, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_73, vertices_265, vertices_145, vertices_785, vertices_193, vertices_385, vertices_38, vertices_70, vertices_42, vertices_74, vertices_522, vertices_290, vertices_546, vertices_322, vertices_770, vertices_52, vertices_148, vertices_356, vertices_164, vertices_196, vertices_56, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_656, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_75), (false, vertices_213), (false, vertices_793), (false, vertices_457), (false, vertices_913), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_356), (true, vertices_164), (true, vertices_552), (true, vertices_560), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 13 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_356) then 16 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_2 1 1 4 5 7 356
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 5 38 358 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 930
cert_cover_5 3 2 0 4 6 7 290 930 2
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 356 484 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1833

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1834.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1834

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 75, 213, 793, 457, 913, 806, 710, 362, 962, 692, 568, 808, 7, 11, 67, 21, 69, 25, 73, 265, 145, 785, 193, 385, 38, 70, 518, 42, 74, 290, 706, 322, 770, 52, 148, 548, 196, 644, 56, 536, 296, 552, 328, 776, 560, 656, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_75, vertices_213, vertices_793, vertices_457, vertices_913, vertices_806, vertices_710, vertices_362, vertices_962, vertices_692, vertices_568, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_73, vertices_265, vertices_145, vertices_785, vertices_193, vertices_385, vertices_38, vertices_70, vertices_518, vertices_42, vertices_74, vertices_290, vertices_706, vertices_322, vertices_770, vertices_52, vertices_148, vertices_548, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_328, vertices_776, vertices_560, vertices_656, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_75), (false, vertices_213), (false, vertices_793), (false, vertices_457), (false, vertices_913), (true, vertices_518), (true, vertices_290), (true, vertices_706), (true, vertices_322), (true, vertices_770), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_706) then 13 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_2 1 0 5 6 8 706
cert_row_4 2 0 1 4 7 8 806 38 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 38 806 3
cert_coverFacet 1 710
cert_cover_5 1 1 0 1 5 6 70 710 3
cert_coverFacet 2 362
cert_cover_5 2 0 0 2 4 5 42 362 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 706 962 3
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1834

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1835.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1835

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 75, 805, 709, 361, 961, 214, 538, 458, 906, 658, 692, 824, 7, 11, 67, 37, 69, 517, 41, 73, 289, 705, 321, 769, 22, 70, 26, 74, 394, 522, 146, 530, 194, 642, 52, 148, 548, 196, 644, 56, 536, 296, 328, 776, 560, 656, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_75, vertices_805, vertices_709, vertices_361, vertices_961, vertices_214, vertices_538, vertices_458, vertices_906, vertices_658, vertices_692, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_517, vertices_41, vertices_73, vertices_289, vertices_705, vertices_321, vertices_769, vertices_22, vertices_70, vertices_26, vertices_74, vertices_394, vertices_522, vertices_146, vertices_530, vertices_194, vertices_642, vertices_52, vertices_148, vertices_548, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_328, vertices_776, vertices_560, vertices_656, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_75), (false, vertices_805), (false, vertices_709), (false, vertices_361), (false, vertices_961), (true, vertices_394), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_148), (true, vertices_536), (true, vertices_776), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_394) then 13 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 0 2 6 7 394
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 8 394 906 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 52 692 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1835

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1836.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1836

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 597, 217, 422, 710, 298, 564, 932, 376, 968, 880, 7, 11, 67, 131, 21, 69, 25, 137, 81, 193, 38, 70, 134, 42, 266, 290, 194, 386, 52, 532, 420, 548, 580, 644, 56, 88, 296, 200, 328, 392, 368, 560, 592, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_597, vertices_217, vertices_422, vertices_710, vertices_298, vertices_564, vertices_932, vertices_376, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_137, vertices_81, vertices_193, vertices_38, vertices_70, vertices_134, vertices_42, vertices_266, vertices_290, vertices_194, vertices_386, vertices_52, vertices_532, vertices_420, vertices_548, vertices_580, vertices_644, vertices_56, vertices_88, vertices_296, vertices_200, vertices_328, vertices_392, vertices_368, vertices_560, vertices_592, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_597), (false, vertices_217), (true, vertices_134), (true, vertices_290), (true, vertices_420), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_328), (true, vertices_368), (true, vertices_560), (true, vertices_800), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_420) then 18 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_368) then 22 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 7 368
cert_row_2 1 1 4 6 7 420
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 3 4 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 38 422 3
cert_coverFacet 1 710
cert_cover_5 1 2 0 1 5 6 70 710 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 8 420 932 3
cert_coverFacet 5 376
cert_cover_5 5 0 2 3 4 5 56 376 3
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 200 968 3
cert_coverFacet 7 880
cert_cover_5 7 0 3 4 5 8 368 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1836

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1837.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1837

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 341, 281, 961, 230, 810, 930, 692, 724, 568, 856, 7, 11, 67, 131, 21, 69, 25, 265, 273, 193, 321, 385, 38, 70, 42, 266, 162, 802, 194, 386, 52, 84, 660, 164, 196, 56, 280, 536, 552, 776, 560, 336, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_341, vertices_281, vertices_961, vertices_230, vertices_810, vertices_930, vertices_692, vertices_724, vertices_568, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_265, vertices_273, vertices_193, vertices_321, vertices_385, vertices_38, vertices_70, vertices_42, vertices_266, vertices_162, vertices_802, vertices_194, vertices_386, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_560, vertices_336, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_341), (false, vertices_281), (false, vertices_961), (true, vertices_162), (true, vertices_802), (true, vertices_660), (true, vertices_164), (true, vertices_196), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 17 15 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_281) then 2 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_802) then 14 else
  if p.val = (true, vertices_660) then 19 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 7 8 856 280 2
cert_row_2 1 0 4 7 8 802
cert_row_2 2 1 3 6 8 660
cert_row_4 3 0 1 4 5 6 230 38 3
cert_rows
cert_pivot_2 2 7 3 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 3 0 1 4 5 38 230 3
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 42 810 3
cert_coverFacet 2 930
cert_cover_5 2 1 0 4 6 7 162 930 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 0 2 3 5 7 280 856 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1837

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1838.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1838

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 229, 809, 929, 598, 346, 450, 692, 964, 568, 856, 7, 11, 67, 131, 37, 69, 41, 265, 161, 801, 193, 385, 22, 70, 26, 266, 82, 194, 322, 386, 52, 532, 164, 196, 580, 644, 56, 344, 536, 552, 776, 560, 592, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_229, vertices_809, vertices_929, vertices_598, vertices_346, vertices_450, vertices_692, vertices_964, vertices_568, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_37, vertices_69, vertices_41, vertices_265, vertices_161, vertices_801, vertices_193, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_194, vertices_322, vertices_386, vertices_52, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_56, vertices_344, vertices_536, vertices_552, vertices_776, vertices_560, vertices_592, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_229), (false, vertices_809), (false, vertices_929), (true, vertices_82), (true, vertices_322), (true, vertices_532), (true, vertices_580), (true, vertices_644), (true, vertices_344), (true, vertices_536), (true, vertices_560), (true, vertices_592), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 20 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_344) then 18 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 7 344
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 22 598 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 964
cert_cover_5 4 3 1 5 6 7 196 964 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 0 2 3 5 8 344 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1838

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1839.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1839

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 211, 613, 689, 961, 398, 198, 282, 914, 108, 460, 824, 872, 7, 19, 67, 37, 69, 49, 145, 545, 193, 577, 641, 14, 70, 134, 26, 266, 146, 274, 194, 386, 44, 76, 396, 100, 196, 56, 280, 104, 808, 328, 560, 656, 784, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_211, vertices_613, vertices_689, vertices_961, vertices_398, vertices_198, vertices_282, vertices_914, vertices_108, vertices_460, vertices_824, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_67, vertices_37, vertices_69, vertices_49, vertices_145, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_134, vertices_26, vertices_266, vertices_146, vertices_274, vertices_194, vertices_386, vertices_44, vertices_76, vertices_396, vertices_100, vertices_196, vertices_56, vertices_280, vertices_104, vertices_808, vertices_328, vertices_560, vertices_656, vertices_784, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_211), (false, vertices_613), (false, vertices_689), (false, vertices_961), (true, vertices_134), (true, vertices_266), (true, vertices_274), (true, vertices_386), (true, vertices_76), (true, vertices_396), (true, vertices_196), (true, vertices_280), (true, vertices_104), (true, vertices_808), (true, vertices_328), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_211) then 12 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_396) then 16 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_808) then 18 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_2 1 2 4 7 8 808
cert_row_4 2 0 3 6 7 8 914 146 3
cert_rows_3
cert_pivot_3 2 1 0
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 914
cert_cover_5 3 2 0 3 6 7 146 914 3
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 460
cert_cover_5 5 0 1 2 5 6 76 460 3
cert_coverFacet 6 824
cert_cover_5 6 1 2 3 4 7 56 824 3
cert_coverFacet 7 872
cert_cover_5 7 1 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1839

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1840.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1840

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 403, 707, 613, 689, 398, 198, 282, 108, 460, 824, 872, 976, 7, 19, 67, 131, 37, 69, 49, 145, 545, 577, 641, 14, 70, 134, 26, 266, 274, 194, 386, 44, 76, 396, 100, 196, 56, 280, 104, 808, 328, 560, 400, 656, 784, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_403, vertices_707, vertices_613, vertices_689, vertices_398, vertices_198, vertices_282, vertices_108, vertices_460, vertices_824, vertices_872, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_67, vertices_131, vertices_37, vertices_69, vertices_49, vertices_145, vertices_545, vertices_577, vertices_641, vertices_14, vertices_70, vertices_134, vertices_26, vertices_266, vertices_274, vertices_194, vertices_386, vertices_44, vertices_76, vertices_396, vertices_100, vertices_196, vertices_56, vertices_280, vertices_104, vertices_808, vertices_328, vertices_560, vertices_400, vertices_656, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_403), (false, vertices_707), (false, vertices_613), (false, vertices_689), (true, vertices_134), (true, vertices_266), (true, vertices_76), (true, vertices_396), (true, vertices_196), (true, vertices_280), (true, vertices_104), (true, vertices_808), (true, vertices_328), (true, vertices_784), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_403) then 12 else
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_808) then 19 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_2 1 2 4 7 8 808
cert_row_4 2 3 5 6 7 8 976 400 1
cert_rows_3
cert_pivot_3 2 1 3
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 460
cert_cover_5 4 0 1 2 5 6 76 460 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 872
cert_cover_5 6 1 2 4 5 7 104 872 3
cert_coverFacet 7 976
cert_cover_5 7 2 3 5 6 7 400 976 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1840

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1841.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1841

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 211, 613, 689, 961, 398, 198, 794, 914, 108, 460, 568, 872, 7, 19, 67, 37, 69, 49, 145, 545, 193, 577, 641, 14, 70, 134, 26, 266, 146, 786, 194, 386, 44, 76, 396, 100, 196, 56, 536, 104, 552, 328, 776, 560, 656, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_211, vertices_613, vertices_689, vertices_961, vertices_398, vertices_198, vertices_794, vertices_914, vertices_108, vertices_460, vertices_568, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_67, vertices_37, vertices_69, vertices_49, vertices_145, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_134, vertices_26, vertices_266, vertices_146, vertices_786, vertices_194, vertices_386, vertices_44, vertices_76, vertices_396, vertices_100, vertices_196, vertices_56, vertices_536, vertices_104, vertices_552, vertices_328, vertices_776, vertices_560, vertices_656, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_211), (false, vertices_613), (false, vertices_689), (false, vertices_961), (true, vertices_134), (true, vertices_266), (true, vertices_786), (true, vertices_386), (true, vertices_76), (true, vertices_396), (true, vertices_196), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 11 14 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_211) then 17 else
  if p.val = (false, vertices_613) then 12 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_786) then 18 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_396) then 13 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_776) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_2 1 1 2 6 7 396
cert_row_4 2 2 4 5 7 8 872 104 3
cert_rows_3
cert_pivot_3 1 0 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 26 794 3
cert_coverFacet 3 914
cert_cover_5 3 0 0 3 6 7 146 914 3
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 6 76 460 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 872
cert_cover_5 7 2 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1841

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1842.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1842

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 211, 613, 689, 961, 398, 198, 282, 914, 620, 460, 824, 840, 7, 19, 67, 37, 69, 49, 145, 545, 193, 577, 641, 14, 70, 134, 26, 266, 146, 274, 194, 386, 44, 76, 396, 612, 196, 56, 280, 552, 328, 584, 776, 560, 656, 784, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_211, vertices_613, vertices_689, vertices_961, vertices_398, vertices_198, vertices_282, vertices_914, vertices_620, vertices_460, vertices_824, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_67, vertices_37, vertices_69, vertices_49, vertices_145, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_134, vertices_26, vertices_266, vertices_146, vertices_274, vertices_194, vertices_386, vertices_44, vertices_76, vertices_396, vertices_612, vertices_196, vertices_56, vertices_280, vertices_552, vertices_328, vertices_584, vertices_776, vertices_560, vertices_656, vertices_784, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_211), (false, vertices_613), (false, vertices_689), (false, vertices_961), (true, vertices_134), (true, vertices_266), (true, vertices_274), (true, vertices_386), (true, vertices_76), (true, vertices_396), (true, vertices_196), (true, vertices_280), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_211) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_396) then 18 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_2 1 1 2 6 7 396
cert_row_4 2 0 3 6 7 8 914 146 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 1 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 914
cert_cover_5 3 2 0 3 6 7 146 914 3
cert_coverFacet 4 620
cert_cover_5 4 0 1 2 4 5 44 620 3
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 6 76 460 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1842

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1843.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1843

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 395, 275, 681, 817, 961, 78, 406, 198, 714, 620, 628, 468, 848, 11, 19, 259, 41, 137, 49, 273, 545, 385, 641, 769, 14, 22, 70, 134, 74, 138, 274, 194, 386, 44, 76, 52, 84, 404, 612, 196, 552, 584, 648, 560, 336, 592, 784, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_395, vertices_275, vertices_681, vertices_817, vertices_961, vertices_78, vertices_406, vertices_198, vertices_714, vertices_620, vertices_628, vertices_468, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_41, vertices_137, vertices_49, vertices_273, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_134, vertices_74, vertices_138, vertices_274, vertices_194, vertices_386, vertices_44, vertices_76, vertices_52, vertices_84, vertices_404, vertices_612, vertices_196, vertices_552, vertices_584, vertices_648, vertices_560, vertices_336, vertices_592, vertices_784, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_395), (false, vertices_275), (false, vertices_681), (false, vertices_817), (false, vertices_961), (true, vertices_70), (true, vertices_134), (true, vertices_74), (true, vertices_194), (true, vertices_76), (true, vertices_84), (true, vertices_404), (true, vertices_612), (true, vertices_196), (true, vertices_584), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 19 13 16 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_681) then 15 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_404) then 18 else
  if p.val = (true, vertices_612) then 20 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 2 5 6 8 714 74 3
cert_rows_3
cert_pivot_3 1 4 0
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 406
cert_cover_5 1 1 0 1 3 6 22 406 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 714
cert_cover_5 3 2 0 2 5 6 74 714 3
cert_coverFacet 4 620
cert_cover_5 4 0 1 2 4 5 44 620 3
cert_coverFacet 5 628
cert_cover_5 5 0 1 3 4 5 52 628 3
cert_coverFacet 6 468
cert_cover_5 6 1 1 3 5 6 84 468 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1843

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1844.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1844

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 331, 595, 809, 561, 961, 78, 214, 236, 820, 916, 420, 488, 720, 11, 19, 67, 41, 265, 49, 529, 545, 321, 577, 769, 14, 22, 70, 74, 82, 44, 76, 52, 148, 788, 164, 292, 196, 388, 232, 296, 328, 560, 208, 592, 656, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_331, vertices_595, vertices_809, vertices_561, vertices_961, vertices_78, vertices_214, vertices_236, vertices_820, vertices_916, vertices_420, vertices_488, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_67, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_70, vertices_74, vertices_82, vertices_44, vertices_76, vertices_52, vertices_148, vertices_788, vertices_164, vertices_292, vertices_196, vertices_388, vertices_232, vertices_296, vertices_328, vertices_560, vertices_208, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_331), (false, vertices_595), (false, vertices_809), (false, vertices_561), (false, vertices_961), (true, vertices_70), (true, vertices_76), (true, vertices_148), (true, vertices_788), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_232), (true, vertices_208), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_788) then 16 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_232) then 19 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 5 6 232
cert_row_2 1 1 3 7 8 788
cert_row_4 2 0 1 3 5 6 214 22 3
cert_rows_3
cert_pivot_3 7 2 0
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 214
cert_cover_5 1 2 0 1 3 5 22 214 3
cert_coverFacet 2 236
cert_cover_5 2 0 1 2 4 5 44 236 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 488
cert_cover_5 6 0 2 4 5 7 232 488 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1844

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1845.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1845

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 787, 323, 677, 561, 961, 78, 346, 364, 484, 696, 920, 424, 7, 19, 67, 259, 37, 133, 49, 529, 545, 193, 321, 641, 769, 14, 70, 26, 74, 274, 322, 44, 76, 356, 164, 196, 56, 664, 280, 168, 296, 328, 392, 560, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_787, vertices_323, vertices_677, vertices_561, vertices_961, vertices_78, vertices_346, vertices_364, vertices_484, vertices_696, vertices_920, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_67, vertices_259, vertices_37, vertices_133, vertices_49, vertices_529, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_26, vertices_74, vertices_274, vertices_322, vertices_44, vertices_76, vertices_356, vertices_164, vertices_196, vertices_56, vertices_664, vertices_280, vertices_168, vertices_296, vertices_328, vertices_392, vertices_560, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_787), (false, vertices_323), (false, vertices_677), (false, vertices_561), (false, vertices_961), (true, vertices_74), (true, vertices_76), (true, vertices_356), (true, vertices_664), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 16 13 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_787) then 12 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_356) then 18 else
  if p.val = (true, vertices_664) then 15 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_2 1 2 3 6 8 664
cert_row_4 2 0 2 3 5 7 346 26 3
cert_rows_3
cert_pivot_3 6 1 0
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 26 346 3
cert_coverFacet 2 364
cert_cover_5 2 0 1 2 4 5 44 364 3
cert_coverFacet 3 484
cert_cover_5 3 0 1 4 5 6 356 484 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 920
cert_cover_5 5 1 2 3 6 7 664 920 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1845

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_multi_six_0212.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0212

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 525, 661, 809, 433, 961, 782, 214, 838, 250, 330, 708, 488, 13, 21, 517, 41, 521, 49, 145, 289, 385, 641, 769, 14, 22, 70, 774, 58, 74, 266, 210, 322, 524, 148, 196, 580, 644, 232, 296, 328, 776, 176, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_525, vertices_661, vertices_809, vertices_433, vertices_961, vertices_782, vertices_214, vertices_838, vertices_250, vertices_330, vertices_708, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_521, vertices_49, vertices_145, vertices_289, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_774, vertices_58, vertices_74, vertices_266, vertices_210, vertices_322, vertices_524, vertices_148, vertices_196, vertices_580, vertices_644, vertices_232, vertices_296, vertices_328, vertices_776, vertices_176, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_525), (false, vertices_661), (false, vertices_809), (false, vertices_433), (false, vertices_961), (true, vertices_70), (true, vertices_774), (true, vertices_74), (true, vertices_266), (true, vertices_210), (true, vertices_322), (true, vertices_196), (true, vertices_580), (true, vertices_232), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 14 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_661) then 9 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_433) then 18 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_774) then 10 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_210) then 13 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_232) then 16 else
  if p.val = (true, vertices_328) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 2 3 5 4 250 58 3
cert_row_4 2 0 2 3 5 6 250 58 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 214
cert_cover 1 3 2 0 1 3 0 5 3 22 214 210 58 250 5
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 7 70 838 3
cert_coverFacet 3 250
cert_cover_2 3 2 0 3 5 58 250 3
cert_coverFacet 4 330
cert_cover_2 4 2 0 5 7 74 330 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 488
cert_cover 6 5 2 2 4 3 0 7 3 232 488 232 58 250 5
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0212

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_multi_six_0213.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0213

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 269, 405, 809, 689, 961, 590, 278, 838, 250, 466, 780, 744, 13, 21, 261, 41, 265, 49, 145, 545, 385, 641, 769, 14, 22, 582, 262, 58, 74, 210, 274, 322, 268, 524, 276, 772, 232, 552, 584, 776, 176, 400, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_269, vertices_405, vertices_809, vertices_689, vertices_961, vertices_590, vertices_278, vertices_838, vertices_250, vertices_466, vertices_780, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_41, vertices_265, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_582, vertices_262, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_268, vertices_524, vertices_276, vertices_772, vertices_232, vertices_552, vertices_584, vertices_776, vertices_176, vertices_400, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_269), (false, vertices_405), (false, vertices_809), (false, vertices_689), (false, vertices_961), (true, vertices_582), (true, vertices_262), (true, vertices_74), (true, vertices_210), (true, vertices_274), (true, vertices_322), (true, vertices_524), (true, vertices_772), (true, vertices_232), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 14 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_405) then 9 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_582) then 10 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_210) then 13 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_232) then 16 else
  if p.val = (true, vertices_584) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 0 2 3 5 4 250 58 3
cert_row_4 2 0 2 3 5 6 250 58 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 7 582 838 3
cert_coverFacet 3 250
cert_cover_2 3 2 0 3 5 58 250 3
cert_coverFacet 4 466
cert_cover 4 5 2 0 3 3 0 7 3 210 466 210 58 250 5
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 744
cert_cover 6 5 2 2 4 3 0 8 3 232 744 232 58 250 5
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0213

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1530 : Certifies 1530 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1339.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1531 : Certifies 1531 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1340.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1532 : Certifies 1532 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1341.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1533 : Certifies 1533 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1342.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1534 : Certifies 1534 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1343.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1535 : Certifies 1535 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1344.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1536 : Certifies 1536 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1345.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1537 : Certifies 1537 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1346.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1538 : Certifies 1538 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1347.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1539 : Certifies 1539 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1348.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1540 : Certifies 1540 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1349.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1541 : Certifies 1541 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1350.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1542 : Certifies 1542 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1351.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1543 : Certifies 1543 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1352.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1544 : Certifies 1544 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1832.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1545 : Certifies 1545 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1833.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1546 : Certifies 1546 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1834.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1547 : Certifies 1547 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1835.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1548 : Certifies 1548 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1836.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1549 : Certifies 1549 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1837.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1550 : Certifies 1550 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1838.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1551 : Certifies 1551 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1839.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1552 : Certifies 1552 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1840.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1553 : Certifies 1553 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1841.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1554 : Certifies 1554 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1842.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1555 : Certifies 1555 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1843.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1556 : Certifies 1556 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1844.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1557 : Certifies 1557 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1845.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1558 : Certifies 1558 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0212.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1559 : Certifies 1559 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0213.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B051 (j : Fin 30) :
    Certifies (1530 + j.val) := by
  fin_cases j
  · exact projection_1530
  · exact projection_1531
  · exact projection_1532
  · exact projection_1533
  · exact projection_1534
  · exact projection_1535
  · exact projection_1536
  · exact projection_1537
  · exact projection_1538
  · exact projection_1539
  · exact projection_1540
  · exact projection_1541
  · exact projection_1542
  · exact projection_1543
  · exact projection_1544
  · exact projection_1545
  · exact projection_1546
  · exact projection_1547
  · exact projection_1548
  · exact projection_1549
  · exact projection_1550
  · exact projection_1551
  · exact projection_1552
  · exact projection_1553
  · exact projection_1554
  · exact projection_1555
  · exact projection_1556
  · exact projection_1557
  · exact projection_1558
  · exact projection_1559

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
