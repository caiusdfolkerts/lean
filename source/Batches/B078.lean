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
/- Source: ProjectionCertificates/R_m14e10q1_0388.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0388

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 341, 405, 613, 681, 241, 398, 838, 810, 650, 184, 312, 408, 880, 277, 69, 133, 517, 81, 145, 97, 161, 545, 641, 134, 262, 518, 138, 266, 522, 642, 770, 324, 580, 388, 56, 152, 280, 168, 296, 552, 392, 648, 112, 176, 304, 336, 400, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_341, vertices_405, vertices_613, vertices_681, vertices_241, vertices_398, vertices_838, vertices_810, vertices_650, vertices_184, vertices_312, vertices_408, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_641, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_341), (false, vertices_405), (false, vertices_613), (false, vertices_681), (false, vertices_241), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_770), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_304), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 262 138 266 522 770 56 152 280 296 392 304 800 832 647 341 405 613 681 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_4 2 0 2 4 7 8 810 266 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 6 1 0 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 262 838 2
cert_coverFacet 2 810
cert_cover_5 2 2 0 2 4 7 266 810 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0388

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0392.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0392

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 775, 661, 229, 793, 465, 582, 810, 482, 610, 684, 612, 440, 664, 263, 69, 133, 517, 145, 273, 529, 193, 321, 769, 70, 518, 98, 290, 546, 322, 578, 770, 100, 164, 548, 580, 644, 152, 280, 536, 168, 296, 552, 648, 776, 400, 656, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_775, vertices_661, vertices_229, vertices_793, vertices_465, vertices_582, vertices_810, vertices_482, vertices_610, vertices_684, vertices_612, vertices_440, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_769, vertices_70, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_775), (false, vertices_661), (false, vertices_229), (false, vertices_793), (false, vertices_465), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_548), (true, vertices_580), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_648), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
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
cert_row_4 0 0 4 5 6 7 482 98 3
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 1 2 4 6 8 684 164 1
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 582
cert_cover_2 0 1 0 5 8 70 582 3
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 482
cert_cover_5 2 0 0 4 5 6 98 482 3
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 164 684 1
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 152 440 2
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0392

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0394.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0394

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 301, 557, 601, 457, 369, 678, 714, 178, 210, 594, 908, 436, 464, 45, 73, 265, 521, 49, 81, 529, 289, 545, 321, 50, 82, 146, 530, 162, 546, 194, 578, 642, 268, 524, 164, 292, 548, 388, 644, 200, 584, 392, 648, 176, 304, 208, 336, 592, 400, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_301, vertices_557, vertices_601, vertices_457, vertices_369, vertices_678, vertices_714, vertices_178, vertices_210, vertices_594, vertices_908, vertices_436, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_200, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_400, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_301), (false, vertices_557), (false, vertices_601), (false, vertices_457), (false, vertices_369), (true, vertices_82), (true, vertices_146), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 82 1 146 2 162 194 578 642 164 388 644 648 176 208 400 563 301 557 601 457 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 1 2 6 7 8 908 268 2
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 194 714 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 908
cert_cover_5 5 2 1 2 6 7 268 908 2
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0394

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0395.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0395

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 299, 403, 707, 901, 841, 310, 114, 210, 812, 692, 404, 632, 720, 43, 67, 131, 259, 73, 265, 577, 385, 641, 769, 50, 82, 146, 274, 98, 290, 194, 52, 148, 276, 292, 548, 388, 644, 772, 104, 296, 552, 584, 776, 112, 560, 208, 592, 400, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_299, vertices_403, vertices_707, vertices_901, vertices_841, vertices_310, vertices_114, vertices_210, vertices_812, vertices_692, vertices_404, vertices_632, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_67, vertices_131, vertices_259, vertices_73, vertices_265, vertices_577, vertices_385, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_274, vertices_98, vertices_290, vertices_194, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_400, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_299), (false, vertices_403), (false, vertices_707), (false, vertices_901), (false, vertices_841), (true, vertices_50), (true, vertices_82), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_548), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 16 else
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_403) then 20 else
  if p.val = (false, vertices_707) then 21 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
cert_nodeAtPriority 1 50 2 82 0 52 148 276 292 548 552 112 560 208 592 656 901 107 299 841 403 707
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_4 1 1 2 4 7 8 812 292 1
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 114
cert_cover_2 1 3 0 4 5 50 114 3
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 292 812 1
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 104 632 1
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0395

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0396.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0396

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 405, 677, 293, 713, 625, 209, 806, 218, 410, 842, 562, 594, 908, 37, 133, 261, 49, 81, 145, 273, 289, 545, 193, 577, 641, 154, 74, 266, 50, 82, 274, 530, 290, 546, 578, 770, 292, 548, 388, 644, 772, 200, 584, 392, 648, 776, 560, 208, 592, 400]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_405, vertices_677, vertices_293, vertices_713, vertices_625, vertices_209, vertices_806, vertices_218, vertices_410, vertices_842, vertices_562, vertices_594, vertices_908] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_145, vertices_273, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_154, vertices_74, vertices_266, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_578, vertices_770, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_560, vertices_208, vertices_592, vertices_400] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_405), (false, vertices_677), (false, vertices_293), (false, vertices_713), (false, vertices_625), (false, vertices_209), (true, vertices_154), (true, vertices_74), (true, vertices_266), (true, vertices_82), (true, vertices_530), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_772), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 13 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_154) then 14 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 293 1 209 74 266 82 530 546 578 770 772 392 776 307 154 405 677 713 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 1 2 6 7 8 908 388 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 154 218 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 74 842 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 594
cert_cover_2 5 3 0 5 8 82 594 3
cert_coverFacet 6 908
cert_cover_5 6 3 1 2 6 7 388 908 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0396

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0397.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0397

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 357, 165, 709, 809, 689, 94, 334, 570, 778, 722, 316, 180, 212, 37, 69, 133, 161, 289, 545, 321, 577, 641, 769, 78, 26, 266, 522, 82, 530, 322, 578, 770, 28, 268, 52, 84, 148, 164, 292, 196, 324, 56, 296, 552, 776, 176, 560, 208, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_357, vertices_165, vertices_709, vertices_809, vertices_689, vertices_94, vertices_334, vertices_570, vertices_778, vertices_722, vertices_316, vertices_180, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_78, vertices_26, vertices_266, vertices_522, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_268, vertices_52, vertices_84, vertices_148, vertices_164, vertices_292, vertices_196, vertices_324, vertices_56, vertices_296, vertices_552, vertices_776, vertices_176, vertices_560, vertices_208, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_357), (false, vertices_165), (false, vertices_709), (false, vertices_809), (false, vertices_689), (true, vertices_78), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_56), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 165 26 266 522 82 530 28 268 52 84 148 56 208 835 78 357 709 809 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 82 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 7 78 334 3
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 722
cert_cover_5 4 0 0 3 5 6 82 722 3
cert_coverFacet 5 316
cert_cover_5 5 3 1 2 3 4 28 316 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0397

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0398.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0398

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 213, 793, 713, 625, 401, 422, 234, 618, 778, 818, 372, 404, 228, 137, 265, 521, 81, 145, 273, 529, 193, 577, 385, 106, 138, 266, 522, 162, 290, 546, 386, 770, 84, 148, 276, 100, 164, 292, 196, 388, 200, 584, 776, 112, 304, 560, 400, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_213, vertices_793, vertices_713, vertices_625, vertices_401, vertices_422, vertices_234, vertices_618, vertices_778, vertices_818, vertices_372, vertices_404, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_200, vertices_584, vertices_776, vertices_112, vertices_304, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_213), (false, vertices_793), (false, vertices_713), (false, vertices_625), (false, vertices_401), (true, vertices_106), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 401 522 162 290 546 770 276 100 164 292 388 304 224 395 106 213 793 713 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 6 7 422 162 1
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 162 422 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 6 106 234 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 290 818 1
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 84 372 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0398

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0427.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0427

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 109, 677, 453, 361, 913, 558, 602, 282, 298, 786, 588, 724, 472, 37, 69, 133, 105, 289, 545, 321, 385, 641, 769, 26, 42, 266, 522, 274, 530, 290, 546, 770, 44, 76, 524, 548, 196, 580, 644, 88, 280, 296, 328, 584, 208, 592, 400, 656, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_109, vertices_677, vertices_453, vertices_361, vertices_913, vertices_558, vertices_602, vertices_282, vertices_298, vertices_786, vertices_588, vertices_724, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_105, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_44, vertices_76, vertices_524, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_296, vertices_328, vertices_584, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_109), (false, vertices_677), (false, vertices_453), (false, vertices_361), (false, vertices_913), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_524), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_584), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 26 1 42 2 266 522 274 530 524 580 88 280 584 208 592 803 677 453 109 361 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 1 3 5 6 8 724 196 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 26 602 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 196 724 1
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0427

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0428.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0428

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 213, 665, 809, 457, 593, 598, 166, 806, 198, 426, 450, 188, 572, 137, 265, 521, 81, 145, 529, 193, 321, 577, 769, 38, 70, 134, 518, 162, 290, 194, 322, 578, 386, 770, 60, 84, 148, 532, 164, 548, 196, 152, 536, 168, 296, 552, 392, 592, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_213, vertices_665, vertices_809, vertices_457, vertices_593, vertices_598, vertices_166, vertices_806, vertices_198, vertices_426, vertices_450, vertices_188, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_38, vertices_70, vertices_134, vertices_518, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_60, vertices_84, vertices_148, vertices_532, vertices_164, vertices_548, vertices_196, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_592, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_213), (false, vertices_665), (false, vertices_809), (false, vertices_457), (false, vertices_593), (true, vertices_38), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_60), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_168) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 4 7 8 806 38 3
cert_row_4 3 0 2 4 6 7 426 162 1
cert_rows
cert_pivot_2 5 3 1 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 70 598 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 38 806 3
cert_coverFacet 3 198
cert_cover_2 3 1 0 5 6 70 198 3
cert_coverFacet 4 426
cert_cover_5 4 3 0 2 4 6 162 426 1
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 188
cert_cover_5 6 1 1 2 3 6 60 188 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0428

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0433.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0433

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 453, 569, 241, 401, 865, 174, 558, 406, 838, 154, 538, 740, 184, 49, 145, 273, 529, 97, 545, 193, 321, 385, 769, 46, 134, 262, 518, 26, 138, 522, 146, 274, 530, 770, 164, 548, 196, 324, 580, 388, 56, 152, 536, 168, 552, 176, 400, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_453, vertices_569, vertices_241, vertices_401, vertices_865, vertices_174, vertices_558, vertices_406, vertices_838, vertices_154, vertices_538, vertices_740, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_536, vertices_168, vertices_552, vertices_176, vertices_400, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_453), (false, vertices_569), (false, vertices_241), (false, vertices_401), (false, vertices_865), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_164), (true, vertices_548), (true, vertices_580), (true, vertices_152), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 401 134 262 518 26 138 522 146 164 548 580 152 168 787 46 453 569 241 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 134 406 2
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 262 838 2
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 538
cert_cover_2 5 2 0 3 8 26 538 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0433

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0434.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0434

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 333, 233, 553, 689, 961, 110, 270, 118, 278, 570, 914, 340, 496, 41, 73, 265, 521, 161, 545, 193, 321, 641, 769, 14, 22, 102, 262, 42, 266, 522, 50, 274, 530, 770, 76, 268, 84, 276, 324, 104, 552, 112, 176, 560, 336, 400, 656, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_333, vertices_233, vertices_553, vertices_689, vertices_961, vertices_110, vertices_270, vertices_118, vertices_278, vertices_570, vertices_914, vertices_340, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_76, vertices_268, vertices_84, vertices_276, vertices_324, vertices_104, vertices_552, vertices_112, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_333), (false, vertices_233), (false, vertices_553), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_276), (true, vertices_112), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 118
cert_cover_5 2 0 0 1 3 4 22 118 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 570
cert_cover_5 4 1 0 2 3 4 42 570 2
cert_coverFacet 5 914
cert_cover_5 5 2 0 3 6 7 274 914 2
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0434

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0435.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0435

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 595, 309, 425, 689, 961, 590, 566, 278, 326, 300, 556, 460, 744, 83, 49, 273, 529, 161, 289, 321, 577, 385, 641, 22, 70, 262, 518, 274, 530, 322, 578, 44, 76, 268, 524, 52, 276, 292, 548, 324, 168, 296, 552, 200, 584, 392, 560, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_595, vertices_309, vertices_425, vertices_689, vertices_961, vertices_590, vertices_566, vertices_278, vertices_326, vertices_300, vertices_556, vertices_460, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_22, vertices_70, vertices_262, vertices_518, vertices_274, vertices_530, vertices_322, vertices_578, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_324, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_560, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_595), (false, vertices_309), (false, vertices_425), (false, vertices_689), (false, vertices_961), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_324), (true, vertices_552), (true, vertices_200), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 4 22 566 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 460
cert_cover_5 6 2 1 2 5 6 76 460 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 168 744 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0435

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0436.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0436

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 141, 525, 421, 837, 185, 817, 590, 218, 242, 562, 610, 460, 992, 13, 133, 261, 517, 25, 137, 521, 49, 529, 161, 289, 769, 26, 74, 522, 50, 210, 530, 98, 546, 578, 76, 140, 524, 324, 580, 388, 152, 200, 176, 560, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_141, vertices_525, vertices_421, vertices_837, vertices_185, vertices_817, vertices_590, vertices_218, vertices_242, vertices_562, vertices_610, vertices_460, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_49, vertices_529, vertices_161, vertices_289, vertices_769, vertices_26, vertices_74, vertices_522, vertices_50, vertices_210, vertices_530, vertices_98, vertices_546, vertices_578, vertices_76, vertices_140, vertices_524, vertices_324, vertices_580, vertices_388, vertices_152, vertices_200, vertices_176, vertices_560, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_141), (false, vertices_525), (false, vertices_421), (false, vertices_837), (false, vertices_185), (false, vertices_817), (true, vertices_74), (true, vertices_50), (true, vertices_210), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_76), (true, vertices_200), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 141 1 525 74 50 98 546 578 76 200 224 608 448 539 210 421 837 185 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 0 1 4
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 5 50 242 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 76 460 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0436

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0448.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0448

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 357, 677, 457, 721, 609, 302, 558, 662, 602, 154, 394, 216, 872, 37, 133, 261, 97, 545, 193, 321, 577, 385, 641, 46, 134, 262, 518, 26, 138, 266, 522, 146, 530, 386, 292, 548, 644, 88, 152, 296, 552, 200, 328, 584, 392, 208, 592, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_357, vertices_677, vertices_457, vertices_721, vertices_609, vertices_302, vertices_558, vertices_662, vertices_602, vertices_154, vertices_394, vertices_216, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_292, vertices_548, vertices_644, vertices_88, vertices_152, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_357), (false, vertices_677), (false, vertices_457), (false, vertices_721), (false, vertices_609), (true, vertices_46), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_296), (true, vertices_552), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 609 518 26 138 266 522 146 530 88 152 296 552 584 391 46 357 677 457 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 6 134 662 2
cert_coverFacet 3 602
cert_cover_5 3 2 0 2 3 5 26 602 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 296 872 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0448

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0449.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0449

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 105, 713, 913, 481, 110, 270, 118, 278, 434, 604, 788, 752, 41, 73, 265, 521, 97, 289, 193, 385, 641, 769, 14, 22, 102, 262, 42, 266, 50, 274, 290, 76, 268, 524, 84, 276, 532, 772, 104, 584, 112, 176, 592, 400, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_105, vertices_713, vertices_913, vertices_481, vertices_110, vertices_270, vertices_118, vertices_278, vertices_434, vertices_604, vertices_788, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_50, vertices_274, vertices_290, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_104, vertices_584, vertices_112, vertices_176, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_105), (false, vertices_713), (false, vertices_913), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_50), (true, vertices_274), (true, vertices_76), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_112), (true, vertices_176), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 105 14 22 262 50 274 76 84 276 532 112 176 592 299 102 781 713 913 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 0 1 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 50 434 3
cert_coverFacet 5 604
cert_cover_5 5 2 1 2 3 5 76 604 2
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0449

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0450.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0450

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 333, 233, 553, 465, 929, 110, 270, 118, 278, 570, 914, 340, 752, 41, 73, 265, 521, 161, 545, 193, 321, 385, 769, 14, 22, 102, 262, 42, 266, 522, 50, 274, 530, 770, 76, 268, 84, 276, 324, 104, 552, 112, 560, 208, 336, 400, 656, 224, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_333, vertices_233, vertices_553, vertices_465, vertices_929, vertices_110, vertices_270, vertices_118, vertices_278, vertices_570, vertices_914, vertices_340, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_76, vertices_268, vertices_84, vertices_276, vertices_324, vertices_104, vertices_552, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_333), (false, vertices_233), (false, vertices_553), (false, vertices_465), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_276), (true, vertices_112), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 553 14 22 262 42 50 274 530 84 276 112 560 656 779 102 333 233 465 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 118
cert_cover_5 2 0 0 1 3 4 22 118 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 570
cert_cover_5 4 1 0 2 3 4 42 570 2
cert_coverFacet 5 914
cert_cover_5 5 2 0 3 6 7 274 914 2
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0450

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0455.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0455

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 781, 661, 389, 617, 457, 673, 790, 362, 810, 690, 210, 338, 468, 133, 261, 517, 73, 265, 521, 97, 161, 545, 193, 385, 641, 298, 82, 146, 274, 530, 98, 162, 546, 194, 322, 770, 148, 276, 532, 388, 772, 104, 552, 328, 776, 208, 336, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_781, vertices_661, vertices_389, vertices_617, vertices_457, vertices_673, vertices_790, vertices_362, vertices_810, vertices_690, vertices_210, vertices_338, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_641, vertices_298, vertices_82, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_552, vertices_328, vertices_776, vertices_208, vertices_336, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_781), (false, vertices_661), (false, vertices_389), (false, vertices_617), (false, vertices_457), (false, vertices_673), (true, vertices_298), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_276), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_298) then 14 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 389 1 673 82 146 274 530 546 322 770 276 208 336 227 298 781 661 617 457
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 7 298
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 298 362 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 8 298 810 3
cert_coverFacet 3 690
cert_cover_5 3 1 0 3 4 6 146 690 2
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 148 468 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0455

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0457.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0457

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 117, 181, 709, 425, 865, 662, 154, 538, 842, 394, 604, 376, 184, 53, 69, 133, 97, 161, 289, 577, 385, 641, 769, 26, 138, 266, 522, 146, 530, 386, 642, 770, 84, 148, 532, 580, 644, 56, 88, 152, 536, 168, 296, 328, 584, 392, 112, 176, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_181, vertices_709, vertices_425, vertices_865, vertices_662, vertices_154, vertices_538, vertices_842, vertices_394, vertices_604, vertices_376, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_53, vertices_69, vertices_133, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_296, vertices_328, vertices_584, vertices_392, vertices_112, vertices_176, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_181), (false, vertices_709), (false, vertices_425), (false, vertices_865), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_328), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 1 2 3 5 8 604 84 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 266 842 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 604
cert_cover_5 5 2 1 2 3 5 84 604 1
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0457

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0460.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0460

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 787, 675, 565, 241, 401, 782, 714, 220, 412, 620, 116, 788, 736, 131, 259, 515, 49, 145, 273, 529, 161, 545, 385, 138, 266, 522, 642, 770, 156, 76, 268, 524, 52, 84, 276, 532, 100, 548, 772, 200, 584, 392, 112, 208, 400, 784, 224, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_787, vertices_675, vertices_565, vertices_241, vertices_401, vertices_782, vertices_714, vertices_220, vertices_412, vertices_620, vertices_116, vertices_788, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_156, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_548, vertices_772, vertices_200, vertices_584, vertices_392, vertices_112, vertices_208, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_787), (false, vertices_675), (false, vertices_565), (false, vertices_241), (false, vertices_401), (true, vertices_522), (true, vertices_156), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_772), (true, vertices_200), (true, vertices_584), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 138 714 2
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 156 220 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 7 156 412 3
cert_coverFacet 4 620
cert_cover_5 4 3 1 2 4 5 76 620 2
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0460

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0461.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0461

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 781, 425, 713, 817, 590, 566, 86, 434, 210, 706, 220, 412, 788, 137, 265, 521, 161, 289, 545, 641, 769, 22, 70, 518, 50, 82, 146, 162, 546, 194, 578, 642, 156, 76, 268, 524, 84, 276, 532, 772, 200, 584, 392, 304, 560, 208, 400, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_781, vertices_425, vertices_713, vertices_817, vertices_590, vertices_566, vertices_86, vertices_434, vertices_210, vertices_706, vertices_220, vertices_412, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_50, vertices_82, vertices_146, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_156, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_200, vertices_584, vertices_392, vertices_304, vertices_560, vertices_208, vertices_400, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_781), (false, vertices_425), (false, vertices_713), (false, vertices_817), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_156), (true, vertices_76), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_156) then 18 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 0 3 4 6 7 434 50 3
cert_rows
cert_pivot_2 5 2 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 22 566 3
cert_coverFacet 2 86
cert_cover_2 2 1 0 3 5 22 86 3
cert_coverFacet 3 434
cert_cover_5 3 3 0 3 4 6 50 434 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 156 220 3
cert_coverFacet 7 412
cert_cover_5 7 1 1 2 3 7 156 412 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0461

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0462.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0462

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 781, 613, 453, 721, 558, 58, 282, 778, 690, 466, 124, 348, 624, 69, 261, 517, 193, 577, 385, 641, 769, 26, 42, 266, 522, 50, 146, 274, 546, 386, 642, 770, 92, 44, 268, 524, 100, 548, 324, 56, 280, 776, 112, 560, 208, 336, 592, 656, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_781, vertices_613, vertices_453, vertices_721, vertices_558, vertices_58, vertices_282, vertices_778, vertices_690, vertices_466, vertices_124, vertices_348, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_546, vertices_386, vertices_642, vertices_770, vertices_92, vertices_44, vertices_268, vertices_524, vertices_100, vertices_548, vertices_324, vertices_56, vertices_280, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_781), (false, vertices_613), (false, vertices_453), (false, vertices_721), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_546), (true, vertices_92), (true, vertices_44), (true, vertices_56), (true, vertices_280), (true, vertices_112), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_92) then 18 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
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
cert_row_4 0 0 3 5 6 7 466 146 2
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 1 2 4 8 558 42 1
cert_row_4 3 0 3 4 6 8 690 50 3
cert_rows
cert_pivot_2 7 5 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 50 690 3
cert_coverFacet 5 466
cert_cover_5 5 0 0 3 5 6 146 466 2
cert_coverFacet 6 124
cert_cover_5 6 1 1 2 3 4 92 124 3
cert_coverFacet 7 348
cert_cover_5 7 1 1 2 3 7 92 348 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0462

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0472.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0472

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 677, 665, 433, 865, 94, 542, 614, 466, 834, 204, 652, 484, 216, 145, 273, 529, 161, 289, 545, 641, 769, 30, 70, 518, 82, 274, 530, 322, 578, 770, 76, 140, 524, 100, 164, 548, 196, 644, 88, 152, 536, 200, 648, 208, 400, 352, 608, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_677, vertices_665, vertices_433, vertices_865, vertices_94, vertices_542, vertices_614, vertices_466, vertices_834, vertices_204, vertices_652, vertices_484, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_88, vertices_152, vertices_536, vertices_200, vertices_648, vertices_208, vertices_400, vertices_352, vertices_608, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_677), (false, vertices_665), (false, vertices_433), (false, vertices_865), (true, vertices_30), (true, vertices_70), (true, vertices_518), (true, vertices_82), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_100), (true, vertices_196), (true, vertices_88), (true, vertices_200), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_30) then 16 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 1 4 5 8 614 70 2
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 5 70 614 2
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 82 466 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0472

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0478.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0478

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 565, 229, 837, 457, 673, 542, 154, 842, 394, 690, 124, 588, 248, 37, 69, 517, 161, 545, 193, 321, 385, 641, 769, 26, 138, 266, 522, 146, 530, 386, 642, 770, 28, 76, 524, 52, 532, 100, 580, 120, 152, 200, 328, 584, 392, 176, 560, 224, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_565, vertices_229, vertices_837, vertices_457, vertices_673, vertices_542, vertices_154, vertices_842, vertices_394, vertices_690, vertices_124, vertices_588, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_52, vertices_532, vertices_100, vertices_580, vertices_120, vertices_152, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_560, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_565), (false, vertices_229), (false, vertices_837), (false, vertices_457), (false, vertices_673), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_120), (true, vertices_152), (true, vertices_584), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_565) then 16 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_120) then 21 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_2 2 2 3 4 5 120
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 266 842 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 146 690 2
cert_coverFacet 5 124
cert_cover_5 5 2 1 2 3 4 28 124 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 6 120 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0478

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0486.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0486

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 597, 805, 453, 713, 566, 314, 538, 458, 650, 802, 124, 364, 600, 69, 261, 517, 193, 577, 385, 641, 769, 26, 138, 266, 522, 50, 530, 290, 546, 386, 642, 770, 108, 52, 84, 532, 292, 548, 324, 56, 88, 536, 296, 200, 328, 584, 648, 592, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_597, vertices_805, vertices_453, vertices_713, vertices_566, vertices_314, vertices_538, vertices_458, vertices_650, vertices_802, vertices_124, vertices_364, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_108, vertices_52, vertices_84, vertices_532, vertices_292, vertices_548, vertices_324, vertices_56, vertices_88, vertices_536, vertices_296, vertices_200, vertices_328, vertices_584, vertices_648, vertices_592, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_597), (false, vertices_805), (false, vertices_453), (false, vertices_713), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_108), (true, vertices_52), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_296), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_713) then 17 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_108) then 18 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_328) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 0 2 5 6 7 458 138 2
cert_rows
cert_pivot_2 8 1 3 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 458
cert_cover_5 3 3 0 2 5 6 138 458 2
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 124
cert_cover_5 6 1 1 2 3 4 108 124 2
cert_coverFacet 7 364
cert_cover_5 7 1 1 2 4 7 108 364 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0486

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0487.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0487

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 837, 793, 465, 737, 62, 526, 614, 538, 434, 674, 316, 780, 484, 145, 273, 529, 193, 321, 577, 641, 769, 14, 38, 518, 26, 522, 50, 146, 530, 162, 546, 642, 60, 268, 524, 100, 292, 324, 580, 772, 280, 536, 776, 304, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_837, vertices_793, vertices_465, vertices_737, vertices_62, vertices_526, vertices_614, vertices_538, vertices_434, vertices_674, vertices_316, vertices_780, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_518, vertices_26, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_60, vertices_268, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_280, vertices_536, vertices_776, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_837), (false, vertices_793), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_50), (true, vertices_162), (true, vertices_546), (true, vertices_60), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_292), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_60) then 18 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
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
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 4 5 8 614 38 3
cert_row_4 2 0 3 4 6 7 434 50 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 5 38 614 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 50 434 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 316
cert_cover_5 6 0 1 2 3 7 60 316 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 100 484 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0487

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0488.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0488

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 653, 405, 805, 841, 465, 678, 810, 330, 650, 370, 226, 244, 308, 133, 261, 517, 73, 137, 521, 401, 193, 321, 769, 74, 138, 266, 522, 98, 162, 290, 546, 194, 322, 642, 52, 148, 276, 164, 292, 548, 644, 328, 648, 776, 112, 304, 208, 336, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_653, vertices_405, vertices_805, vertices_841, vertices_465, vertices_678, vertices_810, vertices_330, vertices_650, vertices_370, vertices_226, vertices_244, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_401, vertices_193, vertices_321, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_642, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_644, vertices_328, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_653), (false, vertices_405), (false, vertices_805), (false, vertices_841), (false, vertices_465), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_642), (true, vertices_52), (true, vertices_164), (true, vertices_112), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 3 4 5 7 370 98 1
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 266 810 2
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 370
cert_cover_5 4 2 0 3 4 5 98 370 1
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0488

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0489.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0489

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 163, 707, 771, 781, 617, 241, 902, 418, 348, 716, 436, 212, 376, 35, 131, 259, 515, 41, 265, 521, 97, 161, 193, 577, 769, 162, 290, 386, 642, 770, 76, 268, 524, 84, 148, 276, 196, 388, 644, 772, 344, 104, 296, 584, 112, 176, 304, 208, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_163, vertices_707, vertices_771, vertices_781, vertices_617, vertices_241, vertices_902, vertices_418, vertices_348, vertices_716, vertices_436, vertices_212, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_97, vertices_161, vertices_193, vertices_577, vertices_769, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_644, vertices_772, vertices_344, vertices_104, vertices_296, vertices_584, vertices_112, vertices_176, vertices_304, vertices_208, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_163), (false, vertices_707), (false, vertices_771), (false, vertices_781), (false, vertices_617), (false, vertices_241), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_344), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_344) then 19 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
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
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_2 2 2 3 5 7 344
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 0 8 2 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 418
cert_cover_2 1 4 0 6 7 162 418 3
cert_coverFacet 2 348
cert_cover_5 2 2 1 2 3 5 76 348 2
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 76 716 3
cert_coverFacet 4 436
cert_cover_5 4 3 1 3 4 6 148 436 2
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 376
cert_cover_5 6 2 2 3 4 5 344 376 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0489

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0497.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0497

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 675, 291, 653, 309, 149, 241, 370, 610, 834, 412, 844, 472, 744, 35, 259, 515, 21, 133, 261, 517, 49, 145, 161, 289, 641, 98, 290, 546, 322, 578, 770, 140, 268, 524, 148, 276, 772, 408, 200, 328, 584, 648, 112, 304, 208, 336, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_675, vertices_291, vertices_653, vertices_309, vertices_149, vertices_241, vertices_370, vertices_610, vertices_834, vertices_412, vertices_844, vertices_472, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_161, vertices_289, vertices_641, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_772, vertices_408, vertices_200, vertices_328, vertices_584, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_675), (false, vertices_291), (false, vertices_653), (false, vertices_309), (false, vertices_149), (false, vertices_241), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_268), (true, vertices_408), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_336), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_408) then 19 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 7 370 98 1
cert_row_2 1 2 3 6 7 408
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 0 0 3 4 5 98 370 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 412
cert_cover_5 3 1 1 2 3 6 140 412 2
cert_coverFacet 4 844
cert_cover_5 4 2 1 2 5 7 268 844 2
cert_coverFacet 5 472
cert_cover_5 5 1 2 3 5 6 408 472 2
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 200 744 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0497

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0498.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0498

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 147, 787, 781, 213, 325, 369, 810, 242, 306, 674, 684, 460, 488, 19, 131, 515, 69, 133, 261, 517, 81, 145, 273, 321, 769, 50, 146, 274, 162, 290, 546, 642, 770, 140, 268, 524, 196, 324, 644, 168, 296, 552, 456, 776, 112, 304, 208, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_147, vertices_787, vertices_781, vertices_213, vertices_325, vertices_369, vertices_810, vertices_242, vertices_306, vertices_674, vertices_684, vertices_460, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_321, vertices_769, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_168, vertices_296, vertices_552, vertices_456, vertices_776, vertices_112, vertices_304, vertices_208, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_147), (false, vertices_787), (false, vertices_781), (false, vertices_213), (false, vertices_325), (false, vertices_369), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_140), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_456), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_456) then 19 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_2 1 2 5 6 7 456
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 2 0 2 4 7 290 810 1
cert_coverFacet 1 242
cert_cover_5 1 0 0 3 4 5 50 242 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 674
cert_cover_2 3 4 0 6 8 162 674 3
cert_coverFacet 4 684
cert_cover_5 4 3 1 2 4 6 140 684 2
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 6 140 460 2
cert_coverFacet 6 488
cert_cover_5 6 1 2 4 5 6 168 488 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0498

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0502.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0502

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 539, 99, 803, 533, 837, 481, 218, 234, 554, 468, 660, 932, 696, 19, 35, 67, 515, 21, 69, 517, 529, 97, 289, 321, 769, 26, 42, 202, 522, 82, 98, 546, 84, 148, 532, 324, 388, 644, 772, 152, 536, 168, 552, 208, 656, 224, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_539, vertices_99, vertices_803, vertices_533, vertices_837, vertices_481, vertices_218, vertices_234, vertices_554, vertices_468, vertices_660, vertices_932, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_515, vertices_21, vertices_69, vertices_517, vertices_529, vertices_97, vertices_289, vertices_321, vertices_769, vertices_26, vertices_42, vertices_202, vertices_522, vertices_82, vertices_98, vertices_546, vertices_84, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_656, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_539), (false, vertices_99), (false, vertices_803), (false, vertices_533), (false, vertices_837), (false, vertices_481), (true, vertices_42), (true, vertices_202), (true, vertices_148), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_208), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 13 else
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_837) then 14 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 1 4 6 7 8 932 388 1
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 0 0 2 3 5 26 218 3
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 5 42 234 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 932
cert_cover_5 5 2 1 4 6 7 388 932 1
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 152 696 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0502

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2373 : Certifies 2373 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0388.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2374 : Certifies 2374 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0392.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2375 : Certifies 2375 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0394.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2376 : Certifies 2376 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0395.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2377 : Certifies 2377 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0396.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2378 : Certifies 2378 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0397.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2379 : Certifies 2379 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0398.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2380 : Certifies 2380 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0427.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2381 : Certifies 2381 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0428.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2382 : Certifies 2382 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0433.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2383 : Certifies 2383 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0434.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2384 : Certifies 2384 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0435.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2385 : Certifies 2385 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0436.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2386 : Certifies 2386 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0448.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2387 : Certifies 2387 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0449.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2388 : Certifies 2388 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0450.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2389 : Certifies 2389 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0455.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2390 : Certifies 2390 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0457.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2391 : Certifies 2391 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0460.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2392 : Certifies 2392 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0461.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2393 : Certifies 2393 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0462.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2394 : Certifies 2394 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0472.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2395 : Certifies 2395 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0478.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2396 : Certifies 2396 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0486.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2397 : Certifies 2397 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0487.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2398 : Certifies 2398 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0488.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2399 : Certifies 2399 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0489.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2400 : Certifies 2400 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0497.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2401 : Certifies 2401 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0498.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2402 : Certifies 2402 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0502.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B078 (j : Fin 30) :
    Certifies (2373 + j.val) := by
  fin_cases j
  · exact projection_2373
  · exact projection_2374
  · exact projection_2375
  · exact projection_2376
  · exact projection_2377
  · exact projection_2378
  · exact projection_2379
  · exact projection_2380
  · exact projection_2381
  · exact projection_2382
  · exact projection_2383
  · exact projection_2384
  · exact projection_2385
  · exact projection_2386
  · exact projection_2387
  · exact projection_2388
  · exact projection_2389
  · exact projection_2390
  · exact projection_2391
  · exact projection_2392
  · exact projection_2393
  · exact projection_2394
  · exact projection_2395
  · exact projection_2396
  · exact projection_2397
  · exact projection_2398
  · exact projection_2399
  · exact projection_2400
  · exact projection_2401
  · exact projection_2402

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
