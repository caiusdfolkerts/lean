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
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m14e11q3_models_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 107, 659, 835, 157, 329, 905, 566, 610, 172, 916, 868, 420, 488, 43, 19, 67, 515, 29, 73, 137, 265, 145, 321, 641, 769, 54, 530, 98, 546, 578, 44, 140, 148, 532, 164, 292, 548, 388, 772, 104, 168, 328, 392, 656, 352, 608, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_107, vertices_659, vertices_835, vertices_157, vertices_329, vertices_905, vertices_566, vertices_610, vertices_172, vertices_916, vertices_868, vertices_420, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_19, vertices_67, vertices_515, vertices_29, vertices_73, vertices_137, vertices_265, vertices_145, vertices_321, vertices_641, vertices_769, vertices_54, vertices_530, vertices_98, vertices_546, vertices_578, vertices_44, vertices_140, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_104, vertices_168, vertices_328, vertices_392, vertices_656, vertices_352, vertices_608, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_107), (false, vertices_659), (false, vertices_835), (false, vertices_157), (false, vertices_329), (false, vertices_905), (true, vertices_546), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_772), (true, vertices_168), (true, vertices_352), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 12 14 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_107) then 16 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_157) then 13 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_905) then 17 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
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
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 1 4 5 7 8 868 292 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 8 54 566 3
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 148 916 3
cert_coverFacet 4 868
cert_cover_5 4 2 1 4 5 7 292 868 2
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0005

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_prism_smaller_next_many_prism_m13e13k3q7_models_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_smaller_next_many_prism_m13e13k3q7_models_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [655, 391, 619, 291, 233, 433, 630, 310, 908, 852, 472, 840, 240, 135, 523, 35, 259, 105, 137, 161, 289, 385, 54, 262, 518, 610, 290, 652, 596, 276, 388, 772, 200, 328, 584, 392, 776, 112, 176, 304, 208, 336, 400, 224, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_655, vertices_391, vertices_619, vertices_291, vertices_233, vertices_433, vertices_630, vertices_310, vertices_908, vertices_852, vertices_472, vertices_840, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_135, vertices_523, vertices_35, vertices_259, vertices_105, vertices_137, vertices_161, vertices_289, vertices_385, vertices_54, vertices_262, vertices_518, vertices_610, vertices_290, vertices_652, vertices_596, vertices_276, vertices_388, vertices_772, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_224, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_655), (false, vertices_391), (false, vertices_619), (false, vertices_291), (false, vertices_233), (false, vertices_433), (true, vertices_54), (true, vertices_596), (true, vertices_276), (true, vertices_772), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 10 12 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_655) then 17 else
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_619) then 19 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_233) then 11 else
  if p.val = (false, vertices_433) then 13 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_596) then 15 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_655), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_619), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 4 630 54 3
cert_row_4 1 2 3 5 6 7 472 200 1
cert_row_2 2 1 2 6 8 652
cert_row_4 3 0 1 3 5 8 630 54 3
cert_rows
cert_pivot_2 4 7 2 1
cert_heightProof 4
cert_coverFacet 0 630
cert_cover_2 0 1 0 3 5 54 630 3
cert_coverFacet 1 310
cert_cover 1 3 1 0 1 3 0 7 3 54 310 54 54 630 5
cert_coverFacet 2 908
cert_cover_5 2 2 1 2 6 7 652 908 3
cert_coverFacet 3 852
cert_cover 3 5 1 1 3 3 0 7 3 596 852 596 54 630 5
cert_coverFacet 4 472
cert_cover_5 4 1 2 3 5 6 200 472 1
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_smaller_next_many_prism_m13e13k3q7_models_0000

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_prism_smaller_next_pentpair_m13e12k2l1p0q1_models_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_smaller_next_pentpair_m13e12k2l1p0q1_models_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 189, 413, 809, 961, 54, 342, 166, 710, 122, 618, 452, 856, 157, 41, 265, 161, 545, 385, 641, 769, 22, 38, 70, 134, 106, 50, 82, 162, 546, 578, 642, 52, 276, 164, 196, 324, 388, 56, 88, 280, 552, 584, 776, 336, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_189, vertices_413, vertices_809, vertices_961, vertices_54, vertices_342, vertices_166, vertices_710, vertices_122, vertices_618, vertices_452, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_157, vertices_41, vertices_265, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_70, vertices_134, vertices_106, vertices_50, vertices_82, vertices_162, vertices_546, vertices_578, vertices_642, vertices_52, vertices_276, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_280, vertices_552, vertices_584, vertices_776, vertices_336, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_189), (false, vertices_413), (false, vertices_809), (false, vertices_961), (true, vertices_22), (true, vertices_38), (true, vertices_70), (true, vertices_134), (true, vertices_106), (true, vertices_50), (true, vertices_82), (true, vertices_578), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_584), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 16 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 13 else
  if p.val = (false, vertices_189) then 17 else
  if p.val = (false, vertices_413) then 18 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_106) then 14 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_189), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_413), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_4 2 0 1 3 5 7 342 22 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 4 6 0 2
cert_heightProof 4
cert_coverFacet 0 54
cert_cover_2 0 1 0 3 4 22 54 3
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 5 22 342 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 710
cert_cover_5 3 1 0 1 5 6 70 710 3
cert_coverFacet 4 122
cert_cover_5 4 0 0 2 3 4 106 122 2
cert_coverFacet 5 618
cert_cover_5 5 0 0 2 4 8 106 618 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 88 856 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_smaller_next_pentpair_m13e12k2l1p0q1_models_0000

end
end BundlePart2

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1980 : Certifies 1980 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1981 : Certifies 1981 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_smaller_next_many_prism_m13e13k3q7_models_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1982 : Certifies 1982 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_smaller_next_pentpair_m13e12k2l1p0q1_models_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B066 (j : Fin 3) :
    Certifies (1980 + j.val) := by
  fin_cases j
  · exact projection_1980
  · exact projection_1981
  · exact projection_1982

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
