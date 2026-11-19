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
/- Source: ProjectionCertificates/R_one_six_0668.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0668

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 270, 906, 812, 628, 744, 848, 960, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 336, 592, 784, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_270, vertices_906, vertices_812, vertices_628, vertices_744, vertices_848, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0668

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0669.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0669

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 398, 796, 340, 452, 632, 976, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 266, 386, 28, 268, 84, 276, 196, 324, 388, 56, 536, 552, 776, 112, 336, 592, 784, 608, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_398, vertices_796, vertices_340, vertices_452, vertices_632, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_28, vertices_268, vertices_84, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_268), (true, vertices_276), (true, vertices_324), (true, vertices_388), (true, vertices_536), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_737) then 20 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 796
cert_cover_5 1 1 1 2 3 7 28 796 3
cert_coverFacet 2 340
cert_cover_2 2 3 1 5 7 84 340 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 336 976 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0669

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0670.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0670

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 398, 796, 212, 404, 632, 976, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 266, 386, 28, 268, 84, 148, 276, 196, 388, 56, 536, 552, 776, 112, 208, 592, 400, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_398, vertices_796, vertices_212, vertices_404, vertices_632, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_28, vertices_268, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_208, vertices_592, vertices_400, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_388), (true, vertices_536), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_737) then 20 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 796
cert_cover_5 1 1 1 2 3 7 28 796 3
cert_coverFacet 2 212
cert_cover_2 2 3 1 5 6 84 212 3
cert_coverFacet 3 404
cert_cover_2 3 3 1 6 7 148 404 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0670

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0672.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0672

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 135, 899, 173, 617, 849, 481, 126, 406, 794, 244, 600, 464, 7, 131, 515, 13, 133, 41, 521, 97, 161, 321, 577, 385, 769, 14, 22, 134, 26, 522, 274, 386, 770, 44, 116, 148, 164, 88, 536, 104, 584, 208, 336, 592, 400, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_135, vertices_899, vertices_173, vertices_617, vertices_849, vertices_481, vertices_126, vertices_406, vertices_794, vertices_244, vertices_600, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_515, vertices_13, vertices_133, vertices_41, vertices_521, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_134, vertices_26, vertices_522, vertices_274, vertices_386, vertices_770, vertices_44, vertices_116, vertices_148, vertices_164, vertices_88, vertices_536, vertices_104, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_135), (false, vertices_899), (false, vertices_173), (false, vertices_617), (false, vertices_849), (false, vertices_481), (true, vertices_22), (true, vertices_26), (true, vertices_274), (true, vertices_116), (true, vertices_148), (true, vertices_88), (true, vertices_536), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 10 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_899) then 11 else
  if p.val = (false, vertices_173) then 13 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (false, vertices_481) then 20 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_116) then 14 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 0 2 3 7 8 794 26 3
cert_rows
cert_pivot_2 4 5 1 0
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 406
cert_cover_5 1 2 0 1 3 6 22 406 3
cert_coverFacet 2 794
cert_cover_5 2 3 0 2 3 7 26 794 3
cert_coverFacet 3 244
cert_cover 3 4 1 1 3 3 0 6 2 116 244 116 14 126 3
cert_coverFacet 4 600
cert_cover_2 4 3 2 5 8 88 600 3
cert_coverFacet 5 464
cert_cover_2 5 5 3 6 7 208 464 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0672

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0683.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0683

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 283, 899, 45, 677, 89, 617, 849, 126, 406, 244, 464, 992, 11, 131, 259, 13, 37, 133, 25, 41, 73, 81, 273, 545, 577, 641, 769, 14, 22, 134, 26, 274, 386, 44, 116, 148, 164, 88, 104, 208, 336, 400, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_283, vertices_899, vertices_45, vertices_677, vertices_89, vertices_617, vertices_849, vertices_126, vertices_406, vertices_244, vertices_464, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_13, vertices_37, vertices_133, vertices_25, vertices_41, vertices_73, vertices_81, vertices_273, vertices_545, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_134, vertices_26, vertices_274, vertices_386, vertices_44, vertices_116, vertices_148, vertices_164, vertices_88, vertices_104, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_283), (false, vertices_899), (false, vertices_45), (false, vertices_677), (false, vertices_89), (false, vertices_617), (false, vertices_849), (true, vertices_22), (true, vertices_116), (true, vertices_148), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 12 15 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 9 else
  if p.val = (false, vertices_283) then 10 else
  if p.val = (false, vertices_899) then 11 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_677) then 13 else
  if p.val = (false, vertices_89) then 1 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_116) then 14 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_208) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_448) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_89), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 7 8 992 224 3
cert_row_4 1 0 1 2 3 4 126 14 3
cert_row_4 2 0 1 2 3 5 126 14 3
cert_row_4 3 0 1 3 6 7 406 22 3
cert_rows
cert_pivot_2 8 4 2 0
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 406
cert_cover_5 1 3 0 1 3 6 22 406 3
cert_coverFacet 2 244
cert_cover 2 4 1 1 3 3 0 6 2 116 244 116 14 126 3
cert_coverFacet 3 464
cert_cover_2 3 5 3 6 7 208 464 3
cert_coverFacet 4 992
cert_cover_5 4 0 4 5 6 7 224 992 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0683

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0686.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0686

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 275, 899, 677, 345, 617, 481, 126, 654, 406, 556, 244, 464, 19, 259, 515, 25, 73, 521, 273, 97, 161, 545, 321, 385, 641, 14, 22, 134, 26, 522, 274, 386, 642, 44, 524, 116, 148, 164, 548, 644, 88, 104, 552, 208, 336, 400, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_275, vertices_899, vertices_677, vertices_345, vertices_617, vertices_481, vertices_126, vertices_654, vertices_406, vertices_556, vertices_244, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_25, vertices_73, vertices_521, vertices_273, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_14, vertices_22, vertices_134, vertices_26, vertices_522, vertices_274, vertices_386, vertices_642, vertices_44, vertices_524, vertices_116, vertices_148, vertices_164, vertices_548, vertices_644, vertices_88, vertices_104, vertices_552, vertices_208, vertices_336, vertices_400, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_275), (false, vertices_899), (false, vertices_677), (false, vertices_345), (false, vertices_617), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_134), (true, vertices_44), (true, vertices_524), (true, vertices_116), (true, vertices_148), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 10 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_899) then 11 else
  if p.val = (false, vertices_677) then 13 else
  if p.val = (false, vertices_345) then 16 else
  if p.val = (false, vertices_617) then 17 else
  if p.val = (false, vertices_481) then 20 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_116) then 14 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 2 6 8 654 14 3
cert_row_4 3 0 1 3 6 7 406 22 3
cert_rows
cert_pivot_2 4 5 2 0
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 654
cert_cover_5 1 2 0 1 2 6 14 654 3
cert_coverFacet 2 406
cert_cover_5 2 3 0 1 3 6 22 406 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 244
cert_cover 4 4 1 1 3 3 0 6 2 116 244 116 14 126 3
cert_coverFacet 5 464
cert_cover_2 5 5 3 6 7 208 464 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0686

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0689.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0689

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 139, 789, 121, 201, 465, 782, 714, 962, 620, 564, 880, 7, 11, 131, 21, 261, 57, 73, 137, 81, 273, 193, 385, 14, 262, 138, 522, 706, 386, 770, 44, 524, 52, 532, 548, 772, 104, 200, 584, 112, 560, 336, 784, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_139, vertices_789, vertices_121, vertices_201, vertices_465, vertices_782, vertices_714, vertices_962, vertices_620, vertices_564, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_137, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_522, vertices_706, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_139), (false, vertices_789), (false, vertices_121), (false, vertices_201), (false, vertices_465), (true, vertices_522), (true, vertices_706), (true, vertices_770), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_560), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_706) then 12 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 8 706
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 6 0 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 138 714 2
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 706 962 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 44 620 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0689

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0690.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0690

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 789, 809, 625, 142, 906, 124, 204, 468, 744, 976, 7, 11, 259, 21, 261, 41, 265, 49, 529, 545, 769, 14, 134, 138, 266, 386, 60, 76, 140, 84, 276, 196, 388, 104, 552, 200, 648, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_789, vertices_809, vertices_625, vertices_142, vertices_906, vertices_124, vertices_204, vertices_468, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_134, vertices_138, vertices_266, vertices_386, vertices_60, vertices_76, vertices_140, vertices_84, vertices_276, vertices_196, vertices_388, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_789), (false, vertices_809), (false, vertices_625), (true, vertices_138), (true, vertices_76), (true, vertices_140), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_200), (true, vertices_648), (true, vertices_464), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_464) then 20 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_2 1 3 5 6 7 464
cert_row_4 2 0 2 6 7 8 906 138 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 906
cert_cover_5 1 2 0 2 6 7 138 906 3
cert_coverFacet 2 124
cert_cover_5 2 0 1 2 3 5 60 124 3
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 468
cert_cover_5 4 1 1 3 5 6 84 468 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0690

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0692.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0692

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 781, 581, 961, 598, 122, 202, 300, 820, 488, 880, 7, 11, 131, 13, 69, 517, 265, 193, 577, 385, 769, 22, 70, 58, 74, 138, 82, 194, 44, 268, 52, 532, 292, 580, 772, 104, 296, 200, 392, 112, 816, 592, 352, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_781, vertices_581, vertices_961, vertices_598, vertices_122, vertices_202, vertices_300, vertices_820, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_69, vertices_517, vertices_265, vertices_193, vertices_577, vertices_385, vertices_769, vertices_22, vertices_70, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_781), (false, vertices_581), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_816), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_816) then 19 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_352) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 581 74 82 532 292 104 296 200 112 592 352 199 395 781 816
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 3 4 7 8 816
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coverFacet 6 880
cert_cover_5 6 1 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0692

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0693.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0693

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 597, 121, 201, 782, 582, 962, 812, 564, 488, 880, 7, 11, 131, 21, 69, 57, 73, 137, 81, 193, 14, 70, 518, 266, 194, 578, 386, 770, 44, 780, 52, 532, 548, 580, 104, 296, 200, 392, 112, 560, 592, 352, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_597, vertices_121, vertices_201, vertices_782, vertices_582, vertices_962, vertices_812, vertices_564, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_14, vertices_70, vertices_518, vertices_266, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_780, vertices_52, vertices_532, vertices_548, vertices_580, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_597), (false, vertices_121), (false, vertices_201), (true, vertices_518), (true, vertices_578), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 44 812 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 488
cert_cover_5 5 2 2 4 5 6 104 488 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0693

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0694.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0694

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 214, 122, 202, 556, 692, 872, 456, 752, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 194, 44, 524, 52, 148, 548, 644, 104, 552, 200, 328, 392, 776, 112, 688, 208, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_214, vertices_122, vertices_202, vertices_556, vertices_692, vertices_872, vertices_456, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_524, vertices_52, vertices_148, vertices_548, vertices_644, vertices_104, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_688, vertices_208, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_148), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_328), (true, vertices_112), (true, vertices_688), (true, vertices_208), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_688) then 20 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 3 4 6 8 688
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 104 872 3
cert_coverFacet 6 456
cert_cover_2 6 5 2 6 7 200 456 3
cert_coverFacet 7 752
cert_cover_5 7 1 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0694

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0696.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0696

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 597, 121, 201, 705, 782, 962, 812, 564, 488, 880, 7, 11, 131, 21, 517, 57, 73, 137, 81, 193, 577, 641, 14, 518, 266, 386, 642, 770, 44, 780, 52, 532, 548, 104, 296, 200, 392, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_597, vertices_121, vertices_201, vertices_705, vertices_782, vertices_962, vertices_812, vertices_564, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_517, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_577, vertices_641, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_532, vertices_548, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_597), (false, vertices_121), (false, vertices_201), (false, vertices_705), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_780) then 15 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 488
cert_cover_5 4 2 2 4 5 6 104 488 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0696

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0697.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0697

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 598, 122, 202, 706, 300, 820, 488, 880, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 518, 58, 74, 138, 82, 194, 578, 642, 44, 268, 52, 532, 292, 772, 104, 296, 200, 392, 112, 816, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_598, vertices_122, vertices_202, vertices_706, vertices_300, vertices_820, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_518, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_578), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_816), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_816) then 20 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 3 4 7 8 816
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 820
cert_cover_5 5 1 1 3 4 7 52 820 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 880
cert_cover_5 7 1 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0697

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0698.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0698

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 534, 122, 202, 722, 364, 820, 456, 880, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 518, 58, 74, 138, 82, 530, 194, 642, 44, 268, 52, 532, 292, 772, 104, 200, 328, 392, 112, 816, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_534, vertices_122, vertices_202, vertices_722, vertices_364, vertices_820, vertices_456, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_518, vertices_58, vertices_74, vertices_138, vertices_82, vertices_530, vertices_194, vertices_642, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_200, vertices_328, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_200), (true, vertices_328), (true, vertices_112), (true, vertices_816), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_816) then 20 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 82 3
cert_row_2 1 3 4 7 8 816
cert_row_2 2 0 2 3 4 58
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 722
cert_cover_5 3 0 0 3 5 6 82 722 3
cert_coverFacet 4 364
cert_cover_5 4 3 1 2 4 5 44 364 3
cert_coverFacet 5 820
cert_cover_5 5 1 1 3 4 7 52 820 3
cert_coverFacet 6 456
cert_cover_2 6 5 2 6 7 200 456 3
cert_coverFacet 7 880
cert_cover_5 7 1 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0698

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0699.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0699

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 534, 122, 202, 722, 300, 372, 852, 488, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 518, 58, 74, 138, 82, 530, 194, 642, 44, 268, 52, 340, 532, 292, 772, 104, 296, 200, 392, 112, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_534, vertices_122, vertices_202, vertices_722, vertices_300, vertices_372, vertices_852, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_518, vertices_58, vertices_74, vertices_138, vertices_82, vertices_530, vertices_194, vertices_642, vertices_44, vertices_268, vertices_52, vertices_340, vertices_532, vertices_292, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_340), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_340) then 18 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 74 1 82 530 194 532 292 104 296 200 112 592 352 647 395 781 340
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 7 340
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 82 722 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 372
cert_cover_5 5 0 1 3 4 5 52 372 3
cert_coverFacet 6 852
cert_cover_5 6 0 1 3 5 8 340 852 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0699

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0700.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0700

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 534, 122, 202, 722, 300, 628, 868, 488, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 518, 58, 74, 138, 82, 530, 194, 642, 44, 268, 52, 532, 612, 292, 772, 104, 296, 200, 392, 112, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_534, vertices_122, vertices_202, vertices_722, vertices_300, vertices_628, vertices_868, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_518, vertices_58, vertices_74, vertices_138, vertices_82, vertices_530, vertices_194, vertices_642, vertices_44, vertices_268, vertices_52, vertices_532, vertices_612, vertices_292, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_532), (true, vertices_612), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 74 1 82 530 194 532 292 104 296 200 112 592 352 647 395 781 612
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 82 722 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 628
cert_cover_5 5 0 1 3 4 5 52 628 3
cert_coverFacet 6 868
cert_cover_5 6 0 1 4 5 7 612 868 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0700

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0701.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0701

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 533, 121, 201, 721, 782, 962, 300, 820, 488, 880, 7, 11, 131, 21, 517, 57, 73, 137, 81, 529, 193, 641, 14, 518, 266, 386, 642, 770, 44, 268, 52, 532, 292, 772, 104, 296, 200, 392, 112, 816, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_533, vertices_121, vertices_201, vertices_721, vertices_782, vertices_962, vertices_300, vertices_820, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_517, vertices_57, vertices_73, vertices_137, vertices_81, vertices_529, vertices_193, vertices_641, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_533), (false, vertices_121), (false, vertices_201), (false, vertices_721), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_296), (true, vertices_816), (true, vertices_352), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 14 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_816) then 19 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 386 962 1
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 488
cert_cover_5 4 3 2 4 5 6 104 488 3
cert_coverFacet 5 880
cert_cover_5 5 0 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0701

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0702.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0702

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 533, 121, 201, 721, 782, 962, 812, 628, 488, 864, 7, 11, 131, 21, 517, 57, 73, 137, 81, 529, 193, 641, 14, 518, 266, 386, 642, 770, 44, 780, 52, 532, 548, 104, 296, 200, 392, 112, 592, 352, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_533, vertices_121, vertices_201, vertices_721, vertices_782, vertices_962, vertices_812, vertices_628, vertices_488, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_517, vertices_57, vertices_73, vertices_137, vertices_81, vertices_529, vertices_193, vertices_641, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_532, vertices_548, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_533), (false, vertices_121), (false, vertices_201), (false, vertices_721), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_780) then 14 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_2 2 1 2 7 8 780
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 386 962 1
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 52 628 3
cert_coverFacet 4 488
cert_cover_5 4 3 2 4 5 6 104 488 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0702

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0703.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0703

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 533, 121, 201, 721, 782, 962, 812, 564, 488, 880, 7, 11, 131, 21, 517, 57, 73, 137, 81, 529, 193, 641, 14, 518, 266, 386, 642, 770, 44, 780, 52, 532, 548, 104, 296, 200, 392, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_533, vertices_121, vertices_201, vertices_721, vertices_782, vertices_962, vertices_812, vertices_564, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_517, vertices_57, vertices_73, vertices_137, vertices_81, vertices_529, vertices_193, vertices_641, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_532, vertices_548, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_533), (false, vertices_121), (false, vertices_201), (false, vertices_721), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_780) then 14 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 488
cert_cover_5 4 2 2 4 5 6 104 488 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0703

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0711.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0711

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 395, 789, 809, 625, 206, 390, 124, 468, 744, 904, 976, 7, 11, 259, 21, 261, 41, 265, 49, 529, 545, 769, 14, 134, 262, 138, 386, 60, 76, 84, 276, 196, 388, 104, 552, 200, 392, 648, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_395, vertices_789, vertices_809, vertices_625, vertices_206, vertices_390, vertices_124, vertices_468, vertices_744, vertices_904, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_134, vertices_262, vertices_138, vertices_386, vertices_60, vertices_76, vertices_84, vertices_276, vertices_196, vertices_388, vertices_104, vertices_552, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_395), (false, vertices_789), (false, vertices_809), (false, vertices_625), (true, vertices_134), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_388), (true, vertices_104), (true, vertices_200), (true, vertices_648), (true, vertices_464), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_464) then 20 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 2 5 6 206 14 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 468
cert_cover_5 3 0 1 3 5 6 84 468 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0711

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0712.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0712

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 387, 789, 121, 721, 897, 398, 812, 628, 488, 992, 7, 11, 131, 259, 21, 261, 57, 73, 81, 529, 193, 385, 641, 769, 14, 262, 138, 386, 44, 268, 52, 532, 548, 772, 104, 296, 200, 392, 112, 592, 480, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_387, vertices_789, vertices_121, vertices_721, vertices_897, vertices_398, vertices_812, vertices_628, vertices_488, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_592, vertices_480, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_387), (false, vertices_789), (false, vertices_121), (false, vertices_721), (false, vertices_897), (true, vertices_268), (true, vertices_548), (true, vertices_296), (true, vertices_392), (true, vertices_480), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 13 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_789) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (false, vertices_897) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_480) then 19 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 4 5 6 7 480
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 812
cert_cover_5 1 2 1 2 4 7 44 812 3
cert_coverFacet 2 628
cert_cover_5 2 3 1 3 4 5 52 628 3
cert_coverFacet 3 488
cert_cover_5 3 1 2 4 5 6 104 488 3
cert_coverFacet 4 992
cert_cover_5 4 1 4 5 6 8 480 992 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0712

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0713.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0713

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 387, 341, 121, 961, 398, 172, 692, 916, 744, 880, 7, 11, 131, 259, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 386, 44, 140, 52, 660, 276, 164, 388, 104, 168, 200, 112, 560, 336, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_387, vertices_341, vertices_121, vertices_961, vertices_398, vertices_172, vertices_692, vertices_916, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_140, vertices_52, vertices_660, vertices_276, vertices_164, vertices_388, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_387), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_140), (true, vertices_660), (true, vertices_164), (true, vertices_388), (true, vertices_168), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 15 12 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_660) then 17 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 1 3 6 8 660
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 172
cert_cover_2 1 2 1 4 6 44 172 3
cert_coverFacet 2 692
cert_cover_5 2 1 1 3 4 6 52 692 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 660 916 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0713

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0714.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0714

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 395, 789, 169, 625, 929, 206, 390, 124, 468, 744, 976, 7, 11, 259, 21, 261, 41, 137, 49, 529, 161, 545, 385, 769, 14, 134, 262, 138, 386, 60, 76, 84, 276, 196, 388, 104, 168, 200, 112, 464, 592, 784, 608, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_395, vertices_789, vertices_169, vertices_625, vertices_929, vertices_206, vertices_390, vertices_124, vertices_468, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_545, vertices_385, vertices_769, vertices_14, vertices_134, vertices_262, vertices_138, vertices_386, vertices_60, vertices_76, vertices_84, vertices_276, vertices_196, vertices_388, vertices_104, vertices_168, vertices_200, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_395), (false, vertices_789), (false, vertices_169), (false, vertices_625), (false, vertices_929), (true, vertices_134), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_388), (true, vertices_104), (true, vertices_200), (true, vertices_464), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 16 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_395) then 11 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_625) then 17 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_464) then 18 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 2 5 6 206 14 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 468
cert_cover_5 3 0 1 3 5 6 84 468 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 976
cert_cover_5 5 0 3 5 6 8 464 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0714

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0715.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0715

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 387, 341, 121, 961, 398, 684, 564, 916, 744, 880, 7, 11, 131, 259, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 386, 44, 140, 52, 276, 532, 548, 388, 644, 104, 680, 200, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_387, vertices_341, vertices_121, vertices_961, vertices_398, vertices_684, vertices_564, vertices_916, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_140, vertices_52, vertices_276, vertices_532, vertices_548, vertices_388, vertices_644, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_387), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_140), (true, vertices_532), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_680), (true, vertices_560), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 17 14 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_680) then 18 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 2 4 6 8 680
cert_row_4 2 1 3 6 7 8 916 276 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 276 916 2
cert_coverFacet 4 744
cert_cover_5 4 1 2 4 5 6 104 744 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0715

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0716.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0716

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 387, 789, 121, 465, 398, 684, 564, 964, 744, 880, 7, 11, 131, 259, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 386, 44, 140, 52, 532, 548, 388, 644, 772, 104, 680, 200, 112, 560, 336, 784, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_387, vertices_789, vertices_121, vertices_465, vertices_398, vertices_684, vertices_564, vertices_964, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_140, vertices_52, vertices_532, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_387), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_140), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_680), (true, vertices_560), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 18 14 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_680) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 2 4 6 8 680
cert_row_4 2 1 5 6 7 8 964 388 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 964
cert_cover_5 3 2 1 5 6 7 388 964 1
cert_coverFacet 4 744
cert_cover_5 4 1 2 4 5 6 104 744 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0716

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0717.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0717

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 387, 789, 121, 465, 654, 902, 620, 564, 968, 880, 7, 11, 131, 259, 21, 261, 57, 73, 81, 273, 193, 385, 14, 646, 262, 138, 386, 44, 524, 52, 532, 548, 772, 104, 200, 584, 648, 112, 560, 336, 784, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_387, vertices_789, vertices_121, vertices_465, vertices_654, vertices_902, vertices_620, vertices_564, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_646, vertices_262, vertices_138, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_387), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_646), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_608), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_646) then 12 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_646), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 2 5 6 7 8 968 200 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 646 902 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 968
cert_cover_5 4 2 2 5 6 7 200 968 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0717

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0718.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0718

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 387, 341, 121, 961, 654, 902, 812, 308, 744, 880, 7, 11, 131, 259, 21, 261, 57, 73, 81, 193, 321, 385, 14, 646, 262, 138, 386, 44, 524, 52, 276, 292, 772, 104, 552, 200, 648, 112, 304, 336, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_387, vertices_341, vertices_121, vertices_961, vertices_654, vertices_902, vertices_812, vertices_308, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_646, vertices_262, vertices_138, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_387), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_646), (true, vertices_524), (true, vertices_292), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_646) then 12 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_646), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 646 902 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0718

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0719.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0719

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 270, 390, 796, 468, 632, 976, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 262, 266, 386, 28, 268, 84, 276, 196, 388, 56, 536, 552, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_270, vertices_390, vertices_796, vertices_468, vertices_632, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_262, vertices_266, vertices_386, vertices_28, vertices_268, vertices_84, vertices_276, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_262), (true, vertices_268), (true, vertices_276), (true, vertices_388), (true, vertices_536), (true, vertices_464), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 10 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_737) then 19 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_464) then 17 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_rows_3
cert_pivot_3 1 6 2
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 468
cert_cover_5 3 0 1 3 5 6 84 468 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 976
cert_cover_5 5 0 3 5 6 8 464 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0719

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0720.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0720

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 270, 390, 412, 724, 632, 920, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 262, 266, 386, 28, 268, 84, 148, 196, 388, 56, 408, 536, 552, 776, 112, 592, 656, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_270, vertices_390, vertices_412, vertices_724, vertices_632, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_262, vertices_266, vertices_386, vertices_28, vertices_268, vertices_84, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_536, vertices_552, vertices_776, vertices_112, vertices_592, vertices_656, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_262), (true, vertices_268), (true, vertices_148), (true, vertices_388), (true, vertices_408), (true, vertices_536), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 10 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_737) then 19 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_408) then 16 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_656) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_rows_3
cert_pivot_3 1 7 2
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 920
cert_cover_5 5 0 2 3 6 8 408 920 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0720

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0721.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0721

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 533, 121, 721, 897, 398, 812, 628, 488, 992, 7, 11, 131, 259, 21, 517, 57, 73, 81, 529, 193, 385, 641, 769, 14, 262, 138, 386, 44, 268, 52, 532, 548, 772, 104, 296, 200, 392, 112, 592, 480, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_533, vertices_121, vertices_721, vertices_897, vertices_398, vertices_812, vertices_628, vertices_488, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_592, vertices_480, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_533), (false, vertices_121), (false, vertices_721), (false, vertices_897), (true, vertices_268), (true, vertices_548), (true, vertices_296), (true, vertices_392), (true, vertices_480), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 13 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (false, vertices_897) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_480) then 19 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 4 5 6 7 480
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 812
cert_cover_5 1 2 1 2 4 7 44 812 3
cert_coverFacet 2 628
cert_cover_5 2 3 1 3 4 5 52 628 3
cert_coverFacet 3 488
cert_cover_5 3 1 2 4 5 6 104 488 3
cert_coverFacet 4 992
cert_cover_5 4 1 4 5 6 8 480 992 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0721

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1080 : Certifies 1080 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0668.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1081 : Certifies 1081 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0669.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1082 : Certifies 1082 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0670.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1083 : Certifies 1083 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0672.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1084 : Certifies 1084 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0683.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1085 : Certifies 1085 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0686.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1086 : Certifies 1086 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0689.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1087 : Certifies 1087 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0690.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1088 : Certifies 1088 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0692.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1089 : Certifies 1089 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0693.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1090 : Certifies 1090 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0694.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1091 : Certifies 1091 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0696.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1092 : Certifies 1092 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0697.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1093 : Certifies 1093 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0698.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1094 : Certifies 1094 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0699.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1095 : Certifies 1095 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0700.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1096 : Certifies 1096 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0701.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1097 : Certifies 1097 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0702.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1098 : Certifies 1098 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0703.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1099 : Certifies 1099 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0711.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1100 : Certifies 1100 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0712.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1101 : Certifies 1101 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0713.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1102 : Certifies 1102 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0714.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1103 : Certifies 1103 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0715.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1104 : Certifies 1104 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0716.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1105 : Certifies 1105 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0717.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1106 : Certifies 1106 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0718.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1107 : Certifies 1107 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0719.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1108 : Certifies 1108 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0720.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1109 : Certifies 1109 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0721.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B036 (j : Fin 30) :
    Certifies (1080 + j.val) := by
  fin_cases j
  · exact projection_1080
  · exact projection_1081
  · exact projection_1082
  · exact projection_1083
  · exact projection_1084
  · exact projection_1085
  · exact projection_1086
  · exact projection_1087
  · exact projection_1088
  · exact projection_1089
  · exact projection_1090
  · exact projection_1091
  · exact projection_1092
  · exact projection_1093
  · exact projection_1094
  · exact projection_1095
  · exact projection_1096
  · exact projection_1097
  · exact projection_1098
  · exact projection_1099
  · exact projection_1100
  · exact projection_1101
  · exact projection_1102
  · exact projection_1103
  · exact projection_1104
  · exact projection_1105
  · exact projection_1106
  · exact projection_1107
  · exact projection_1108
  · exact projection_1109

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
