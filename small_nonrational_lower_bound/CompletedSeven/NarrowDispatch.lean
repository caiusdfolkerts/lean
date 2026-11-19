module

public import CompletedSeven.PureClassification
public import CompletedSeven.MixedClassification
public import CompletedSeven.TwoSixThirteenClassification

/-!
# Seven-facet classifications used by the residual theorem

The pure and mixed branches use their complete numerical catalogues. In the
branch with two six-vertex facets, the separate surplus argument proves that
the seven-vertex facet has canonical template 13. All eight possible counts
of square pyramids are retained here.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.CompletedSeven

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open ActualResidualPartition MatroidChecked.SevenBudgetCoverage

theorem pure_rows : ∀ row ∈ noSixCases, Nonempty (PureRowCertificate row) := by
  intro row hrow
  simp only [noSixCases, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Case0034.certificate⟩
  · exact ⟨Case0035.certificate⟩
  · exact ⟨Case0036.certificate⟩
  · exact ⟨Case0037.certificate⟩
  · exact ⟨Case0038.certificate⟩
  · exact ⟨Case0039.certificate⟩
  · exact ⟨Case0040.certificate⟩
  · exact ⟨Case0041.certificate⟩
  · exact ⟨Case0042.certificate⟩
  · exact ⟨Case0043.certificate⟩
  · exact ⟨Case0044.certificate⟩
  · exact ⟨Case0045.certificate⟩
  · exact ⟨Case0046.certificate⟩
  · exact ⟨Case0047.certificate⟩
  · exact ⟨Case0048.certificate⟩
  · exact ⟨Case0049.certificate⟩
  · exact ⟨Case0050.certificate⟩
  · exact ⟨Case0051.certificate⟩
  · exact ⟨Case0052.certificate⟩
  · exact ⟨Case0053.certificate⟩
  · exact ⟨Case0054.certificate⟩
  · exact ⟨Case0055.certificate⟩
  · exact ⟨Case0056.certificate⟩
  · exact ⟨Case0057.certificate⟩
  · exact ⟨Case0058.certificate⟩
  · exact ⟨Case0059.certificate⟩
  · exact ⟨Case0060.certificate⟩
  · exact ⟨Case0061.certificate⟩
  · exact ⟨Case0062.certificate⟩
  · exact ⟨Case0063.certificate⟩
  · exact ⟨Case0064.certificate⟩
  · exact ⟨Case0065.certificate⟩
  · exact ⟨Case0066.certificate⟩
  · exact ⟨Case0067.certificate⟩
  · exact ⟨Case0068.certificate⟩
  · exact ⟨Case0069.certificate⟩
  · exact ⟨Case0070.certificate⟩
  · exact ⟨Case0071.certificate⟩
  · exact ⟨Case0072.certificate⟩
  · exact ⟨Case0073.certificate⟩
  · exact ⟨Case0074.certificate⟩
  · exact ⟨Case0075.certificate⟩
  · exact ⟨Case0076.certificate⟩
  · exact ⟨Case0077.certificate⟩
  · exact ⟨Case0078.certificate⟩
  · exact ⟨Case0079.certificate⟩
  · exact ⟨Case0080.certificate⟩
  · exact ⟨Case0081.certificate⟩
  · exact ⟨Case0082.certificate⟩
  · exact ⟨Case0083.certificate⟩
  · exact ⟨Case0084.certificate⟩
  · exact ⟨Case0085.certificate⟩
  · exact ⟨Case0086.certificate⟩
  · exact ⟨Case0087.certificate⟩
  · exact ⟨Case0088.certificate⟩
  · exact ⟨Case0089.certificate⟩
  · exact ⟨Case0090.certificate⟩
  · exact ⟨Case0091.certificate⟩
  · exact ⟨Case0092.certificate⟩
  · exact ⟨Case0093.certificate⟩
  · exact ⟨Case0094.certificate⟩
  · exact ⟨Case0095.certificate⟩
  · exact ⟨Case0096.certificate⟩
  · exact ⟨Case0097.certificate⟩
  · exact ⟨Case0098.certificate⟩
  · exact ⟨Case0099.certificate⟩
  · exact ⟨Case0100.certificate⟩
  · exact ⟨Case0101.certificate⟩
  · exact ⟨Case0102.certificate⟩

theorem mixed_rows : ∀ row ∈ oneSixCases, Nonempty (MixedRowCertificate row) := by
  intro row hrow
  simp only [oneSixCases, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Case0000.certificate⟩
  · exact ⟨Case0001.certificate⟩
  · exact ⟨Case0002.certificate⟩
  · exact ⟨Case0003.certificate⟩
  · exact ⟨Case0004.certificate⟩
  · exact ⟨Case0005.certificate⟩
  · exact ⟨Case0006.certificate⟩
  · exact ⟨Case0007.certificate⟩
  · exact ⟨Case0008.certificate⟩
  · exact ⟨Case0009.certificate⟩
  · exact ⟨Case0010.certificate⟩
  · exact ⟨Case0011.certificate⟩
  · exact ⟨Case0012.certificate⟩
  · exact ⟨Case0013.certificate⟩
  · exact ⟨Case0014.certificate⟩
  · exact ⟨Case0015.certificate⟩
  · exact ⟨Case0016.certificate⟩
  · exact ⟨Case0017.certificate⟩
  · exact ⟨Case0018.certificate⟩
  · exact ⟨Case0019.certificate⟩
  · exact ⟨Case0020.certificate⟩
  · exact ⟨Case0021.certificate⟩
  · exact ⟨Case0022.certificate⟩
  · exact ⟨Case0023.certificate⟩
  · exact ⟨Case0024.certificate⟩
  · exact ⟨Case0025.certificate⟩
  · exact ⟨Case0026.certificate⟩
  · exact ⟨Case0027.certificate⟩
  · exact ⟨Case0028.certificate⟩
  · exact ⟨Case0029.certificate⟩
  · exact ⟨Case0030.certificate⟩
  · exact ⟨Case0031.certificate⟩
  · exact ⟨Case0032.certificate⟩
  · exact ⟨Case0033.certificate⟩

/-- Every possible square-pyramid count for canonical template 13. -/
theorem two_six_thirteen_rows (s : Fin 8) :
    Nonempty (TwoSixCertificate 13 s) := by
  fin_cases s
  · exact ⟨Case0470.certificate⟩
  · exact ⟨Case0471.certificate⟩
  · exact ⟨Case0472.certificate⟩
  · exact ⟨Case0473.certificate⟩
  · exact ⟨Case0474.certificate⟩
  · exact ⟨Case0475.certificate⟩
  · exact ⟨Case0476.certificate⟩
  · exact ⟨Case0477.certificate⟩

theorem pure_complete (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SevenPureCase P) : HasClassifiedEncoding P := by
  obtain ⟨D⟩ := pure_rows C.row C.row_mem
  exact pure_of_certificate P hP C D

theorem mixed_complete (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SevenMixedCase P) : HasClassifiedEncoding P := by
  obtain ⟨D⟩ := mixed_rows C.row C.row_mem
  exact mixed_of_certificate P hP C D


/-- The template equality is supplied by the geometric surplus theorem. -/
theorem two_six_thirteen_complete (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SevenTwoSixCase P) (hC : C.template = 13) : HasClassifiedEncoding P := by
  obtain ⟨D⟩ := two_six_thirteen_rows C.squarePyramids
  apply two_six_of_certificate P hP C
  simpa only [hC] using D

#print axioms pure_complete
#print axioms mixed_complete
#print axioms two_six_thirteen_complete

end Papers.RationalityTen.CompletedSeven
