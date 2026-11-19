module
public import theorem12
@[expose] public section
noncomputable section
namespace FourPapers.Universal
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 600000
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {K X Y X' Y' : Type u} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup X'] [Module K X'] [AddCommGroup Y'] [Module K Y']
variable {P : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
theorem koszulGradedHomologyComparison_formula (i n : ℕ) :
    ∃ hin hout, koszulGradedHomologyComparison K hs d hrank i n =
      chainHomologyEquiv _ _ _ _ _ _
    (koszulGradeComparison K hs d hrank (i + 1) n)
    (koszulGradeComparison K hs d hrank i n)
    (koszulGradeComparison K hs d hrank (i - 1) n) hin hout := by
  exact ⟨(gradeEquiv_commutes _ _ _ _ _ _ _ _ _ _
      (originalKoszulCoefficientEquiv_filtered K hs d hrank (i + 1))
      (originalKoszulCoefficientEquiv_filtered K hs d hrank i)
      (coefficientEquiv_incoming_commutes K hs d hrank i) n), (gradeEquiv_commutes _ _ _ _ _ _ _ _ _ _
      (originalKoszulCoefficientEquiv_filtered K hs d hrank i)
      (originalKoszulCoefficientEquiv_filtered K hs d hrank (i - 1))
      (coefficientEquiv_outgoing_commutes K hs d hrank i) n), rfl⟩
end FourPapers.Universal
