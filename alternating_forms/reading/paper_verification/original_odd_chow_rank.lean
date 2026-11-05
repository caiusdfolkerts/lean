module

public import PaperVerification.IsotropicPavingChowRank

/-!
# The Chow-rank bound in the paper's literal coordinates

The attracting chart calculation uses the displayed permutation to the
anti-diagonal pencil. This file transports its actual Chow groups back to
both the Section 4 forms and the literal path pencil (2). The latter two
pencils generate exactly the same homogeneous ideal.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory MvPolynomial
open AlternatingForms TotalChow
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionFour_isNoetherian (k t : ℕ) (hs : t+2 ≤ k+1) :
    AlgebraicGeometry.IsNoetherian (Proj (isotropicProjectiveGrading (t := t)
      (sectionFourPluckerForms (K := ℂ) k))) := by
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  exact (HomogeneousQuotientProjective.projectivePresentation
    (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := ℂ) k))
    (isotropicPluckerIdeal_isHomogeneous _)).isNoetherian

theorem originalOdd_isNoetherian (k t : ℕ) (hs : t+2 ≤ k+1) :
    AlgebraicGeometry.IsNoetherian (Proj (isotropicProjectiveGrading (t := t)
      (oddPluckerForms (K := ℂ) k))) := by
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  exact (HomogeneousQuotientProjective.projectivePresentation
    (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := ℂ) k))
    (isotropicPluckerIdeal_isHomogeneous _)).isNoetherian

/-- The complete genuine Chow group of the Section 4 scheme. -/
theorem sectionFour_total_chow_rank (k t : ℕ) (hs : t+2 ≤ k+1) :
    letI := sectionFour_isNoetherian k t hs
    Module.Finite ℚ (TotalChowQ (isotropicStructureMap (t := t)
      (sectionFourPluckerForms (K := ℂ) k))) ∧
      Module.finrank ℚ (TotalChowQ (isotropicStructureMap (t := t)
        (sectionFourPluckerForms (K := ℂ) k))) ≤
          Nat.choose (2*k+2-(t+2)) (t+2) := by
  letI := sectionFour_isNoetherian k t hs
  letI := chain_isNoetherian k t hs
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  letI : LocallyOfFiniteType (isotropicStructureMap (t := t)
      (sectionFourPluckerForms (K := ℂ) k)) :=
    (HomogeneousQuotientProjective.projectivePresentation
      (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := ℂ) k))
      (isotropicPluckerIdeal_isHomogeneous _)).finiteType.1
  letI : LocallyOfFiniteType (isotropicStructureMap (t := t)
      (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k))) :=
    (chainProjectivePresentation k t hs).finiteType.1
  let C := totalChowEquiv (chainSectionFourIso (K := ℂ) k t) _ _
    (chainSectionFourIso_hom_over k t)
  have h := chain_total_chow_rank k t hs
  letI := h.1
  exact ⟨Module.Finite.equiv C,C.finrank_eq.symm.trans_le h.2⟩

/-- The same rank bound for the literal original path pencil (2), with
all genuine algebraic cycles and all gradings retained. -/
theorem originalOdd_total_chow_rank (k t : ℕ) (hs : t+2 ≤ k+1) :
    letI := originalOdd_isNoetherian k t hs
    Module.Finite ℚ (TotalChowQ (isotropicStructureMap (t := t)
      (oddPluckerForms (K := ℂ) k))) ∧
      Module.finrank ℚ (TotalChowQ (isotropicStructureMap (t := t)
        (oddPluckerForms (K := ℂ) k))) ≤
          Nat.choose (2*k+2-(t+2)) (t+2) := by
  letI := originalOdd_isNoetherian k t hs
  letI := sectionFour_isNoetherian k t hs
  letI : AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading
      (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := ℂ) k))
      (isotropicPluckerIdeal_isHomogeneous _))) := sectionFour_isNoetherian k t hs
  letI : AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading
      (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := ℂ) k))
      (isotropicPluckerIdeal_isHomogeneous _))) := originalOdd_isNoetherian k t hs
  exact (homogeneousQuotient_total_rank_congr
    (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := ℂ) k))
    (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := ℂ) k))
    (isotropicPluckerIdeal_isHomogeneous _) (isotropicPluckerIdeal_isHomogeneous _)
    (sectionFour_isotropicPluckerIdeal k t) _).mp (sectionFour_total_chow_rank k t hs)

end PaperVerification.IsotropicAttractingCharts
