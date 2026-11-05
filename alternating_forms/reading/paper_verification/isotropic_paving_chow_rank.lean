module

public import PaperVerification.BoundedFinitePavingChowRank
public import PaperVerification.IsotropicProjectivePresentation
public import PaperVerification.IsotropicAttractingClosedCells
public import PaperVerification.IsotropicAttractingCanonicalComparison
public import PaperVerification.IsotropicAttractingCellBudget
public import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective

/-!
# The complete actual Chow-rank bound for the common-isotropic scheme

The strata and all the maps below are those of the original homogeneous
quotient.  The finite-dimensionality conclusion is derived from genuine
closed/open localization and the actual affine-space Chow calculation.
No cycle-class comparison, Chern-class relation, or abstract ring model is
assumed in this argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory MvPolynomial
open AlternatingForms IsotropicAttractingCoordinates TotalChow
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equality of the literal homogeneous ideals transports the actual
Chow groups, including their structural morphisms. -/
theorem homogeneousQuotient_total_rank_congr {σ : Type}
    (I J : Ideal (MvPolynomial σ ℂ))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ ℂ)) (h : I = J)
    [AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading I hI))]
    [AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading J hJ))]
    (b : ℕ) :
    (Module.Finite ℚ (TotalChowQ (HomogeneousQuotientCharts.structureMap I hI)) ∧
      Module.finrank ℚ (TotalChowQ (HomogeneousQuotientCharts.structureMap I hI)) ≤ b) ↔
    (Module.Finite ℚ (TotalChowQ (HomogeneousQuotientCharts.structureMap J hJ)) ∧
      Module.finrank ℚ (TotalChowQ (HomogeneousQuotientCharts.structureMap J hJ)) ≤ b) := by
  subst J
  rfl

/-- The complete dimension-graded Chow group is finite dimensional and
has rank at most the number of independent coordinate pivots. Every
stratum is included, and the filtration terminates at the empty scheme. -/
theorem chain_total_chow_rank (k t : ℕ) (hs : t+2 ≤ k+1) :
    letI := chain_isNoetherian k t hs
    Module.Finite ℚ (TotalChowQ
      (isotropicStructureMap (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))) ∧
      Module.finrank ℚ (TotalChowQ
        (isotropicStructureMap (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))) ≤
        Nat.choose (2*k+2-(t+2)) (t+2) := by
  classical
  letI := chain_isNoetherian k t hs
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  let N := pivotCount (t+2) (2*k+1)
  let stage (m : ℕ) := filtrationScheme (K := ℂ)
    (pivotPrefix (t+2) (2*k+1) m) (2*k+1) (2*k)
  let base (m : ℕ) : stage m ⟶ complexBase :=
    filtrationStructureMap (pivotPrefix (t+2) (2*k+1) m) (2*k+1) (2*k)
  let presentation (m : ℕ) := HomogeneousQuotientProjective.projectivePresentation
    (filtrationIdeal (K := ℂ) (pivotPrefix (t+2) (2*k+1) m) (2*k+1) (2*k))
    (filtrationIdeal_isHomogeneous _ _ _)
  letI : ∀ m, AlgebraicGeometry.IsNoetherian (stage m) :=
    fun m => (presentation m).isNoetherian
  letI : ∀ m, LocallyOfFiniteType (base m) :=
    fun m => (presentation m).finiteType.1
  let closed (m : ℕ) : stage (m+1) ⟶ stage m :=
    filtrationInclusion (pivotPrefix_mono (t+2) (2*k+1) (Nat.le_succ m)) (2*k+1) (2*k)
  letI : ∀ m, IsClosedImmersion (closed m) := fun m =>
    filtrationInclusion_isClosedImmersion _ _ _
  let cell (m : ℕ) (hm : m < N) : (stage m).Opens :=
    filtrationChart (pivotPrefix (t+2) (2*k+1) m)
      (weightOrderedPivots (t+2) (2*k+1) ⟨m,hm⟩) (2*k+1) (2*k)
  have hover (m : ℕ) : closed m ≫ base m = base (m+1) :=
    filtrationInclusion_over _ _ _
  have hcomplement (m : ℕ) (hm : m < N) :
      Set.range (closed m) = (Set.range (cell m hm).ι)ᶜ := by
    dsimp only [cell]
    exact orderedFiltration_closed_open_complement (K := ℂ) ⟨m,hm⟩ (2*k+1) (2*k)
  have hempty : IsEmpty (stage N) := by
    refine ⟨fun x => ?_⟩
    have hx : filtrationToOriginal (K := ℂ) (pivotPrefix (t+2) (2*k+1) N)
        (2*k+1) (2*k) x ∈ Set.range
          (filtrationToOriginal (K := ℂ) (pivotPrefix (t+2) (2*k+1) N) (2*k+1) (2*k)) :=
      ⟨x,rfl⟩
    rw [filtration_image_final] at hx
    exact hx
  have hcell (m : ℕ) (hm : m < N) :
      Module.Finite ℚ (TotalChowQ ((cell m hm).ι ≫ base m)) ∧
        Module.finrank ℚ (TotalChowQ ((cell m hm).ι ≫ base m)) ≤ cellBudget k (t+2) m := by
    dsimp only [cell]
    let i : Fin N := ⟨m,hm⟩
    let p := weightOrderedPivots (t+2) (2*k+1) i
    let E := pivotPrefix (t+2) (2*k+1) m
    have hE : EarlierSet p E := pivotPrefix_earlier _ _ i
    by_cases hp : IndependentPivots (indexEmbedding p)
    · have h := finite_and_finrank_le_one_of_polynomialIso
        ((filtrationChart (K := ℂ) E p (2*k+1) (2*k)).ι ≫ base m)
        {v : Coordinate (indexEmbedding p) // v ∉ Set.range (pivotEmbedding hp)}
        (filtrationChartIsoAffine E p hE hp)
        (filtrationChartIsoAffine_hom_over E p hE hp)
      have hb : cellBudget k (t+2) m = 1 := by
        unfold cellBudget
        rw [dif_pos hm]
        exact if_pos hp
      rw [hb]
      exact h
    · letI := filtrationChart_isEmpty_of_not_independent (K := ℂ) E p hE hp
      have h := finite_and_finrank_eq_zero_of_empty
        ((filtrationChart (K := ℂ) E p (2*k+1) (2*k)).ι ≫ base m)
      refine ⟨h.1,?_⟩
      rw [h.2]
      exact Nat.zero_le _
  have h := boundedFinitePaving_total_rank stage base closed hover N cell hcomplement hempty
    (cellBudget k (t+2)) hcell
  rw [sum_cellBudget k (t+2) hs] at h
  have hI : filtrationIdeal (K := ℂ) (pivotPrefix (t+2) (2*k+1) 0) (2*k+1) (2*k) =
      isotropicPluckerIdeal (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)) := by
    simp only [filtrationIdeal, pivotPrefix_zero, Set.image_empty, Ideal.span_empty, sup_bot_eq]
  letI := (presentation 0).isNoetherian
  letI : AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading
      (isotropicPluckerIdeal (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))
      (isotropicPluckerIdeal_isHomogeneous _))) :=
    (chainProjectivePresentation k t hs).isNoetherian
  exact (homogeneousQuotient_total_rank_congr
    (filtrationIdeal (K := ℂ) (pivotPrefix (t+2) (2*k+1) 0) (2*k+1) (2*k))
    (isotropicPluckerIdeal (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))
    (filtrationIdeal_isHomogeneous _ _ _)
    (isotropicPluckerIdeal_isHomogeneous _) hI _).mp h

end PaperVerification.IsotropicAttractingCharts
