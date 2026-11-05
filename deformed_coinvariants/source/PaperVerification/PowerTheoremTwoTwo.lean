module

public import PaperVerification.PowerSumComparator
public import PaperVerification.PowerOriginalHilbert

/-!
# All clauses of Theorem 2.2

This statement records the literal monomial basis, the exact Hilbert polynomial,
the original-field graded representation comparison for every coefficient
stabilizer subgroup, the equal-coefficient power-sum alternative, and all the
same conclusions for the original operator family under condition (2.3).

The only abbreviation in the statement means existence of an actual
representation equivalence identifying every homogeneous piece.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation Module
open scoped BigOperators

namespace PaperVerification

def GradedRepresentationEquivalent
    {K G V W : Type*} [Semiring K] [Monoid G]
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (A : ℕ → Submodule K V) (B : ℕ → Submodule K W) : Prop :=
  ∃ e : ρ.Equiv σ, ∀ d x, x ∈ A d ↔ e x ∈ B d

theorem gradedRepresentationEquivalent_of_preserves_both
    {K G V W : Type*} [Semiring K] [Monoid G]
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    {A : ℕ → Submodule K V} {B : ℕ → Submodule K W}
    (h : ∃ e : ρ.Equiv σ,
      (∀ d x, x ∈ A d → e x ∈ B d) ∧
      (∀ d y, y ∈ B d → e.symm y ∈ A d)) :
    GradedRepresentationEquivalent ρ σ A B := by
  obtain ⟨e,he,he'⟩ := h
  refine ⟨e,fun d x => ⟨he d x,?_⟩⟩
  intro hx
  have h' := he' d (e x) hx
  change e.toLinearEquiv.symm (e.toLinearEquiv x) ∈ A d at h'
  simpa only [LinearEquiv.symm_apply_apply] using h'

namespace PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- Every printed conclusion of Theorem 2.2, for every field and every
positive tail index, under its exact unbounded nonresonance condition. -/
theorem paper_theorem_2_2
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m) :
    (∃ B : Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ tailHit c lam m),
      ∀ a, B a = (tailHit c lam m).mkQ (monomial a.val 1)) ∧
    (GradedHilbert.series (tailQuotientGrading c lam m) =
      ((∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j : Polynomial ℤ) : PowerSeries ℤ)) ∧
    (∀ (G : Subgroup (Equiv.Perm (Fin n)))
      (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i),
      GradedRepresentationEquivalent (tailQuotientAction G c lam m hfix)
        (completeHomogeneousAction G m) (tailQuotientDegree c lam m)
        (ordinaryQuotientDegree (completeHomogeneousFamily K n m))) ∧
    (∀ a : K, (∀ i, c i = a) → ∀ G : Subgroup (Equiv.Perm (Fin n)),
      GradedRepresentationEquivalent
        (tailQuotientAction G (fun _ : Fin n => a) lam m (fun _ _ => rfl))
        (powerSumAction G m) (tailQuotientDegree (fun _ : Fin n => a) lam m)
        (ordinaryQuotientDegree (powerSumFamily K n m))) ∧
    (∀ hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0,
      (∃ B : Basis (ArtinIndex n m) K
          (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m),
        ∀ a, B a = (originalTailHit c lam m).mkQ (monomial a.val 1)) ∧
      (GradedHilbert.series
          (originalTailQuotientGrading c lam m (coordinate_factor_ne_zero hnr hlow)) =
        ((∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j : Polynomial ℤ) : PowerSeries ℤ)) ∧
      (∀ (G : Subgroup (Equiv.Perm (Fin n)))
        (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i),
        GradedRepresentationEquivalent (originalTailQuotientAction G c lam m hfix)
          (completeHomogeneousAction G m) (originalTailQuotientDegree c lam m)
          (ordinaryQuotientDegree (completeHomogeneousFamily K n m))) ∧
      (∀ a : K, (∀ i, c i = a) → ∀ G : Subgroup (Equiv.Perm (Fin n)),
        GradedRepresentationEquivalent
          (originalTailQuotientAction G (fun _ : Fin n => a) lam m (fun _ _ => rfl))
          (powerSumAction G m) (originalTailQuotientDegree (fun _ : Fin n => a) lam m)
          (ordinaryQuotientDegree (powerSumFamily K n m)))) := by
  refine ⟨paper_theorem_2_2_monomial_basis c lam m hm hnr,
    paper_theorem_2_2_hilbert_polynomial c lam m hm hnr,?_,?_,?_⟩
  · intro G hfix
    exact gradedRepresentationEquivalent_of_preserves_both
      (paper_theorem_2_2_graded_representation c lam m hm hnr G hfix)
  · intro a hc G
    have he : c = fun _ => a := funext hc
    subst c
    exact gradedRepresentationEquivalent_of_preserves_both
      (paper_theorem_2_2_equal_coefficient_power_sums a lam m hm hnr G)
  · intro hlow
    refine ⟨paper_theorem_2_2_original_monomial_basis c lam m hm hnr hlow,
      paper_theorem_2_2_original_hilbert_polynomial c lam m hm hnr hlow,?_,?_⟩
    · intro G hfix
      exact gradedRepresentationEquivalent_of_preserves_both
        (paper_theorem_2_2_original_graded_representation c lam m hm hnr hlow G hfix)
    · intro a hc G
      have he : c = fun _ => a := funext hc
      subst c
      exact gradedRepresentationEquivalent_of_preserves_both
        (paper_theorem_2_2_original_equal_coefficient_power_sums a lam m hm hnr hlow G)

end PowerOperators
end PaperVerification
