module

public import PaperVerification.PowerOriginalAction
public import PaperVerification.PowerRepresentationTheorem

/-!
# The graded comparison for the original power operators

The genuine diagonal quotient equivalence is equivariant and preserves every
homogeneous piece. Composing it with the reversed-family comparison transfers
the complete graded representation statement under precisely condition (2.3).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem paper_theorem_2_2_original_graded_representation
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    ∃ e : (originalTailQuotientAction G c lam m hfix).Equiv (completeHomogeneousAction G m),
      (∀ d x, x ∈ originalTailQuotientDegree c lam m d →
        e x ∈ ordinaryQuotientDegree (completeHomogeneousFamily K n m) d) ∧
      (∀ d y, y ∈ ordinaryQuotientDegree (completeHomogeneousFamily K n m) d →
        e.symm y ∈ originalTailQuotientDegree c lam m d) := by
  obtain ⟨e,he,he'⟩ := paper_theorem_2_2_graded_representation c lam m hm hnr G hfix
  let h := coordinate_factor_ne_zero hnr hlow
  refine ⟨(diagonalQuotientRepresentationEquiv G c lam m h hfix).trans e,?_,?_⟩
  · intro d x hx
    exact he d _ (diagonalQuotientEquiv_preserves_degree c lam m h d hx)
  · intro d y hy
    exact diagonalQuotientEquiv_symm_preserves_degree c lam m h d (he' d y hy)

end PaperVerification.PowerOperators
