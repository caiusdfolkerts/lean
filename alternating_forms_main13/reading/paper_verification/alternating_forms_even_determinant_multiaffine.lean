module

public import PaperVerification.AlternatingFormsEvenDeterminantProducts
public import Mathlib.Data.Sigma.Basic

/-!
# Multiaffinity of products on disjoint odd subsets

Every determinant uses a variable at most once.  When its column sets are
disjoint from the column sets of the other factors, their product is still
multiaffine.  The coefficients of the two forms remain arbitrary throughout.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms.EvenDeterminants

open scoped BigOperators

variable {K α τ : Type*} [CommRing K] [Nontrivial K]

theorem termVariables_degreeOf_eq_zero (r : ℕ) (a : OddRows r → α)
    (σ : Equiv.Perm (OddRows r)) (x : α) (hx : ∀ j, x ≠ a j) :
    (termVariables (K := K) r a σ).degreeOf x = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  have hp := MvPolynomial.degreeOf_prod_le x Finset.univ
    (fun i : Fin r => (MvPolynomial.X (a (σ (Sum.inr i))) : MvPolynomial α K))
  change (termVariables r a σ).degreeOf x ≤ _ at hp
  simpa [MvPolynomial.degreeOf_X, hx] using hp

theorem oddSubsetDeterminant_degreeOf_le_one (r : ℕ) (b c : α → K)
    (a : OddRows r → α) (ha : Function.Injective a) (x : α) :
    (oddSubsetDeterminant r b c a).degreeOf x ≤ 1 := by
  classical
  rw [oddSubsetDeterminant_expansion]
  apply (MvPolynomial.degreeOf_sum_le x Finset.univ _).trans
  apply Finset.sup_le
  intro σ hσ
  apply (MvPolynomial.degreeOf_C_mul_le _ x _).trans
  exact termVariables_degreeOf_le_one r a ha σ x

theorem oddSubsetDeterminant_degreeOf_eq_zero (r : ℕ) (b c : α → K)
    (a : OddRows r → α) (x : α) (hx : ∀ j, x ≠ a j) :
    (oddSubsetDeterminant r b c a).degreeOf x = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  rw [oddSubsetDeterminant_expansion]
  apply (MvPolynomial.degreeOf_sum_le x Finset.univ _).trans
  apply Finset.sup_le
  intro σ hσ
  apply (MvPolynomial.degreeOf_C_mul_le _ x _).trans
  exact (termVariables_degreeOf_eq_zero r a σ x hx).le

/-- Disjointness of the literal column labels, including injectivity within
each factor, is precisely the hypothesis used for multiaffinity. -/
theorem determinantProduct_degreeOf_le_one [Fintype τ] (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m)
    (hinj : Function.Injective (fun p : (a : τ) × Fin (2 * r a + 1) => I p.1 p.2))
    (b c : Fin m → K) (x : Fin m) :
    (determinantProduct m r I b c).degreeOf x ≤ 1 := by
  classical
  let D (a : τ) := oddSubsetDeterminant (r a) b c
    (fun j => I a (rowPosition (r a) j))
  have hp := MvPolynomial.degreeOf_prod_le x Finset.univ D
  change (determinantProduct m r I b c).degreeOf x ≤ ∑ a, (D a).degreeOf x at hp
  have hwithin (a : τ) : Function.Injective (I a) := by
    intro i j hij
    exact sigma_mk_injective (β := fun a : τ => Fin (2 * r a + 1))
      (i := a) (hinj (show I a i = I a j from hij))
  by_cases hx : ∃ a i, I a i = x
  · obtain ⟨a₀, i₀, hi₀⟩ := hx
    have hz (a : τ) (ha : a ≠ a₀) : (D a).degreeOf x = 0 := by
      apply oddSubsetDeterminant_degreeOf_eq_zero
      intro j hj
      have he : (⟨a, rowPosition (r a) j⟩ : (a : τ) × Fin (2 * r a + 1)) =
          ⟨a₀, i₀⟩ := hinj (hj.symm.trans hi₀.symm)
      exact ha (congrArg Sigma.fst he)
    have hs : (∑ a, (D a).degreeOf x) = (D a₀).degreeOf x := by
      apply Finset.sum_eq_single a₀
      · intro a ha hne
        exact hz a hne
      · simp
    rw [hs] at hp
    exact hp.trans (oddSubsetDeterminant_degreeOf_le_one (r a₀) b c _
      ((hwithin a₀).comp (rowPosition_injective (r a₀))) x)
  · have hz (a : τ) : (D a).degreeOf x = 0 := by
      apply oddSubsetDeterminant_degreeOf_eq_zero
      intro j hj
      exact hx ⟨a, rowPosition (r a) j, hj.symm⟩
    exact hp.trans (by simp only [hz, Finset.sum_const_zero]; exact Nat.zero_le 1)

end PaperVerification.AlternatingForms.EvenDeterminants
