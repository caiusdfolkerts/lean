module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Finset.Card

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Rank bound for finitely supported zero-sum vectors -/

namespace Unimodular.IncidenceRank

theorem dimension_lt_support_card {K V : Type*}
    [CommRing K] [Nontrivial K] [StrongRankCondition K] [DecidableEq V] {n : ℕ}
    (L : (Fin n → K) →ₗ[K] (V → K)) (hinj : Function.Injective L)
    (t : Finset V) (a : V) (ha : a ∈ t)
    (hsupport : ∀ x v, v ∉ t → L x v = 0)
    (hsum : ∀ x, ∑ v ∈ t, L x v = 0) : n < t.card := by
  let P : (Fin n → K) →ₗ[K] ((t.erase a) → K) :=
    { toFun := fun x v ↦ L x v
      map_add' := by intro x y; ext v; simp
      map_smul' := by intro c x; ext v; simp }
  have hp : Function.Injective P := by
    intro x y hxy
    apply hinj
    funext v
    by_cases hv : v ∈ t
    · by_cases hva : v = a
      · subst v
        have hrest : (∑ w ∈ t.erase a, L x w) = ∑ w ∈ t.erase a, L y w := by
          apply Finset.sum_congr rfl
          intro w hw
          exact congrFun hxy ⟨w, hw⟩
        have hx : (∑ w ∈ t.erase a, L x w) + L x a = 0 := by
          rw [Finset.sum_erase_add _ _ ha]
          exact hsum x
        have hy : (∑ w ∈ t.erase a, L y w) + L y a = 0 := by
          rw [Finset.sum_erase_add _ _ ha]
          exact hsum y
        rw [hrest] at hx
        exact add_left_cancel (hx.trans hy.symm)
      · exact congrFun hxy ⟨v, Finset.mem_erase.mpr ⟨hva, hv⟩⟩
    · rw [hsupport x v hv, hsupport y v hv]
  have hdim := LinearMap.finrank_le_finrank_of_injective hp
  have hcard : n ≤ (t.erase a).card := by simpa using hdim
  have herase := Finset.card_erase_add_one ha
  omega

#print axioms dimension_lt_support_card
end Unimodular.IncidenceRank
