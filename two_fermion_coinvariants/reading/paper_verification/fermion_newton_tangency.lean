module

public import PaperVerification.FermionNewtonLocalNumerators

/-!
# The positive-edge tangency of the actual Newton columns

An earlier positive vertex supplies a numerator factor. On an active positive
edge, compatibility keeps both endpoints active and their specialized
numerators and denominators agree. These two cases establish tangency in the
original common-numerator module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

theorem identifyCoordinates_starDenominator_ne_zero_of_avoids
    (a b k : Fin n) (hab : a ≠ b) (T : Finset (Fin n)) (hself : k ∉ T)
    (hp : ∀ j ∈ T, ¬ (k = a ∧ j = b) ∧ ¬ (k = b ∧ j = a)) :
    identifyCoordinates (F := F) a b (starDenominator k T) ≠ 0 := by
  rw [starDenominator, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact identifyCoordinates_star_ne_zero a b k j hab
    (fun h ↦ hself (by simpa only [h] using hj)) (hp j hj)

theorem clearedFractionNumerator_eval_zero_of_numerator
    (φ : P (F := F) (n := n) →+* (P (F := F) (n := n))) (Q N D : P (F := F) (n := n)) (hD : D ∣ Q)
    (hN : φ N = 0) (hD0 : φ D ≠ 0) : φ (clearedFractionNumerator Q N D hD) = 0 := by
  have h := congrArg φ (clearedFractionNumerator_relation Q N D hD)
  simp only [map_mul, hN, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hD0

theorem columnCommonNumerator_eval_zero_of_numerator
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) (φ : P (F := F) (n := n) →+* (P (F := F) (n := n)))
    (hN : φ ((columnNumerator δ σ i).eval (X k)) = 0)
    (hactive : k ∈ activeInterval δ i → φ (starDenominator k (earlierNegative σ i)) ≠ 0)
    (hpole : k ∈ earlierNegative σ i → ∀ l ∈ activeInterval δ i,
      φ (starDenominator k ((earlierNegative σ i).erase k) * (X k - X l)) ≠ 0) :
    φ (columnCommonNumerator β δ σ hc i k) = 0 := by
  by_cases ha : k ∈ activeInterval δ i
  · rw [columnCommonNumerator_eq_active β δ σ hc i k ha]
    exact clearedFractionNumerator_eval_zero_of_numerator φ _ _ _ _ hN (hactive ha)
  · by_cases hn : k ∈ earlierNegative σ i
    · rw [columnCommonNumerator_eq_residue_sum β δ σ hc i k hn, map_sum]
      apply Finset.sum_eq_zero
      intro l hl
      rw [map_mul]
      unfold residueNumerator
      rw [clearedFractionNumerator_eval_zero_of_numerator φ _ _ _ _ hN
        (hpole hn l.val l.property), mul_zero]
    · rw [columnCommonNumerator_eq_zero_of_outside β δ σ hc i k ha hn, map_zero]

theorem activeInterval_lower_closed
    (δ : Fin n → ℕ) (i a b : Fin n) (hia : i ≤ a) (hab : a ≤ b)
    (hb : b ∈ activeInterval δ i) : a ∈ activeInterval δ i := by
  rcases (mem_activeInterval _ _ _).mp hb with ⟨_,h⟩
  exact (mem_activeInterval _ _ _).mpr ⟨hia, fun j hij hja ↦ h j hij (hja.trans hab)⟩

theorem identifyCoordinates_columnNumerator_earlier_positive
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i a b : Fin n)
    (hab : a ≠ b) (ha : a ∈ earlierPositive σ i) :
    identifyCoordinates (F := F) a b ((columnNumerator δ σ i).eval (X b)) = 0 := by
  rw [columnNumerator, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_prod, map_mul]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hprod : identifyCoordinates (F := F) a b
      (∏ j ∈ earlierPositive σ i, (X b - X j)) = 0 := by
    rw [map_prod]
    apply Finset.prod_eq_zero ha
    simp only [map_sub, identifyCoordinates_X, if_neg (Ne.symm hab), if_pos rfl, if_true, sub_self]
  rw [hprod, mul_zero]

theorem identifyCoordinates_poly_eval_eq
    (a b : Fin n) (hab : a ≠ b) (N : Polynomial (P (F := F) (n := n))) :
    identifyCoordinates a b (N.eval (X a)) = identifyCoordinates a b (N.eval (X b)) := by
  change (identifyCoordinates a b).toRingHom (N.eval (X a)) =
    (identifyCoordinates a b).toRingHom (N.eval (X b))
  rw [← Polynomial.eval_map_apply, ← Polynomial.eval_map_apply]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, identifyCoordinates_X,
    if_pos rfl, if_true, if_neg (Ne.symm hab)]

theorem identifyCoordinates_starDenominator_eq
    (a b : Fin n) (hab : a ≠ b) (T : Finset (Fin n)) :
    identifyCoordinates (F := F) a b (starDenominator a T) =
      identifyCoordinates a b (starDenominator b T) := by
  simp only [starDenominator, map_prod, map_sub]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [identifyCoordinates_X, if_pos rfl, if_true, if_neg (Ne.symm hab)]

theorem columnCommonNumerator_positive_dvd
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i : Fin n) (e : Edge n) (he : σ e.1.1 = 1) :
    edgeLinear e ∣ columnCommonNumerator β δ σ hc i e.1.1 -
      columnCommonNumerator β δ σ hc i e.1.2 := by
  rcases e with ⟨⟨a,b⟩,hab⟩
  change σ a = 1 at he
  let φ := (identifyCoordinates (F := F) a b).toRingHom
  apply (identifyCoordinates_eq_zero_iff a b (ne_of_lt hab) _).mp
  change φ (_ - _) = 0
  rw [map_sub, sub_eq_zero]
  have haN : a ∉ earlierNegative σ i := by
    intro h
    have hσ := ((mem_earlierNegative σ i a).mp h).2
    omega
  by_cases hai : a < i
  · have haA : a ∉ activeInterval δ i := by
      intro h
      exact (not_lt_of_ge ((mem_activeInterval δ i a).mp h).1) hai
    rw [columnCommonNumerator_eq_zero_of_outside β δ σ hc i a haA haN, map_zero]
    apply Eq.symm
    apply columnCommonNumerator_eval_zero_of_numerator β δ σ hc i b φ
    · exact identifyCoordinates_columnNumerator_earlier_positive δ σ i a b (ne_of_lt hab)
        ((mem_earlierPositive σ i a).mpr ⟨hai,he⟩)
    · intro hbA
      apply identifyCoordinates_starDenominator_ne_zero_of_avoids a b b (ne_of_lt hab) _
        (fun hbN ↦ Finset.disjoint_left.mp (activeInterval_disjoint_earlierNegative δ σ i) hbA hbN)
      intro j hj
      exact ⟨fun h ↦ (ne_of_gt hab) h.1, fun h ↦ haN (h.2 ▸ hj)⟩
    · intro hbN l hl
      rw [map_mul]
      apply mul_ne_zero
      · apply identifyCoordinates_starDenominator_ne_zero_of_avoids a b b (ne_of_lt hab) _
          (Finset.notMem_erase b _)
        intro j hj
        exact ⟨fun h ↦ (ne_of_gt hab) h.1,
          fun h ↦ haN (h.2 ▸ (Finset.mem_erase.mp hj).2)⟩
      · have hbl : b < l := ((mem_earlierNegative σ i b).mp hbN).1.trans_le
          ((mem_activeInterval δ i l).mp hl).1
        apply identifyCoordinates_star_ne_zero a b b l (ne_of_lt hab) (ne_of_lt hbl)
        refine ⟨fun h ↦ (ne_of_gt hab) h.1, ?_⟩
        intro h
        have hia := ((mem_activeInterval δ i l).mp hl).1
        rw [h.2] at hia
        exact (not_lt_of_ge hia) hai
  · have hia : i ≤ a := le_of_not_gt hai
    have hbN : b ∉ earlierNegative σ i := by
      intro h
      exact (not_lt_of_ge (hia.trans hab.le)) ((mem_earlierNegative σ i b).mp h).1
    by_cases haA : a ∈ activeInterval δ i
    · have hbA := activeInterval_closed_positive δ σ hc i a b haA hab he
      rw [columnCommonNumerator_eq_active β δ σ hc i a haA,
        columnCommonNumerator_eq_active β δ σ hc i b hbA]
      apply numerator_evaluations_eq_of_fraction_data φ
        (negativeDenominator σ) ((columnNumerator δ σ i).eval (X a))
        ((columnNumerator δ σ i).eval (X b))
        (starDenominator a (earlierNegative σ i))
        (starDenominator b (earlierNegative σ i)) _ _
        (clearedFractionNumerator_relation _ _ _ _) (clearedFractionNumerator_relation _ _ _ _)
      · apply identifyCoordinates_starDenominator_ne_zero_of_avoids a b a (ne_of_lt hab) _ haN
        intro j hj
        exact ⟨fun h ↦ hbN (h.2 ▸ hj), fun h ↦ (ne_of_lt hab) h.1⟩
      · exact identifyCoordinates_starDenominator_eq a b (ne_of_lt hab) _
      · exact identifyCoordinates_poly_eval_eq a b (ne_of_lt hab) _
    · have hbA : b ∉ activeInterval δ i := fun hb ↦
        haA (activeInterval_lower_closed δ i a b hia hab.le hb)
      rw [columnCommonNumerator_eq_zero_of_outside β δ σ hc i a haA haN,
        columnCommonNumerator_eq_zero_of_outside β δ σ hc i b hbA hbN]

end PaperVerification.Fermion.Newton
