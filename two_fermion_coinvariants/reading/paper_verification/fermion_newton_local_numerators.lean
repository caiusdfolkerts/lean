module

public import PaperVerification.FermionNewtonHyperplaneEvaluation

/-!
# Explicit numerator terms and the off-pair normal conditions

The chosen common numerator is identified with the polynomial quotients
clearing each actual denominator. For a negative hyperplane, every row outside
its two endpoints has only denominators that remain nonzero after restriction;
its numerator is therefore divisible by that hyperplane equation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

def clearedFractionNumerator (Q N D : P (F := F) (n := n)) (hD : D ∣ Q) : P (F := F) (n := n) :=
  Classical.choose hD * N

theorem clearedFractionNumerator_relation (Q N D : P (F := F) (n := n)) (hD : D ∣ Q) :
    D * clearedFractionNumerator Q N D hD = Q * N := by
  rw [clearedFractionNumerator, ← mul_assoc, ← Classical.choose_spec hD]

theorem map_clearedFractionNumerator (Q N D : P (F := F) (n := n)) (hD : D ∣ Q) (hD0 : D ≠ 0) :
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (clearedFractionNumerator Q N D hD) =
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) Q *
        (algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) N /
          algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) D) := by
  have h := congrArg (algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)))
    (clearedFractionNumerator_relation Q N D hD)
  simp only [map_mul] at h
  have hd : algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) D ≠ 0 := by
    intro hz
    exact hD0 (IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (by simpa using hz))
  apply mul_left_cancel₀ hd
  rw [h]
  field_simp [hd]
  <;> ring

def activeNumerator (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i k : Fin n)
    (hk : k ∈ activeInterval δ i) : P (F := F) (n := n) :=
  clearedFractionNumerator (negativeDenominator σ) ((columnNumerator δ σ i).eval (X k))
    (starDenominator k (earlierNegative σ i)) (active_denominator_dvd δ σ i k hk)

def residueNumerator (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i k l : Fin n)
    (hk : k ∈ earlierNegative σ i) (hl : l ∈ activeInterval δ i) : P (F := F) (n := n) :=
  clearedFractionNumerator (negativeDenominator σ) ((columnNumerator δ σ i).eval (X k))
    (starDenominator k ((earlierNegative σ i).erase k) * (X k - X l))
    (residue_denominator_dvd δ σ i k l hk hl)

theorem columnCommonNumerator_eq_active
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) (hk : k ∈ activeInterval δ i) :
    columnCommonNumerator β δ σ hc i k = activeNumerator δ σ i k hk := by
  apply Eq.symm
  apply columnCommonNumerator_unique
  rw [newtonColumn_active_formula β δ σ i k hk]
  exact map_clearedFractionNumerator _ _ _ _ (starDenominator_ne_zero k _
    (fun hn ↦ Finset.disjoint_left.mp (activeInterval_disjoint_earlierNegative δ σ i) hk hn))

theorem columnCommonNumerator_eq_residue_sum
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) (hk : k ∈ earlierNegative σ i) :
    columnCommonNumerator β δ σ hc i k =
      ∑ l : activeInterval δ i, C (β l.val / β k) * residueNumerator δ σ i k l.val hk l.property := by
  apply Eq.symm
  apply columnCommonNumerator_unique
  rw [newtonColumn_residue_formula β δ σ i k hk, map_sum, Finset.mul_sum,
    ← Finset.sum_coe_sort (activeInterval δ i)]
  apply Finset.sum_congr rfl
  intro l hl
  rw [map_mul]
  unfold residueNumerator
  rw [map_clearedFractionNumerator]
  · ring
  · apply mul_ne_zero (starDenominator_ne_zero k _ (Finset.notMem_erase k _))
    have hkl : k < l.val := ((mem_earlierNegative σ i k).mp hk).1.trans_le
      ((mem_activeInterval δ i l.val).mp l.property).1
    exact sub_ne_zero.mpr (fun h ↦ (ne_of_lt hkl) (MvPolynomial.X_injective h))

theorem columnCommonNumerator_eq_zero_of_outside
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) (ha : k ∉ activeInterval δ i) (hn : k ∉ earlierNegative σ i) :
    columnCommonNumerator β δ σ hc i k = 0 := by
  apply IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))
  rw [map_columnCommonNumerator]
  simp only [newtonColumn, rationalColumn, if_neg ha, if_neg hn, mul_zero, map_zero]

theorem identifyCoordinates_starDenominator_ne_zero
    (a b k : Fin n) (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (T : Finset (Fin n)) (hself : k ∉ T) :
    identifyCoordinates (F := F) a b (starDenominator k T) ≠ 0 := by
  rw [starDenominator, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact identifyCoordinates_star_ne_zero a b k j hab
    (fun h ↦ hself (by simpa only [h] using hj))
    ⟨fun h ↦ hka h.1, fun h ↦ hkb h.1⟩

theorem identifyCoordinates_negativeDenominator_eq_zero
    (σ : Fin n → ℤ) (e : Edge n) (he : σ e.1.1 = -1) :
    identifyCoordinates (F := F) e.1.1 e.1.2 (negativeDenominator σ) = 0 := by
  apply (identifyCoordinates_eq_zero_iff e.1.1 e.1.2 (ne_of_lt e.2) _).mpr
  exact edgeLinear_dvd_negativeDenominator σ e he

/-- The full normal condition away from the two endpoints, for each
literal common-numerator column. -/
theorem columnCommonNumerator_negative_other_dvd
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i : Fin n) (e : Edge n) (he : σ e.1.1 = -1)
    (k : Fin n) (hka : k ≠ e.1.1) (hkb : k ≠ e.1.2) :
    edgeLinear e ∣ columnCommonNumerator β δ σ hc i k := by
  apply (identifyCoordinates_eq_zero_iff e.1.1 e.1.2 (ne_of_lt e.2) _).mp
  let φ := (identifyCoordinates (F := F) e.1.1 e.1.2).toRingHom
  have hQ : φ (negativeDenominator σ) = 0 :=
    identifyCoordinates_negativeDenominator_eq_zero σ e he
  by_cases ha : k ∈ activeInterval δ i
  · rw [columnCommonNumerator_eq_active β δ σ hc i k ha]
    apply numerator_vanishes_of_regular_denominator φ
      (negativeDenominator σ) ((columnNumerator δ σ i).eval (X k))
      (starDenominator k (earlierNegative σ i)) _
      (clearedFractionNumerator_relation _ _ _ _) hQ
    exact identifyCoordinates_starDenominator_ne_zero _ _ k (ne_of_lt e.2) hka hkb _
      (fun hn ↦ Finset.disjoint_left.mp (activeInterval_disjoint_earlierNegative δ σ i) ha hn)
  · by_cases hn : k ∈ earlierNegative σ i
    · rw [columnCommonNumerator_eq_residue_sum β δ σ hc i k hn, map_sum]
      apply Finset.sum_eq_zero
      intro l hl
      rw [map_mul]
      change φ (C (β l.val / β k)) * φ (residueNumerator δ σ i k l.val hn l.property) = 0
      suffices hz : φ (residueNumerator δ σ i k l.val hn l.property) = 0 by rw [hz, mul_zero]
      apply numerator_vanishes_of_regular_denominator φ
        (negativeDenominator σ) ((columnNumerator δ σ i).eval (X k))
        (starDenominator k ((earlierNegative σ i).erase k) * (X k - X l.val)) _
        (clearedFractionNumerator_relation _ _ _ _) hQ
      rw [map_mul]
      apply mul_ne_zero
        (identifyCoordinates_starDenominator_ne_zero _ _ k (ne_of_lt e.2) hka hkb _
          (Finset.notMem_erase k _))
      have hkl : k < l.val := ((mem_earlierNegative σ i k).mp hn).1.trans_le
        ((mem_activeInterval δ i l.val).mp l.property).1
      exact identifyCoordinates_star_ne_zero _ _ k l.val (ne_of_lt e.2) (ne_of_lt hkl)
        ⟨fun h ↦ hka h.1, fun h ↦ hkb h.1⟩
    · rw [columnCommonNumerator_eq_zero_of_outside β δ σ hc i k ha hn, map_zero]

end PaperVerification.Fermion.Newton
