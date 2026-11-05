module

public import PaperVerification.FermionNewtonProfileNonzero

/-!
# Actual polynomial numerators for the rational Newton columns

Every pole denominator is a product of distinct negative edge equations.
The common negative product therefore clears it. This file keeps that fact
as divisibility in the original polynomial ring, including the coordinate
factors prescribed by the multiplicity profile.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

def starDenominator (k : Fin n) (T : Finset (Fin n)) : P (F := F) (n := n) :=
  ∏ j ∈ T, (X k - X j)

theorem starLinear_prime (k j : Fin n) (hkj : k ≠ j) :
    Prime (X (R := F) k - X j) := by
  have h := (MulEquiv.prime_iff (coordinateShear (F := F) k j hkj)).mpr
    (MvPolynomial.prime_X (R := F) (i := k))
  simpa only [coordinateShear_X_self] using h

theorem starLinear_relPrime (k j l : Fin n) (hkj : k ≠ j) (hkl : k ≠ l) (hjl : j ≠ l) :
    IsRelPrime (X (R := F) k - X j) (X k - X l) := by
  apply (starLinear_prime k j hkj).irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  let ev : P (F := F) (n := n) →ₐ[F] (P (F := F) (n := n)) := aeval fun t ↦ if t = j then X k else X t
  have h := map_dvd ev hd
  have hz : (X (R := F) k - X l) = 0 := by
    simpa only [ev, map_sub, aeval_X, if_neg hkj, if_pos rfl, if_true, sub_self,
      if_neg (Ne.symm hjl), zero_dvd_iff] using h
  exact hkl (MvPolynomial.X_injective (sub_eq_zero.mp hz))

theorem starLinear_relPrime_coordinate (k j : Fin n) (hkj : k ≠ j) :
    IsRelPrime (X (R := F) k - X j) (X k) := by
  apply IsRelPrime.symm
  apply (MvPolynomial.prime_X (R := F) (i := k)).irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  have h := (coordinateRestriction_eq_zero_iff k (X (R := F) k - X j)).mpr hd
  have hz : (X (R := F) j) = 0 := by
    simpa only [coordinateRestriction, map_sub, aeval_X, if_pos rfl, if_true,
      if_neg (Ne.symm hkj), zero_sub, neg_eq_zero] using h
  exact MvPolynomial.X_ne_zero (R := F) j hz

theorem starLinear_dvd_negativeDenominator (σ : Fin n → ℤ) (k j : Fin n)
    (hkj : k ≠ j)
    (hneg : (k < j → σ k = -1) ∧ (j < k → σ j = -1)) :
    (X (R := F) k - X j) ∣ negativeDenominator σ := by
  rcases lt_or_gt_of_ne hkj with hlt | hgt
  · exact edgeLinear_dvd_negativeDenominator σ ⟨(k,j),hlt⟩ (hneg.1 hlt)
  · obtain ⟨q,hq⟩ := edgeLinear_dvd_negativeDenominator (F := F) σ ⟨(j,k),hgt⟩ (hneg.2 hgt)
    refine ⟨-q, ?_⟩
    rw [hq]
    change (X j - X k) * q = (X k - X j) * -q
    ring

theorem starDenominator_dvd_negativeDenominator (σ : Fin n → ℤ)
    (k : Fin n) (T : Finset (Fin n)) (hself : k ∉ T)
    (hneg : ∀ j ∈ T, (k < j → σ k = -1) ∧ (j < k → σ j = -1)) :
    starDenominator (F := F) k T ∣ negativeDenominator σ := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro j hj l hl hjl
    change j ∈ T at hj
    change l ∈ T at hl
    exact starLinear_relPrime k j l (fun h ↦ hself (by simpa only [h] using hj))
      (fun h ↦ hself (by simpa only [h] using hl)) hjl
  · intro j hj
    exact starLinear_dvd_negativeDenominator σ k j
      (fun h ↦ hself (by simpa only [h] using hj)) (hneg j hj)

theorem starDenominator_ne_zero (k : Fin n) (T : Finset (Fin n)) (hself : k ∉ T) :
    starDenominator (F := F) k T ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (fun h ↦ hself (by simpa only [MvPolynomial.X_injective h] using hj))

theorem active_denominator_dvd (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (i k : Fin n) (hk : k ∈ activeInterval δ i) :
    starDenominator (F := F) k (earlierNegative σ i) ∣ negativeDenominator σ := by
  have hik := ((mem_activeInterval δ i k).mp hk).1
  apply starDenominator_dvd_negativeDenominator
  · intro hn
    exact (not_lt_of_ge hik) ((mem_earlierNegative σ i k).mp hn).1
  · intro j hj
    rcases (mem_earlierNegative σ i j).mp hj with ⟨hji,hjσ⟩
    exact ⟨fun hkj ↦ False.elim ((not_lt_of_ge (le_of_lt (hji.trans_le hik))) hkj),
      fun _ ↦ hjσ⟩

theorem residue_denominator_dvd (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (i k l : Fin n) (hk : k ∈ earlierNegative σ i) (hl : l ∈ activeInterval δ i) :
    starDenominator (F := F) k ((earlierNegative σ i).erase k) * (X k - X l) ∣
      negativeDenominator σ := by
  have hki := ((mem_earlierNegative σ i k).mp hk).1
  have hkσ := ((mem_earlierNegative σ i k).mp hk).2
  have hil := ((mem_activeInterval δ i l).mp hl).1
  have hkl : k < l := hki.trans_le hil
  have hlnot : l ∉ (earlierNegative σ i).erase k := by
    intro h
    exact (not_lt_of_ge hil) ((mem_earlierNegative σ i l).mp (Finset.mem_erase.mp h).2).1
  have h := starDenominator_dvd_negativeDenominator (F := F) σ k
    (insert l ((earlierNegative σ i).erase k))
    (by simp only [Finset.mem_insert, Finset.mem_erase]; exact not_or.mpr ⟨ne_of_lt hkl, by simp⟩)
    (by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨fun _ ↦ hkσ, fun hlt ↦ False.elim ((not_lt_of_ge (le_of_lt (hki.trans_le hil))) hlt)⟩
      · exact ⟨fun _ ↦ hkσ, fun _ ↦ ((mem_earlierNegative σ i j).mp (Finset.mem_erase.mp hj).2).2⟩)
  simpa only [starDenominator, Finset.prod_insert hlnot, mul_comm] using h

/-- Rational functions whose common-denominator numerator has a prescribed
polynomial divisor. This is an actual submodule, so sums of residue terms
retain both polynomiality and the coordinate divisibility. -/
def clearedDivisibility (Q p : P (F := F) (n := n)) : Submodule (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) where
  carrier := {z | ∃ a : (P (F := F) (n := n)), p ∣ a ∧ algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) a =
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) Q * z}
  zero_mem' := ⟨0, dvd_zero _, by simp⟩
  add_mem' := by
    rintro x y ⟨a,ha,hea⟩ ⟨b,hb,heb⟩
    refine ⟨a+b,dvd_add ha hb,?_⟩
    rw [map_add,hea,heb,mul_add]
  smul_mem' := by
    rintro a x ⟨b,hb,heb⟩
    refine ⟨a*b,dvd_mul_of_dvd_right hb a,?_⟩
    rw [map_mul,heb,Algebra.smul_def]
    ring

theorem fraction_mem_clearedDivisibility
    (Q p N D : P (F := F) (n := n)) (hD : D ∣ Q) (hD0 : D ≠ 0) (hN : p ∣ N) :
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) N /
        algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) D ∈ clearedDivisibility Q p := by
  obtain ⟨q,hq⟩ := hD
  refine ⟨q*N,dvd_mul_of_dvd_right hN q,?_⟩
  have hd : algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) D ≠ 0 := by
    intro hz
    exact hD0 (IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (by simpa using hz))
  rw [hq,map_mul,map_mul]
  field_simp [hd]
  <;> ring

theorem evaluated_numerator_coordinate_dvd
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i k : Fin n) (hδ : δ k ≤ δ i) :
    X k ^ δ k ∣ (columnNumerator (F := F) δ σ i).eval (X k) := by
  rw [columnNumerator, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact dvd_mul_of_dvd_left (pow_dvd_pow (X k) hδ) _

theorem map_starDenominator (k : Fin n) (T : Finset (Fin n)) :
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (starDenominator (F := F) k T) =
      ∏ j ∈ T, (rationalNode k - rationalNode j) := by
  simp only [starDenominator, map_prod, map_sub, rationalNode]

end PaperVerification.Fermion.Newton
