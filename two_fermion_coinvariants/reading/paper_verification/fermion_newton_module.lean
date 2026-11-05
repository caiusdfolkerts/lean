module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization

public import PaperVerification.FermionRadical
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.Prime.Lemmas
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Coprime.Lemmas
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

/-!
# The actual numerator module of rational Newton fields

The rational fields in Section 2.1 have common denominator `Q₋`. Their
numerators satisfy the paper's coordinate, tangent and weighted-normal
conditions. This module defines those exact conditions and proves that the
weighted contraction has no pole. It also proves that every sufficiently
high ordinary power field lies in the module, so its contraction ideal
contains the ordinary moment ideal. The explicit Newton determinant and the
basis/deletion identities are separate obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

abbrev P := MvPolynomial (Fin n) F
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

def edgeLinear (e : Edge n) : P (F := F) (n := n) := X e.1.1 - X e.1.2

/-- A coordinate shear sends `Xᵢ` to `Xᵢ-Xⱼ`. -/
def coordinateShear (i j : Fin n) (hij : i ≠ j) : P (F := F) (n := n) ≃ₐ[F] P (F := F) (n := n) :=
  AlgEquiv.ofAlgHom
    (aeval fun k ↦ if k = i then X i - X j else X k)
    (aeval fun k ↦ if k = i then X i + X j else X k)
    (by
      ext k
      by_cases hk : k = i
      · subst k; simp [hij, Ne.symm hij]
      · simp [hk])
    (by
      ext k
      by_cases hk : k = i
      · subst k; simp [hij, Ne.symm hij]
      · simp [hk])

@[simp] theorem coordinateShear_X_self (i j : Fin n) (hij : i ≠ j) :
    coordinateShear (F := F) i j hij (X i) = X i - X j := by
  simp [coordinateShear]

 theorem edgeLinear_prime (e : Edge n) : Prime (edgeLinear (F := F) e) := by
  have h := (MulEquiv.prime_iff
    (coordinateShear (F := F) e.1.1 e.1.2 (ne_of_lt e.2))).mpr
      (MvPolynomial.prime_X (R := F) (i := e.1.1))
  simpa only [coordinateShear_X_self, edgeLinear] using h

/-- Distinct ordered hyperplanes have relatively prime defining equations. -/
 theorem edgeLinear_pairwise_relPrime :
    Pairwise (fun e f : Edge n ↦ IsRelPrime (edgeLinear (F := F) e) (edgeLinear f)) := by
  intro e f hef
  apply (edgeLinear_prime e).irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  rcases e with ⟨⟨i, j⟩, hij⟩
  rcases f with ⟨⟨k, l⟩, hkl⟩
  let ev : P (F := F) (n := n) →ₐ[F] P (F := F) (n := n) := aeval fun t ↦ if t = i then X j else X t
  have hmap := map_dvd ev hd
  have heq : (if k = i then j else k) = (if l = i then j else l) := by
    have hz : X (R := F) (if k = i then j else k) -
        X (if l = i then j else l) = 0 := by
      by_cases hki : k = i <;> by_cases hli : l = i <;>
        simpa [ev, edgeLinear, ne_of_gt hij, hki, hli] using hmap
    exact MvPolynomial.X_injective (sub_eq_zero.mp hz)
  by_cases hki : k = i
  · by_cases hli : l = i
    · subst k; subst l; exact (lt_irrefl _ hkl)
    · simp only [hki, hli, if_true, if_false] at heq
      apply hef
      apply Subtype.ext
      exact Prod.ext hki.symm heq
  · by_cases hli : l = i
    · simp only [hki, hli, if_false, if_true] at heq
      subst l
      subst k
      exact (not_lt_of_ge (le_of_lt hij)) hkl
    · simp only [hki, hli, if_false] at heq
      exact (ne_of_lt hkl) heq

/-- The common denominator is the product of all negative hyperplanes. -/
def negativeDenominator (σ : Fin n → ℤ) : P (F := F) (n := n) :=
  ∏ e ∈ Finset.univ.filter (fun e : Edge n ↦ σ e.1.1 = -1), edgeLinear e

 theorem negativeDenominator_ne_zero (σ : Fin n → ℤ) :
    negativeDenominator (F := F) σ ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro e he
  exact (edgeLinear_prime e).ne_zero

 theorem edgeLinear_dvd_negativeDenominator (σ : Fin n → ℤ) (e : Edge n)
    (he : σ e.1.1 = -1) : edgeLinear (F := F) e ∣ negativeDenominator σ := by
  classical
  exact Finset.dvd_prod_of_mem _ (by simp [he])

/-- Exact common-numerator conditions from Section 2.1. -/
def NumeratorConditions (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (a : Fin n → P (F := F) (n := n)) : Prop :=
  (∀ i, X i ^ δ i ∣ a i) ∧
  (∀ e : Edge n, σ e.1.1 = 1 → edgeLinear e ∣ a e.1.1 - a e.1.2) ∧
  (∀ e : Edge n, σ e.1.1 = -1 →
    (edgeLinear e ∣ C (β e.1.1) * a e.1.1 + C (β e.1.2) * a e.1.2) ∧
    ∀ k, k ≠ e.1.1 → k ≠ e.1.2 → edgeLinear e ∣ a k)

/-- The numerator form of the paper's rational Newton-field module. -/
def numeratorModule (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) :
    Submodule (P (F := F) (n := n)) (Fin n → P (F := F) (n := n)) where
  carrier := {a | NumeratorConditions β δ σ a}
  zero_mem' := by simp [NumeratorConditions]
  add_mem' := by
    intro a b ha hb
    refine ⟨fun i ↦ dvd_add (ha.1 i) (hb.1 i), ?_, ?_⟩
    · intro e he
      simpa only [Pi.add_apply, add_sub_add_comm] using dvd_add (ha.2.1 e he) (hb.2.1 e he)
    · intro e he
      refine ⟨?_, fun k hki hkj ↦ dvd_add ((ha.2.2 e he).2 k hki hkj)
        ((hb.2.2 e he).2 k hki hkj)⟩
      convert dvd_add (ha.2.2 e he).1 (hb.2.2 e he).1 using 1 <;>
        simp only [Pi.add_apply] <;> ring
  smul_mem' := by
    intro p a ha
    refine ⟨fun i ↦ dvd_mul_of_dvd_right (ha.1 i) p, ?_, ?_⟩
    · intro e he
      simpa only [Pi.smul_apply, smul_eq_mul, mul_sub] using
        dvd_mul_of_dvd_right (ha.2.1 e he) p
    · intro e he
      refine ⟨?_, fun k hki hkj ↦ dvd_mul_of_dvd_right ((ha.2.2 e he).2 k hki hkj) p⟩
      convert dvd_mul_of_dvd_right (ha.2.2 e he).1 p using 1 <;>
        simp only [Pi.smul_apply, smul_eq_mul] <;> ring

@[simp] theorem mem_numeratorModule (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (a : Fin n → P (F := F) (n := n)) :
    a ∈ numeratorModule β δ σ ↔ NumeratorConditions β δ σ a := Iff.rfl

/-- Weighted contraction cancels every permitted negative pole. -/
 theorem denominator_dvd_contraction (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) {a : Fin n → P (F := F) (n := n)} (ha : a ∈ numeratorModule β δ σ) :
    negativeDenominator σ ∣ ∑ i, C (β i) * a i := by
  classical
  apply Finset.prod_dvd_of_isRelPrime
    (edgeLinear_pairwise_relPrime.set_pairwise _)
  intro e he
  have he' : σ e.1.1 = -1 := (Finset.mem_filter.mp he).2
  have hi := ha.2.2 e he'
  have hrest : edgeLinear e ∣
      ∑ k ∈ (Finset.univ.erase e.1.1).erase e.1.2, C (β k) * a k := by
    apply Finset.dvd_sum
    intro k hk
    have hk' := Finset.mem_erase.mp hk
    have hk'' := Finset.mem_erase.mp hk'.2
    exact dvd_mul_of_dvd_right (hi.2 k hk''.1 hk'.1) _
  have hsplit : (∑ i, C (β i) * a i) =
      (∑ k ∈ (Finset.univ.erase e.1.1).erase e.1.2, C (β k) * a k) +
        (C (β e.1.1) * a e.1.1 + C (β e.1.2) * a e.1.2) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e.1.1),
      ← Finset.sum_erase_add _ _ (show e.1.2 ∈ Finset.univ.erase e.1.1 by
        simp [ne_of_gt e.2])]
    ring
  rw [hsplit]
  exact dvd_add hrest hi.1

/-- The contraction ideal consists literally of the polynomial values
`(Σ βᵢ Aᵢ)/Q₋` of the rational fields. -/
def contractionIdeal (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) :
    Ideal (P (F := F) (n := n)) where
  carrier := {p | ∃ a ∈ numeratorModule β δ σ,
    (∑ i, C (β i) * a i) = negativeDenominator σ * p}
  zero_mem' := ⟨0, (numeratorModule β δ σ).zero_mem, by simp⟩
  add_mem' := by
    rintro p q ⟨a, ha, hpa⟩ ⟨b, hb, hqb⟩
    refine ⟨a + b, (numeratorModule β δ σ).add_mem ha hb, ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hpa, hqb]
  smul_mem' := by
    rintro p q ⟨a, ha, hqa⟩
    refine ⟨p • a, (numeratorModule β δ σ).smul_mem p ha, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, C (β i) * (p * a i)) = p * ∑ i, C (β i) * a i := by
        simp only [Finset.mul_sum, mul_left_comm]
      _ = _ := by rw [hqa]; ring

/-- Sufficiently high polynomial power fields satisfy all Newton conditions. -/
 theorem powerField_mem_numeratorModule (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (d : ℕ) (hd : ∀ i, δ i ≤ d) :
    (fun i ↦ negativeDenominator (F := F) σ * X i ^ d) ∈ numeratorModule β δ σ := by
  refine ⟨fun i ↦ dvd_mul_of_dvd_right (pow_dvd_pow (X i) (hd i)) _, ?_, ?_⟩
  · intro e he
    simpa only [mul_sub, edgeLinear] using
      dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow (X (R := F) e.1.1) (X e.1.2) d)
        (negativeDenominator σ)
  · intro e he
    have hq := edgeLinear_dvd_negativeDenominator (F := F) σ e he
    refine ⟨dvd_add ?_ ?_, fun k hki hkj ↦ dvd_mul_of_dvd_left hq _⟩ <;>
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hq _) _

 theorem powerMoment_mem_contractionIdeal (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (d : ℕ) (hd : ∀ i, δ i ≤ d) :
    (∑ i, C (β i) * X i ^ d) ∈ contractionIdeal β δ σ := by
  refine ⟨_, powerField_mem_numeratorModule β δ σ d hd, ?_⟩
  simp only [Finset.mul_sum, mul_left_comm]

/-- This is the actual ideal inclusion used to establish finite colength in
Section 2.2. It holds before any Newton determinant or basis is assumed. -/
 theorem ordinaryMomentIdeal_le_contractionIdeal (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (b : ℕ) (hb : ∀ i, δ i ≤ b) :
    ordinaryMomentIdeal (fun i : Fin n ↦ (X i : P (F := F) (n := n))) β (Polynomial.X ^ b) ≤
      contractionIdeal β δ σ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change _ ∈ contractionIdeal β δ σ
  have h := powerMoment_mem_contractionIdeal β δ σ (b + k)
    (fun i ↦ (hb i).trans (Nat.le_add_right b k))
  simpa only [moment, Polynomial.aeval_X_pow, smul_eq_mul,
    pow_add, MvPolynomial.algebraMap_eq, mul_assoc, mul_left_comm, mul_comm] using h

/-- The actual Newton contraction quotient is finite over the coefficient
field whenever the subset sums are nonzero. This uses pole cancellation and
ordinary moments, not an assumed Newton basis. -/
theorem contraction_quotient_finite (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Module.Finite F (P (F := F) (n := n) ⧸ contractionIdeal β δ σ) := by
  classical
  let d : ℕ := ∑ i, δ i
  have hd (i : Fin n) : δ i ≤ d := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (δ j))
    (Finset.mem_univ i)
  apply finite_quotient_of_univariate_radical (contractionIdeal β δ σ)
    (fun _ ↦ Polynomial.X ^ d) (fun _ ↦ Polynomial.monic_X.pow d)
  intro i
  apply common_polynomial_mem_radical (contractionIdeal β δ σ)
    (fun j : Fin n ↦ (X j : P (F := F) (n := n))) β (Polynomial.X ^ d) hβ
  intro k
  exact ordinaryMomentIdeal_le_contractionIdeal β δ σ d hd (Ideal.subset_span ⟨k, rfl⟩)

end PaperVerification.Fermion.Newton
