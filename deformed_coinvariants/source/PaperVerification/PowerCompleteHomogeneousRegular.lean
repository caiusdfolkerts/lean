module

public import PaperVerification.AlternatingFormsFieldDescent
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Lean.Elab.Tactic.Omega

/-!
# The complete homogeneous comparator over every field

The consecutive complete homogeneous polynomials have only the origin as a
common zero. The proof uses their actual generating function: the finite zero
window propagates by the elementary-symmetric recurrence, so its inverse is a
polynomial. Each factor `1-xᵢt` must then be a polynomial unit. Regularity over
the original field follows by the verified algebraic-closure descent route.
No characteristic or algebraic-closure hypothesis remains in the endpoint.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

section Recurrence

variable {R : Type*} [CommRing R] {n m : ℕ}

theorem elementary_eq_zero_above_variables {j : ℕ} (hj : n < j) :
    MvPolynomial.esymm (Fin n) R j = 0 := by
  rw [MvPolynomial.esymm_eq_multiset_esymm, Multiset.esymm_of_card_lt]
  simpa using hj

/-- The initial length-`n` zero window forces the entire complete-homogeneous
tail to vanish, in arbitrary characteristic. -/
theorem complete_homogeneous_tail_zero (hm : 0 < m) (x : Fin n → R)
    (hwindow : ∀ i : Fin n, MvPolynomial.eval x (MvPolynomial.hsymm (Fin n) R (m+i.val)) = 0)
    (k : ℕ) (hmk : m ≤ k) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin n) R k) = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < m+n
    · simpa only [Nat.add_sub_of_le hmk] using hwindow ⟨k-m, by omega⟩
    · have hkpos : k ≠ 0 := by omega
      have hrec := congrArg (MvPolynomial.eval x)
        (TauCeti.sum_range_hsymm_mul_neg_one_pow_mul_esymm (σ := Fin n) R k)
      simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero, if_neg hkpos] at hrec
      rw [Finset.sum_range_succ] at hrec
      have hsum : ∑ r ∈ Finset.range k,
          MvPolynomial.eval x (MvPolynomial.hsymm (Fin n) R r) *
            ((-1 : R) ^ (k-r) * MvPolynomial.eval x (MvPolynomial.esymm (Fin n) R (k-r))) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        have hrk := Finset.mem_range.mp hr
        by_cases hmr : m ≤ r
        · rw [ih r hrk hmr, zero_mul]
        · rw [elementary_eq_zero_above_variables (by omega), map_zero, mul_zero, mul_zero]
      simpa only [hsum, Nat.sub_self, pow_zero, MvPolynomial.esymm_zero,
        map_one, one_mul, mul_one, zero_add] using hrec

end Recurrence

section CommonZero

variable {K : Type*} [Field K] {n m : ℕ}

/-- The full common-zero assertion for the literal complete homogeneous
polynomials. It holds over every field, including positive characteristic. -/
theorem complete_homogeneous_common_zero (hm : 0 < m) (x : Fin n → K)
    (hwindow : ∀ i : Fin n, MvPolynomial.eval x (MvPolynomial.hsymm (Fin n) K (m+i.val)) = 0) :
    x = 0 := by
  let H : PowerSeries K := PowerSeries.mk fun r =>
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin n) K r)
  let E : Polynomial K := ∏ i : Fin n, (1-Polynomial.C (x i)*Polynomial.X)
  have htail : ∀ r, m ≤ r → PowerSeries.coeff r H = 0 := by
    intro r hr
    simpa only [H, PowerSeries.coeff_mk] using
      complete_homogeneous_tail_zero hm x hwindow r hr
  have htrunc : H = (PowerSeries.trunc m H : Polynomial K) := by
    ext r
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    by_cases hr : r < m
    · simp only [if_pos hr]
    · simp only [if_neg hr, htail r (by omega)]
  have hH : H = ∏ i : Fin n, PowerSeries.mk fun r => x i ^ r := by
    simpa only [H, MvPolynomial.aeval_eq_eval] using
      (TauCeti.mk_aeval_hsymm_eq_prod_mk_pow (R := K) x)
  have hinverse : H * (E : PowerSeries K) = 1 := by
    rw [hH]
    change (∏ i : Fin n, PowerSeries.mk fun r => x i ^ r) *
      Polynomial.coeToPowerSeries.ringHom (∏ i : Fin n, (1-Polynomial.C (x i)*Polynomial.X)) = 1
    rw [map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    simpa only [map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X] using
      TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (x i)
  have hpoly : PowerSeries.trunc m H * E = 1 := by
    apply Polynomial.coe_injective K
    rw [Polynomial.coe_mul, Polynomial.coe_one, ← htrunc]
    exact hinverse
  have hE : IsUnit E := isUnit_iff_exists_inv'.mpr ⟨PowerSeries.trunc m H, hpoly⟩
  ext i
  have hdiv : (1-Polynomial.C (x i)*Polynomial.X) ∣ E :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hu : IsUnit (1-Polynomial.C (x i)*Polynomial.X) := isUnit_of_dvd_unit hdiv hE
  have hdegree := Polynomial.natDegree_eq_zero_of_isUnit hu
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt
    (p := 1-Polynomial.C (x i)*Polynomial.X) (n := 1) (by omega)
  simpa only [Polynomial.coeff_sub, Polynomial.coeff_one, if_neg (by omega : 1 ≠ 0),
    Polynomial.coeff_C_mul_X, if_pos rfl, ite_true, sub_zero, zero_sub, neg_eq_zero,
    Pi.zero_apply] using hz

/-- The actual homogeneous complete intersection used as the representation
comparator in Theorem 2.2, with no restriction on the ground field. -/
theorem complete_homogeneous_isWeaklyRegular (K : Type*) [Field K]
    (n m : ℕ) (hm : 0 < m) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn fun i : Fin n => MvPolynomial.hsymm (Fin n) K (m+i.val)) := by
  apply AlternatingForms.homogeneous_parameters_regular_of_common_zero_extension
    (L := AlgebraicClosure K) (fun _ : Fin n => 1) (fun _ => one_ne_zero)
  · intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact ⟨m+i.val, MvPolynomial.isHomogeneous_hsymm _⟩
  · intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact (MvPolynomial.isHomogeneous_hsymm (σ := Fin n) (R := K) (m+i.val)).coeff_eq_zero
      (by simpa using (show 0 ≠ m+i.val by omega))
  · intro x hx
    apply complete_homogeneous_common_zero hm x
    intro i
    have hi := hx (MvPolynomial.hsymm (Fin n) K (m+i.val)) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [← MvPolynomial.eval_map, MvPolynomial.map_hsymm] at hi
    exact hi
  · simp only [List.length_ofFn, Fintype.card_fin]

end CommonZero

end PaperVerification.PowerOperators
