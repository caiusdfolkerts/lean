module

public import PaperVerification.AlternatingFormsChernAnnihilation
public import PaperVerification.AlternatingFormsChernHomogeneity
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A nonzero top value of the actual Chern coefficient pairing

The central coefficient of the squared staircase alternant is the sign of
reversal times `s!`.  Consequently the formal integration functional is
nonzero on the top power of the last Chern coordinate.  This supplies the
nonzero functional needed by the complete-intersection pairing argument
without invoking geometric positivity.  The geometric integration comparison
and the perfect-pairing theorem for the complete intersection remain separate.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

section AlternantCoefficient

variable {R : Type*} [CommRing R]

private theorem cast_intUnit_sq (u : ℤˣ) : ((u : ℤ) : R) ^ 2 = 1 := by
  have h := congrArg (fun z : ℤ => (z : R)) (Int.isUnit_sq u.isUnit)
  simpa only [Int.cast_pow, Int.cast_one] using h

/-- The exponent with the same value in every variable. -/
noncomputable def constantExponent (s d : ℕ) : Fin s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun _ => d

@[simp] theorem constantExponent_apply (s d : ℕ) (i : Fin s) :
    constantExponent s d i = d := rfl

/-- The constant rectangular exponent in the squared Vandermonde has one
contribution of the same sign from each permutation. -/
theorem chernVandermonde_sq_central_coefficient (s : ℕ) :
    (chernVandermonde (R := R) s ^ 2).coeff (constantExponent s (s - 1)) =
      (s.factorial : R) * ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤ) : R) := by
  let a : Fin s → ℕ := fun i => s - 1 - i.val
  let D : MvPolynomial (Fin s) R := chernVandermonde s
  let m := constantExponent s (s - 1)
  have hexpand : D * D =
      ∑ τ : Equiv.Perm (Fin s), Equiv.Perm.sign τ •
        (D * ∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i) := by
    calc
      _ = D * ∑ τ : Equiv.Perm (Fin s), Equiv.Perm.sign τ •
          ∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i :=
        congrArg (fun q : MvPolynomial (Fin s) R => D * q)
          (TauCeti.alternant_eq_sum a)
      _ = _ := by simp only [Finset.mul_sum, mul_smul_comm]
  have hterm (τ : Equiv.Perm (Fin s)) :
      (Equiv.Perm.sign τ •
        (D * ∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i)).coeff m =
          ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤ) : R) := by
    let d : Fin s →₀ ℕ := Finsupp.equivFunOnFinite.symm (a ∘ τ.symm)
    have hprod : (∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i) =
        monomial d 1 := by
      have hp : (∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i) =
          ∏ i : Fin s, (X i : MvPolynomial (Fin s) R) ^ a (τ.symm i) := by
        rw [← Equiv.prod_comp τ (fun i => (X i : MvPolynomial (Fin s) R) ^ a (τ.symm i))]
        simp
      rw [hp, prod_X_pow]
      apply congrArg (fun e : Fin s →₀ ℕ => monomial e (1 : R))
      ext i
      simp [d, Function.comp_def]
    have hle : d ≤ m := by
      intro i
      change s - 1 - (τ.symm i).val ≤ s - 1
      exact Nat.sub_le _ _
    have hcomp : m - d =
        Finsupp.equivFunOnFinite.symm (a ∘ (τ.symm.trans Fin.revPerm)) := by
      ext i
      change (s - 1) - (s - 1 - (τ.symm i).val) =
        s - 1 - ((τ.symm i).rev).val
      rw [Fin.val_rev]
      have hi := (τ.symm i).isLt
      omega
    rw [coeff_smul, hprod, coeff_mul_monomial', if_pos hle, mul_one, hcomp]
    change Equiv.Perm.sign τ •
      (TauCeti.alternant (Fin s) R a).coeff
        (Finsupp.equivFunOnFinite.symm (a ∘ (τ.symm.trans Fin.revPerm))) = _
    rw [TauCeti.coeff_alternant_of_injective (TauCeti.injective_staircase s),
      Equiv.Perm.sign_trans, Equiv.Perm.sign_symm]
    simp only [Units.smul_def, zsmul_eq_mul, Units.val_mul, Int.cast_mul]
    have hsquare := cast_intUnit_sq (R := R) (Equiv.Perm.sign τ)
    calc
      _ = (((Equiv.Perm.sign Fin.revPerm : ℤ) : R)) *
          (((Equiv.Perm.sign τ : ℤ) : R) ^ 2) := by ring
      _ = _ := by rw [hsquare, mul_one]
  change (D ^ 2).coeff m = _
  rw [pow_two, hexpand, coeff_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

end AlternantCoefficient

section NonzeroValue

variable {K : Type*} [Field K] [CharZero K] {s N : ℕ}

theorem esymm_fin_card :
    esymm (Fin s) K s = ∏ i : Fin s, (X i : MvPolynomial (Fin s) K) := by
  have hpow : (Finset.univ : Finset (Fin s)).powersetCard s = {Finset.univ} := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.powersetCard_self (Finset.univ : Finset (Fin s))
  rw [esymm, hpow, Finset.sum_singleton]

/-- The last Chern coordinate raised to its top-degree exponent. -/
noncomputable def chernTopTestPolynomial (hs : 0 < s) (N : ℕ) : MvPolynomial (Fin s) K :=
  X ⟨s - 1, by omega⟩ ^ (2 * (N - s))

/-- This is a top-degree element for the paper's actual Chern grading. -/
theorem chernTopTestPolynomial_isWeightedHomogeneous (hs : 0 < s) (N : ℕ) :
    (chernTopTestPolynomial (K := K) hs N).IsWeightedHomogeneous
      chernCoefficientWeight (s * (2 * (N - s))) := by
  have h := (MvPolynomial.isWeightedHomogeneous_X K chernCoefficientWeight
    (⟨s - 1, by omega⟩ : Fin s)).pow (2 * (N - s))
  have hlast : s - 1 + 1 = s := by omega
  simpa only [chernTopTestPolynomial, chernCoefficientWeight, hlast,
    smul_eq_mul, mul_comm] using h

theorem chernTopTestPolynomial_substitution (hs : 0 < s) (N : ℕ) :
    MvPolynomial.aeval (fun i : Fin s => esymm (Fin s) K (i.val + 1))
      (chernTopTestPolynomial (K := K) hs N) =
        monomial (constantExponent s (2 * (N - s))) 1 := by
  rw [chernTopTestPolynomial, map_pow, aeval_X]
  have hlast : s - 1 + 1 = s := by omega
  rw [hlast, esymm_fin_card, ← Finset.prod_pow, prod_X_pow]
  apply congrArg (fun e : Fin s →₀ ℕ => monomial e (1 : K))
  ext i
  simp [constantExponent]

/-- The nonzero top value is derived by a coefficient computation for the
actual functional, rather than assumed as a pairing hypothesis. -/
theorem chernCoefficientIntegration_top_ne_zero (hs : 0 < s) (hsN : s ≤ N) :
    chernCoefficientIntegration N (chernTopTestPolynomial (K := K) hs N) ≠ 0 := by
  have hindex : constantExponent s (2 * (N - s)) +
      2 • constantExponent s (s - 1) = chernTopExponent s N := by
    ext i
    simp only [Finsupp.add_apply, Finsupp.smul_apply, constantExponent_apply,
      chernTopExponent_apply, smul_eq_mul]
    omega
  unfold chernCoefficientIntegration
  rw [chernTopTestPolynomial_substitution]
  unfold chernIntegrationCoefficient
  rw [← map_pow, ← hindex, coeff_monomial_mul, one_mul,
    coeff_expand_smul 2 (by decide), chernVandermonde_sq_central_coefficient]
  apply mul_ne_zero
  · exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))
  · apply mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))
    exact Int.cast_ne_zero.mpr (Units.ne_zero (Equiv.Perm.sign Fin.revPerm))

end NonzeroValue

end PaperVerification.AlternatingForms
