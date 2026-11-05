module

public import PaperVerification.AlternatingFormsEvenDeterminantOrder
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Polynomial normalization of the universal determinant vectors

The two coefficient vectors remain b and c throughout this degeneration.
No substitution y_i=b_i z_i is made before the leading term is determined.
The normalized determinant is an explicit polynomial sum, and its product
with the exact power of t is proved equal to the original determinant.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.EvenDeterminants

open scoped BigOperators Polynomial
open MvPolynomial

variable {K α : Type*} [CommRing K]

def rowScalar (r : ℕ) (b c : α → K) : OddRows r → α → K
  | Sum.inl i, j => b j ^ (r - i.val) * c j ^ i.val
  | Sum.inr i, j => b j ^ (r - 1 - i.val) * c j ^ i.val

def rowVariable (r : ℕ) : OddRows r → α → MvPolynomial α K
  | Sum.inl _, _ => 1
  | Sum.inr _, j => MvPolynomial.X j

def termVariables (r : ℕ) (a : OddRows r → α) (σ : Equiv.Perm (OddRows r)) :
    MvPolynomial α K :=
  ∏ i : Fin r, MvPolynomial.X (a (σ (Sum.inr i)))

def termScalar (r : ℕ) (b c : α → K) (a : OddRows r → α)
    (σ : Equiv.Perm (OddRows r)) : K :=
  ∏ i, rowScalar r b c i (a (σ i))

theorem oddSubsetMatrix_factor (r : ℕ) (b c : α → K) (a : OddRows r → α)
    (i j : OddRows r) :
    oddSubsetMatrix r b c a i j =
      MvPolynomial.C (rowScalar r b c i (a j)) * rowVariable r i (a j) := by
  cases i <;> simp [oddSubsetMatrix, rowScalar, rowVariable]

theorem determinant_term_factorization (r : ℕ) (b c : α → K) (a : OddRows r → α)
    (σ : Equiv.Perm (OddRows r)) :
    (∏ i, oddSubsetMatrix r b c a i (σ i)) =
      MvPolynomial.C (termScalar r b c a σ) * termVariables r a σ := by
  simp_rw [oddSubsetMatrix_factor]
  rw [Finset.prod_mul_distrib, ← map_prod]
  congr 1
  rw [Fintype.prod_sum_type]
  simp [rowVariable, termVariables]

theorem oddSubsetDeterminant_expansion (r : ℕ) (b c : α → K)
    (a : OddRows r → α) :
    oddSubsetDeterminant r b c a =
      ∑ σ : Equiv.Perm (OddRows r),
        MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : K) * termScalar r b c a σ) *
          termVariables r a σ := by
  rw [oddSubsetDeterminant,
    PaperVerification.DeterminantDerivation.determinant_row_expansion]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [determinant_term_factorization, map_mul, map_intCast]
  ring

theorem termVariables_homogeneous (r : ℕ) (a : OddRows r → α)
    (σ : Equiv.Perm (OddRows r)) :
    (termVariables (K := K) r a σ).IsHomogeneous r := by
  simpa only [termVariables, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] using
    MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin r => (MvPolynomial.X (a (σ (Sum.inr i))) : MvPolynomial α K))
      (fun _ => 1) (fun i hi => MvPolynomial.isHomogeneous_X K _)

theorem termVariables_degreeOf_le_one [Nontrivial K] (r : ℕ)
    (a : OddRows r → α) (ha : Function.Injective a)
    (σ : Equiv.Perm (OddRows r)) (x : α) :
    (termVariables (K := K) r a σ).degreeOf x ≤ 1 := by
  classical
  have hinj : Function.Injective (fun i : Fin r => a (σ (Sum.inr i))) :=
    ha.comp (σ.injective.comp Sum.inr_injective)
  have hp := MvPolynomial.degreeOf_prod_le x Finset.univ
    (fun i : Fin r => (MvPolynomial.X (a (σ (Sum.inr i))) : MvPolynomial α K))
  change (termVariables r a σ).degreeOf x ≤ _ at hp
  by_cases hx : ∃ i : Fin r, a (σ (Sum.inr i)) = x
  · obtain ⟨i, rfl⟩ := hx
    simpa [MvPolynomial.degreeOf_X, hinj.eq_iff] using hp
  · have hn (i : Fin r) : x ≠ a (σ (Sum.inr i)) :=
      fun he => hx ⟨i, he.symm⟩
    have hzero : (termVariables (K := K) r a σ).degreeOf x ≤ 0 := by
      simpa [MvPolynomial.degreeOf_X, hn] using hp
    exact hzero.trans (Nat.zero_le 1)

/-- The two literal coefficient vectors used for the nonzero-minor witness. -/
def firstParameter (m : ℕ) (i : Fin m) : K[X] :=
  Polynomial.X ^ i.val

def secondParameter (m : ℕ) (i : Fin m) : K[X] :=
  Polynomial.X ^ (m - 1 - i.val)

theorem parameter_rowScalar (m r : ℕ) (i : OddRows r) (j : Fin m) :
    rowScalar r (firstParameter (K := K) m) (secondParameter m) i j =
      Polynomial.X ^ entryExponent m r i j := by
  cases i <;> simp only [rowScalar, firstParameter, secondParameter,
    entryExponent, ← pow_mul, ← pow_add] <;> congr 1 <;> ring

theorem parameter_termScalar (m r : ℕ) (I : Fin (2 * r + 1) → Fin m)
    (σ : Equiv.Perm (OddRows r)) :
    termScalar r (firstParameter (K := K) m) (secondParameter m)
        (fun i => I (rowPosition r i)) σ =
      Polynomial.X ^ determinantTermExponent m r I σ := by
  unfold termScalar
  simp_rw [parameter_rowScalar]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

theorem parameter_determinant_expansion (m r : ℕ) (I : Fin (2 * r + 1) → Fin m) :
    oddSubsetDeterminant r (firstParameter (K := K) m) (secondParameter m)
        (fun i => I (rowPosition r i)) =
      ∑ σ : Equiv.Perm (OddRows r),
        MvPolynomial.C (Polynomial.monomial (determinantTermExponent m r I σ)
          (((Equiv.Perm.sign σ : ℤ) : K))) *
        termVariables r (fun i => I (rowPosition r i)) σ := by
  rw [oddSubsetDeterminant_expansion]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [parameter_termScalar]
  congr 2
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_intCast]

/-- Remove the exact minimum power term by term, within the polynomial ring. -/
def normalizedDeterminant (m r : ℕ) (I : Fin (2 * r + 1) → Fin m) :
    MvPolynomial (Fin m) K[X] :=
  ∑ σ : Equiv.Perm (OddRows r),
    MvPolynomial.C (Polynomial.monomial
      (determinantTermExponent m r I σ - determinantTermExponent m r I 1)
      (((Equiv.Perm.sign σ : ℤ) : K))) *
    termVariables r (fun i => I (rowPosition r i)) σ

theorem normalizedDeterminant_factor (m r : ℕ)
    (I : Fin (2 * r + 1) → Fin m) (hI : StrictMono I) :
    MvPolynomial.C (Polynomial.X ^ determinantTermExponent m r I 1) *
        normalizedDeterminant (K := K) m r I =
      oddSubsetDeterminant r (firstParameter m) (secondParameter m)
        (fun i => I (rowPosition r i)) := by
  rw [parameter_determinant_expansion, normalizedDeterminant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  have he : determinantTermExponent m r I 1 ≤ determinantTermExponent m r I σ := by
    by_cases hs : σ = 1
    · subst σ
      exact le_rfl
    · exact (determinantTermExponent_unique_minimum m r I hI σ hs).le
  rw [← mul_assoc, ← map_mul, Polynomial.X_pow_eq_monomial,
    Polynomial.monomial_mul_monomial, one_mul, Nat.add_sub_of_le he]

/-- The exact constant coefficient vector is the alternating-position monomial. -/
theorem normalizedDeterminant_at_zero (m r : ℕ)
    (I : Fin (2 * r + 1) → Fin m) (hI : StrictMono I) :
    MvPolynomial.map (Polynomial.evalRingHom (0 : K))
        (normalizedDeterminant m r I) =
      ∏ i : Fin r, (MvPolynomial.X
        (I (rowPosition r (Sum.inr i))) : MvPolynomial (Fin m) K) := by
  classical
  rw [normalizedDeterminant, map_sum, Finset.sum_eq_single 1]
  · simp [termVariables, Polynomial.coe_evalRingHom, Polynomial.eval_monomial]
  · intro σ hσ hs
    have he := determinantTermExponent_unique_minimum m r I hI σ hs
    have hn : determinantTermExponent m r I σ -
        determinantTermExponent m r I 1 ≠ 0 := by omega
    simp [map_mul, MvPolynomial.map_C, Polynomial.coe_evalRingHom,
      Polynomial.eval_monomial, hn]
  · simp

theorem normalizedDeterminant_homogeneous (m r : ℕ)
    (I : Fin (2 * r + 1) → Fin m) :
    (normalizedDeterminant (K := K) m r I).IsHomogeneous r := by
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  exact (termVariables_homogeneous r (fun i => I (rowPosition r i)) σ).C_mul _

theorem normalizedDeterminant_degreeOf_le_one [Nontrivial K] (m r : ℕ)
    (I : Fin (2 * r + 1) → Fin m) (hI : Function.Injective I) (x : Fin m) :
    (normalizedDeterminant (K := K) m r I).degreeOf x ≤ 1 := by
  classical
  apply (MvPolynomial.degreeOf_sum_le x Finset.univ _).trans
  apply Finset.sup_le
  intro σ hσ
  apply (MvPolynomial.degreeOf_C_mul_le _ x _).trans
  exact termVariables_degreeOf_le_one r (fun i => I (rowPosition r i))
    (hI.comp (rowPosition_injective r)) σ x

section Kernels

variable [IsDomain K]

/-- The polynomial normalization itself remains in both actual derivative kernels. -/
theorem normalizedDeterminant_joint_kernel (m r : ℕ)
    (I : Fin (2 * r + 1) → Fin m) (hI : StrictMono I) :
    directionalDerivative (firstParameter (K := K) m) (normalizedDeterminant m r I) = 0 ∧
    directionalDerivative (secondParameter (K := K) m) (normalizedDeterminant m r I) = 0 := by
  have hscale : (MvPolynomial.C
      (Polynomial.X ^ determinantTermExponent m r I 1) :
      MvPolynomial (Fin m) K[X]) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (pow_ne_zero _ Polynomial.X_ne_zero)
  have hfirst := oddSubsetDeterminant_first_kernel r
    (firstParameter (K := K) m) (secondParameter m)
    (fun i => I (rowPosition r i))
  have hsecond := oddSubsetDeterminant_second_kernel r
    (firstParameter (K := K) m) (secondParameter m)
    (fun i => I (rowPosition r i))
  rw [← normalizedDeterminant_factor m r I hI] at hfirst hsecond
  simp only [Derivation.leibniz, MvPolynomial.derivation_C, smul_zero,
    add_zero, smul_eq_mul, mul_zero] at hfirst hsecond
  exact ⟨(mul_eq_zero.mp hfirst).resolve_left hscale,
    (mul_eq_zero.mp hsecond).resolve_left hscale⟩

end Kernels

end PaperVerification.AlternatingForms.EvenDeterminants

