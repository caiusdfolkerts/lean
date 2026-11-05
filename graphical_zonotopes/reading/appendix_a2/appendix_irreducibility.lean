module

public import Papers.GraphicalZonotopes.AppendixStability
public import Papers.GraphicalZonotopes.AppendixDeterminantRecurrence
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Absolute irreducibility of the tridiagonal determinant

The determinant is first regarded as a polynomial in its first variable.
Its leading and constant coefficients are relatively prime over every
field. The proof treats positive matrix sizes; the zero-size determinant
is the unit polynomial and is not asserted to be irreducible.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Finset Matrix
open MvPolynomial

namespace GraphicalZonotopes.PathDeterminant

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Evaluation commutes with the literal matrix determinant. -/
theorem polynomial_eval₂ (m : ℕ) (f : R →+* S) (t : Fin (m+2) → S) :
    MvPolynomial.eval₂ f t (polynomial R m) = (tridiagonal t).det := by
  change (MvPolynomial.eval₂Hom f t)
    (tridiagonal (fun j => MvPolynomial.X j)).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, tridiagonal]
  split_ifs <;> simp_all [MvPolynomial.coe_eval₂Hom, tridiagonal,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_zero]

/-- Renaming the variables does not change the determinant construction. -/
theorem polynomial_rename {σ : Type*} {m : ℕ} (f : Fin (m+2) → σ) :
    MvPolynomial.rename f (polynomial R m) =
      (tridiagonal (fun j => MvPolynomial.X (f j))).det := by
  unfold polynomial
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, tridiagonal]
  split_ifs <;> simp_all [tridiagonal]

/-- Scalar extension is the ordinary coefficient map on this polynomial. -/
theorem polynomial_map (m : ℕ) (f : R →+* S) :
    MvPolynomial.map f (polynomial R m) = polynomial S m := by
  unfold polynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, tridiagonal]
  split_ifs <;> simp_all [tridiagonal]

@[simp] theorem polynomial_zero (R : Type*) [CommRing R] :
    polynomial R 0 = 1 := by
  simp [polynomial]

theorem polynomial_one (R : Type*) [CommRing R] :
    polynomial R 1 = X 0 + X 1 + X 2 := by
  unfold polynomial
  rw [Matrix.det_fin_one]
  simpa using tridiagonal_diag (fun j : Fin 3 => (X j : MvPolynomial (Fin 3) R)) 0

/-- The matrix recurrence expressed in the original multivariate ring. -/
theorem polynomial_recurrence (R : Type*) [CommRing R] (m : ℕ) :
    polynomial R (m+2) =
      (X 0 + X 1 + X 2) *
        MvPolynomial.rename Fin.succ (polynomial R (m+1)) -
      (X 1)^2 *
        MvPolynomial.rename (fun j : Fin (m+2) => j.succ.succ) (polynomial R m) := by
  rw [polynomial_rename, polynomial_rename]
  exact tridiagonal_det_recurrence
    (fun j : Fin (m+4) => (X j : MvPolynomial (Fin (m+4)) R))

/-- A polynomial in the tail variables becomes a constant under
the equivalence separating the first variable. -/
theorem finSuccEquiv_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ p) =
      Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [MvPolynomial.rename_C, MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, MvPolynomial.rename_X,
        MvPolynomial.finSuccEquiv_X_succ, hp]

/-- The constant coefficient after the first variable is separated.
The following theorem proves its connection with the actual determinant. -/
def constantCoefficient (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin (m+3)) R :=
  (X 0 + X 1) * polynomial R (m+1) -
    (X 0)^2 * MvPolynomial.rename Fin.succ (polynomial R m)

theorem finSuccEquiv_polynomial_one (R : Type*) [CommRing R] :
    MvPolynomial.finSuccEquiv R 2 (polynomial R 1) =
      Polynomial.X + Polynomial.C (X 0 + X 1) := by
  rw [polynomial_one]
  change (MvPolynomial.finSuccEquiv R 2)
    (X 0 + X (0 : Fin 2).succ + X (1 : Fin 2).succ) = _
  simp only [map_add, MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ, add_assoc]

/-- The exact primitive-linear form used in the irreducibility induction. -/
theorem finSuccEquiv_polynomial_succ_succ (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial.finSuccEquiv R (m+3) (polynomial R (m+2)) =
      Polynomial.C (polynomial R (m+1)) * Polynomial.X +
        Polynomial.C (constantCoefficient R m) := by
  have hdouble :
      MvPolynomial.rename (fun j : Fin (m+2) => j.succ.succ) (polynomial R m) =
        MvPolynomial.rename (Fin.succ : Fin (m+3) → Fin (m+4))
          (MvPolynomial.rename Fin.succ (polynomial R m)) := by
    simp only [MvPolynomial.rename_rename, Function.comp_def]
  have h1 : (1 : Fin (m+4)) = (0 : Fin (m+3)).succ := rfl
  have h2 : (2 : Fin (m+4)) = (1 : Fin (m+3)).succ := rfl
  rw [polynomial_recurrence, hdouble, h1, h2]
  simp only [constantCoefficient, map_sub, map_mul, map_add, map_pow,
    MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ,
    finSuccEquiv_rename_succ]
  ring

theorem polynomial_first_coefficient (R : Type*) [CommRing R] (m : ℕ) :
    (MvPolynomial.finSuccEquiv R (m+3) (polynomial R (m+2))).coeff 1 =
      polynomial R (m+1) := by
  rw [finSuccEquiv_polynomial_succ_succ]
  simp [Polynomial.coeff_C_mul_X]

theorem polynomial_constant_coefficient (R : Type*) [CommRing R] (m : ℕ) :
    (MvPolynomial.finSuccEquiv R (m+3) (polynomial R (m+2))).coeff 0 =
      constantCoefficient R m := by
  rw [finSuccEquiv_polynomial_succ_succ]
  simp [Polynomial.coeff_C_mul_X]

/-- This specialization kills the first matrix row in every characteristic. -/
def singularWeights (R : Type*) [CommRing R] (m : ℕ) : Fin (m+3) → R :=
  fun j => if j.val = 0 then 1 else if j.val = 2 then -1 else 0

theorem singularWeights_first_row (R : Type*) [CommRing R] (m : ℕ) (j : Fin (m+1)) :
    tridiagonal (singularWeights R m) 0 j = 0 := by
  have hbelow : j.succ ≠ (0 : Fin (m+1)).castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at hv
    omega
  have htwo : 2 < m + 3 := by omega
  simp [tridiagonal, singularWeights, hbelow, Nat.mod_eq_of_lt htwo]

end Ring

section Field

variable (K : Type*) [Field K]

/-- The determinant cannot disappear on reducing coefficients in any characteristic. -/
theorem polynomial_ne_zero_field (m : ℕ) : polynomial K m ≠ 0 := by
  have hpos : ∀ k, polynomial K (k+1) ≠ 0 := by
    intro k
    induction k with
    | zero =>
        intro hz
        have hcoef :
            (MvPolynomial.finSuccEquiv K 2 (polynomial K 1)).coeff 1 = 1 := by
          rw [finSuccEquiv_polynomial_one]
          simp
        rw [hz, map_zero, Polynomial.coeff_zero] at hcoef
        exact zero_ne_one hcoef
    | succ k ih =>
        intro hz
        have hcoef := polynomial_first_coefficient K k
        rw [hz, map_zero, Polynomial.coeff_zero] at hcoef
        exact ih hcoef.symm
  cases m with
  | zero => simp
  | succ m => exact hpos m

theorem polynomial_totalDegree_field (m : ℕ) :
    (polynomial K m).totalDegree = m :=
  (polynomial_homogeneous K m).totalDegree (polynomial_ne_zero_field K m)

/-- Uniformly in the size and characteristic, the determinant cannot divide
its first variable. Evaluating at (1,0,-1,0,...) turns such divisibility
into the impossible statement that zero divides one. -/
theorem polynomial_not_dvd_first_variable (m : ℕ) :
    ¬ polynomial K (m+1) ∣ (X 0 : MvPolynomial (Fin (m+3)) K) := by
  intro h
  let v := singularWeights K m
  have hd := map_dvd (MvPolynomial.eval v) h
  have hz : MvPolynomial.eval v (polynomial K (m+1)) = 0 := by
    change MvPolynomial.eval₂ (RingHom.id K) v (polynomial K (m+1)) = 0
    rw [polynomial_eval₂]
    exact Matrix.det_eq_zero_of_row_eq_zero 0 (singularWeights_first_row K m)
  have hx : MvPolynomial.eval v (X 0) = 1 := by
    simp [v, singularWeights]
  rw [hz, hx] at hd
  exact one_ne_zero (zero_dvd_iff.mp hd)

/-- The two coefficients of the primitive-linear form have no common nonunit divisor. -/
theorem polynomial_isRelPrime_constantCoefficient (m : ℕ)
    (hA : Irreducible (polynomial K (m+1))) :
    IsRelPrime (polynomial K (m+1)) (constantCoefficient K m) := by
  apply hA.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  have hp : Prime (polynomial K (m+1)) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hA
  have hCne :
      MvPolynomial.rename (Fin.succ : Fin (m+2) → Fin (m+3))
        (polynomial K m) ≠ 0 := by
    intro h
    apply polynomial_ne_zero_field K m
    exact (MvPolynomial.rename_eq_zero_iff_of_injective _ (Fin.succ_injective _)).mp h
  have hCdeg :
      (MvPolynomial.rename (Fin.succ : Fin (m+2) → Fin (m+3))
        (polynomial K m)).totalDegree ≤ m := by
    calc
      _ ≤ (polynomial K m).totalDegree :=
        MvPolynomial.totalDegree_rename_le _ _
      _ = m := polynomial_totalDegree_field K m
  have hnotC : ¬ polynomial K (m+1) ∣
      MvPolynomial.rename (Fin.succ : Fin (m+2) → Fin (m+3)) (polynomial K m) := by
    intro h
    have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain h hCne
    rw [polynomial_totalDegree_field] at hd
    omega
  have hmul : polynomial K (m+1) ∣
      (X 0 + X 1) * polynomial K (m+1) :=
    ⟨X 0 + X 1, mul_comm _ _⟩
  have hprod : polynomial K (m+1) ∣
      (X 0)^2 * MvPolynomial.rename Fin.succ (polynomial K m) := by
    have hd := dvd_sub hmul hdiv
    have heq :
        (X 0 + X 1) * polynomial K (m+1) - constantCoefficient K m =
          (X 0)^2 * MvPolynomial.rename Fin.succ (polynomial K m) := by
      unfold constantCoefficient
      ring
    rwa [heq] at hd
  rcases hp.dvd_mul.mp hprod with hpow | hC
  · exact polynomial_not_dvd_first_variable K m (hp.dvd_of_dvd_pow hpow)
  · exact hnotC hC

/-- Irreducibility of the exact determinant over every field, at every positive size. -/
theorem polynomial_irreducible (m : ℕ) : Irreducible (polynomial K (m+1)) := by
  induction m with
  | zero =>
      apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 2)).mp
      rw [finSuccEquiv_polynomial_one]
      have hrel : IsRelPrime (1 : MvPolynomial (Fin 2) K) (X 0 + X 1) := by
        intro d hd _
        exact isUnit_of_dvd_one hd
      simpa using Polynomial.irreducible_C_mul_X_add_C
        (a := (1 : MvPolynomial (Fin 2) K)) (b := X 0 + X 1) one_ne_zero hrel
  | succ m ih =>
      apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K (m+3))).mp
      rw [finSuccEquiv_polynomial_succ_succ]
      exact Polynomial.irreducible_C_mul_X_add_C
        (polynomial_ne_zero_field K (m+1))
        (polynomial_isRelPrime_constantCoefficient K m ih)

/-- Irreducibility after every coefficient homomorphism into a field. -/
theorem polynomial_irreducible_map {L : Type*} [Field L] (f : K →+* L) (m : ℕ) :
    Irreducible (MvPolynomial.map f (polynomial K (m+1))) := by
  rw [polynomial_map]
  exact polynomial_irreducible L m

/-- Absolute irreducibility in Proposition A.2, stated explicitly as
irreducibility after extending scalars to an algebraic closure. -/
theorem proposition_A_2_absoluteIrreducible (m : ℕ) (hm : 0 < m) :
    Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (polynomial K m)) := by
  cases m with
  | zero => omega
  | succ m =>
      exact polynomial_irreducible_map K (algebraMap K (AlgebraicClosure K)) m

end Field

end GraphicalZonotopes.PathDeterminant
