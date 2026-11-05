module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.BigOperators.Module
public import Lean.Elab.Tactic.Omega

/-!
# Independence of lifts modulo a regular polynomial parameter

If multiplication by `X` is injective, vectors whose images modulo `X` are
linearly independent over the coefficient ring are independent over its
polynomial ring. The proof divides any proposed finite relation by `X`;
no finite-dimensionality, field, or torsion-free theorem is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Polynomial
open scoped BigOperators

namespace PaperVerification.PolynomialBasisLifting

variable {K M V I : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [Module K[X] M] [IsScalarTower K K[X] M]
  [AddCommGroup V] [Module K V]

/-- A linear map annihilating `X M` sees only the constant coefficient
of every polynomial scalar. -/
theorem map_polynomial_smul (q : M →ₗ[K] V)
    (hqX : ∀ m, q ((X : K[X]) • m) = 0) (p : K[X]) (m : M) :
    q (p • m) = p.coeff 0 • q m := by
  calc
    q (p • m) = q ((X * p.divX + C (p.coeff 0)) • m) := by rw [X_mul_divX_add]
    _ = q ((X : K[X]) • (p.divX • m)) + q (C (p.coeff 0) • m) := by
      rw [add_smul, mul_smul, map_add]
    _ = p.coeff 0 • q m := by
      rw [hqX, zero_add, ← Polynomial.algebraMap_eq, algebraMap_smul, map_smul]

/-- Finite-family form of polynomial independence lifting. -/
theorem linearIndependent_lifts_finite [Fintype I]
    (q : M →ₗ[K] V) (hqX : ∀ m, q ((X : K[X]) • m) = 0)
    (hX : IsSMulRegular M (X : K[X])) (b : I → M)
    (hb : LinearIndependent K (fun i => q (b i))) : LinearIndependent K[X] b := by
  classical
  have constant_zero (p : I → K[X]) (hp : (∑ i, p i • b i) = 0) :
      ∀ i, (p i).coeff 0 = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    have hq := congrArg q hp
    simpa only [map_sum, map_polynomial_smul q hqX, map_zero] using hq
  have aux : ∀ N : ℕ, ∀ p : I → K[X], (∀ i, (p i).natDegree ≤ N) →
      (∑ i, p i • b i) = 0 → ∀ i, p i = 0 := by
    intro N
    induction N with
    | zero =>
      intro p hdeg hp i
      have hi : (p i).natDegree = 0 := Nat.eq_zero_of_le_zero (hdeg i)
      rw [Polynomial.eq_C_of_natDegree_eq_zero hi, constant_zero p hp i, C_0]
    | succ N ih =>
      intro p hdeg hp
      have hc := constant_zero p hp
      have hpdiv (i : I) : X * (p i).divX = p i := by
        simpa only [hc i, C_0, add_zero] using (p i).X_mul_divX_add
      have hrel : (∑ i, (p i).divX • b i) = 0 := by
        apply hX
        change (X : K[X]) • (∑ i, (p i).divX • b i) = (X : K[X]) • (0 : M)
        rw [smul_zero, Finset.smul_sum]
        simpa only [← mul_smul, hpdiv] using hp
      have hdegdiv (i : I) : (p i).divX.natDegree ≤ N := by
        rw [natDegree_divX_eq_natDegree_tsub_one]
        have hi := hdeg i
        omega
      have hz := ih (fun i => (p i).divX) hdegdiv hrel
      intro i
      rw [← hpdiv i, hz i, mul_zero]
  apply Fintype.linearIndependent_iff.mpr
  intro p hp
  exact aux (Finset.univ.sup fun i => (p i).natDegree) p
    (fun i => Finset.le_sup (f := fun i => (p i).natDegree) (Finset.mem_univ i)) hp

/-- No restriction on the indexing set is needed: every linear relation has finite support. -/
theorem linearIndependent_lifts
    (q : M →ₗ[K] V) (hqX : ∀ m, q ((X : K[X]) • m) = 0)
    (hX : IsSMulRegular M (X : K[X])) (b : I → M)
    (hb : LinearIndependent K (fun i => q (b i))) : LinearIndependent K[X] b := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro s
  exact linearIndependent_lifts_finite q hqX hX (fun i : s => b i)
    (hb.comp _ Subtype.val_injective)

end PaperVerification.PolynomialBasisLifting
