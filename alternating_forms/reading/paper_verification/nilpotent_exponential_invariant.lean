module

public import PaperVerification.RegularNilpotentFlag
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Infinite

/-!
# Invariant subspaces of the genuine finite exponential action

For a nilpotent linear map over a characteristic-zero field, invariance under
all finite exponentials is equivalent to invariance under the linear map.
The reverse implication extracts the coefficient of the parameter from an
actual scalar polynomial. No differentiability or Lie-theoretic assertion is
assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.NilpotentExponentialInvariant

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [Module ℚ V] [IsScalarTower ℚ K V] [SMulCommClass ℚ K V]

/-- A scalar coordinate of the finite exponential orbit is an actual polynomial. -/
def scalarOrbitPolynomial (T : Module.End K V) (v : V) (ℓ : V →ₗ[K] K)
    (n : ℕ) : Polynomial K :=
  ∑ i ∈ Finset.range n,
    Polynomial.C ((i.factorial : K)⁻¹ * ℓ ((T^i) v)) * Polynomial.X^i

/-- The polynomial has precisely the scalar values of the finite exponential. -/
theorem scalarOrbitPolynomial_eval (T : Module.End K V) (v : V)
    (ℓ : V →ₗ[K] K) (n : ℕ) (hn : T^n=0) (u : K) :
    (scalarOrbitPolynomial T v ℓ n).eval u = ℓ (IsNilpotent.exp (u • T) v) := by
  have hu : (u • T)^n=0 := by rw [smul_pow,hn,smul_zero]
  rw [IsNilpotent.exp_eq_sum hu]
  simp only [scalarOrbitPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_rat_smul,
    smul_pow, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [LinearMap.smul_apply, Algebra.smul_def, map_inv₀, map_natCast,Algebra.algebraMap_self,RingHom.id_apply]
  ring

/-- Stability under the infinitesimal map implies stability under every genuine
finite exponential, by the finite sum defining the exponential. -/
theorem exponential_invariant_of_invariant
    (T : Module.End K V) (hT : IsNilpotent T) (U : Submodule K V)
    (hU : ∀ v ∈ U, T v ∈ U) :
    ∀ u : K, ∀ v ∈ U, IsNilpotent.exp (u • T) v ∈ U := by
  obtain ⟨n,hn⟩ := hT
  intro u v hv
  have hu : (u • T)^n=0 := by rw [smul_pow,hn,smul_zero]
  rw [IsNilpotent.exp_eq_sum hu, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i hi
  rw [LinearMap.smul_apply]
  apply (U.restrictScalars ℚ).smul_mem
  change ((u • T)^i) v ∈ U
  apply Module.End.pow_apply_mem_of_forall_mem
  · intro x hx
    exact U.smul_mem u (hU x hx)
  · exact hv

/-- If an entire exponential orbit stays in a linear subspace, its linear
coefficient does too. A separating functional would give an identically zero
polynomial with nonzero linear coefficient. -/
theorem invariant_of_exponential_invariant
    (T : Module.End K V) (hT : IsNilpotent T) (U : Submodule K V)
    (hU : ∀ u : K, ∀ v ∈ U, IsNilpotent.exp (u • T) v ∈ U) :
    ∀ v ∈ U, T v ∈ U := by
  intro v hv
  by_contra hnot
  obtain ⟨ℓ,hℓne,hℓ⟩ := Submodule.exists_le_ker_of_notMem hnot
  obtain ⟨n,hn⟩ := hT
  have hn' : T^(n+2)=0 := pow_eq_zero_of_le (by omega) hn
  have hp : scalarOrbitPolynomial T v ℓ (n+2) = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro u
    rw [scalarOrbitPolynomial_eval T v ℓ (n+2) hn' u]
    exact hℓ (hU u v hv)
  have hc := congrArg (fun p : Polynomial K => p.coeff 1) hp
  have h1 : 1 < n+2 := by omega
  have hcoeff : (scalarOrbitPolynomial T v ℓ (n+2)).coeff 1 = ℓ (T v) := by
    simp only [scalarOrbitPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow]
    simp [h1]
  rw [hcoeff, Polynomial.coeff_zero] at hc
  exact hℓne hc

/-- Invariant subspaces of the additive one-parameter action are exactly the
invariant subspaces of its nilpotent generator. -/
theorem exponential_invariant_iff
    (T : Module.End K V) (hT : IsNilpotent T) (U : Submodule K V) :
    (∀ u : K, ∀ v ∈ U, IsNilpotent.exp (u • T) v ∈ U) ↔
      (∀ v ∈ U, T v ∈ U) :=
  ⟨invariant_of_exponential_invariant T hT U,
    exponential_invariant_of_invariant T hT U⟩

/-- Equality under the actual linear-map action on subspaces is equivalent to
stability under the entire exponential family; inverse parameters supply the
reverse inclusion. -/
theorem exponential_map_eq_iff
    (T : Module.End K V) (hT : IsNilpotent T) (U : Submodule K V) :
    (∀ u : K, U.map (IsNilpotent.exp (u • T)) = U) ↔
      (∀ u : K, ∀ v ∈ U, IsNilpotent.exp (u • T) v ∈ U) := by
  constructor
  · intro h u v hv
    have hm : IsNilpotent.exp (u • T) v ∈ U.map (IsNilpotent.exp (u • T)) :=
      Submodule.mem_map.mpr ⟨v,hv,rfl⟩
    rwa [h u] at hm
  · intro h u
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact h u v hv
    · intro v hv
      apply Submodule.mem_map.mpr
      refine ⟨IsNilpotent.exp ((-u) • T) v,h (-u) v hv,?_⟩
      change (IsNilpotent.exp (u • T)*IsNilpotent.exp ((-u) • T)) v = v
      rw [neg_smul,IsNilpotent.exp_mul_exp_neg_self (hT.smul u),Module.End.one_apply]

/-- The finite exponentials satisfy the additive group law. -/
theorem exponential_add
    (T : Module.End K V) (hT : IsNilpotent T) (u v : K) :
    IsNilpotent.exp ((u+v) • T) =
      IsNilpotent.exp (u • T) * IsNilpotent.exp (v • T) := by
  rw [add_smul]
  apply IsNilpotent.exp_add_of_commute
  · change (u • T)*(v • T)=(v • T)*(u • T)
    simp [smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm]
  · exact hT.smul u
  · exact hT.smul v

end PaperVerification.NilpotentExponentialInvariant
