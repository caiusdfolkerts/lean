module

public import PaperVerification.EulerJacobian
public import PaperVerification.KoszulSyzygies

/-!
# The polynomial divergence model of the Brieskorn quotient

All spaces below use actual multivariate polynomials and partial derivatives.
The tangent fields are the kernel of contraction with the gradient. Their
ordinary divergences form the subspace appearing in the top-form model.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [CommRing K] [Fintype ι]

local notation "P" => MvPolynomial ι K

/-- The usual divergence of a polynomial vector field. -/
def divergence : (ι → P) →ₗ[K] P where
  toFun g := ∑ i, pderiv i (g i)
  map_add' g h := by simp [Finset.sum_add_distrib]
  map_smul' a g := by simp [Finset.smul_sum]

@[simp] theorem divergence_apply (g : ι → P) :
    divergence g = ∑ i, pderiv i (g i) := rfl

/-- The actual polynomial gradient. -/
def gradient (F : P) : ι → P := fun i => pderiv i F

/-- Polynomial vector fields tangent to all level sets of `F`. -/
def tangent (F : P) : Submodule P (ι → P) :=
  LinearMap.ker (KoszulSyzygies.coefficient (gradient F))

/-- Divergences of tangent fields, regarded as a coefficient-ring submodule. -/
def divergenceSpace (F : P) : Submodule K P :=
  ((tangent F).restrictScalars K).map divergence

/-- Divergence of an alternating matrix, with the sign convention of the
coordinate Koszul boundary. -/
def curl (A : ι → ι → P) : ι → P :=
  fun j => ∑ i, pderiv i (A j i - A i j)

/-- Mixed partials commute, so the divergence of this curl is zero. -/
theorem divergence_curl (A : ι → ι → P) : divergence (curl A) = 0 := by
  simp only [divergence_apply, curl, map_sum, map_sub, Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact pderiv_comm j i (A j i)

/-- Differentiating a Koszul relation cancels the symmetric Hessian terms. -/
theorem divergence_boundary (F : P) (A : ι → ι → P) :
    divergence (KoszulSyzygies.boundary (gradient F) A) =
      KoszulSyzygies.coefficient (gradient F) (curl A) := by
  have hH := KoszulSyzygies.symmetric_skew_sum
    (fun i j => pderiv i (pderiv j F)) A (fun i j => pderiv_comm i j F)
  simp only [divergence_apply, KoszulSyzygies.boundary_apply, gradient,
    map_sum, pderiv_mul, Finset.sum_add_distrib]
  rw [hH, zero_add]
  rw [Finset.sum_comm]
  simp only [KoszulSyzygies.coefficient_apply, gradient, curl, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Contraction with the gradient is the extra term in the product rule. -/
theorem divergence_mul (F : P) (g : ι → P) :
    divergence (F • g) = KoszulSyzygies.coefficient (gradient F) g + F * divergence g := by
  simp only [divergence_apply, Pi.smul_apply, smul_eq_mul, pderiv_mul,
    Finset.sum_add_distrib, KoszulSyzygies.coefficient_apply, gradient, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Multiplication by the potential preserves the divergence subspace. -/
theorem potential_mul_mem (F u : P) (hu : u ∈ divergenceSpace F) :
    F * u ∈ divergenceSpace F := by
  obtain ⟨g, hg, rfl⟩ := hu
  refine ⟨F • g, (tangent F).smul_mem F hg, ?_⟩
  have hzero : KoszulSyzygies.coefficient (gradient F) g = 0 := hg
  rw [divergence_mul, hzero, zero_add]

/-- Regularity of the actual gradient implies that every divergence of a
level-set-tangent field lies in the actual Jacobian ideal. -/
theorem divergenceSpace_le_jacobian {n : ℕ} (F : MvPolynomial (Fin n) K)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F))) :
    divergenceSpace F ≤
      (Ideal.span (Set.range (gradient F))).restrictScalars K := by
  intro u hu
  obtain ⟨g, hg, rfl⟩ := hu
  have hker : g ∈ LinearMap.ker (KoszulSyzygies.coefficient (gradient F)) := hg
  rw [KoszulSyzygies.kernel_eq_boundary_range (gradient F) hreg] at hker
  obtain ⟨A, rfl⟩ := hker
  rw [divergence_boundary, KoszulSyzygies.coefficient_apply]
  apply (Ideal.span (Set.range (gradient F))).sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The polynomial Euler vector field, applied to a coefficient polynomial. -/
def eulerField (w : ι → ℕ) (u : P) : ι → P := fun i => w i • (X i * u)

theorem coefficient_eulerField (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (u : P) :
    KoszulSyzygies.coefficient (gradient F) (eulerField w u) = h • (F * u) := by
  have hE := MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv hF
  simp only [KoszulSyzygies.coefficient_apply, gradient, eulerField]
  calc
    (∑ i, (w i • (X i * u)) * pderiv i F) =
        (∑ i, w i • (X i * pderiv i F)) * u := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [nsmul_eq_mul]
      ring
    _ = (h • F) * u := by rw [hE]
    _ = h • (F * u) := by simp only [nsmul_eq_mul, mul_assoc]

theorem divergence_eulerField (w : ι → ℕ) (u : P) :
    divergence (eulerField w u) = (∑ i, w i) • u +
      ∑ i, w i • (X i * pderiv i u) := by
  simp only [divergence_apply, eulerField, map_nsmul, pderiv_mul, pderiv_X_self,
    one_mul, smul_add, Finset.sum_add_distrib, Finset.sum_smul]

theorem divergence_eulerField_homogeneous (w : ι → ℕ) (u : P) (d : ℕ)
    (hu : u.IsWeightedHomogeneous w d) :
    divergence (eulerField w u) = ((∑ i, w i) + d) • u := by
  rw [divergence_eulerField, hu.sum_weight_X_mul_pderiv, add_smul]

end PaperVerification.JacobianDivergence
