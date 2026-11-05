module

public import PaperVerification.JacobianGrading
public import PaperVerification.ProjectionQuotient

/-!
# The single resonant weighted degree

The scalar Euler operator is diagonal on the actual polynomial grading. If it
has precisely one zero eigenvalue, its image is exactly the kernel of projection
onto that degree. This identifies the residual quotient without truncation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.EulerResonance

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K

def scalarEuler (w : ι → ℕ) (a t : K) : P →ₗ[K] P :=
  a • LinearMap.id + t • JacobianDivergence.weightedEuler w

@[simp] theorem scalarEuler_apply (w : ι → ℕ) (a t : K) (f : P) :
    scalarEuler w a t f = a • f + t • JacobianDivergence.weightedEuler w f := rfl

theorem scalarEuler_homogeneous (w : ι → ℕ) (a t : K) (d : ℕ)
    (f : P) (hf : f.IsWeightedHomogeneous w d) :
    scalarEuler w a t f = (a + t * (d : K)) • f := by
  rw [scalarEuler_apply, JacobianDivergence.weightedEuler_homogeneous w f d hf,
    smul_smul, add_smul]

/-- Nonresonance is required only in degrees that actually contain monomials,
including when the positive weights omit some natural-number degrees. -/
theorem scalarEuler_surjective_of_monomial_nonresonance
    (w : ι → ℕ) (a t : K)
    (hne : ∀ e : ι →₀ ℕ, a + t * (Finsupp.weight w e : K) ≠ 0) :
    Function.Surjective (scalarEuler w a t) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  intro f hf
  clear hf
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => exact (LinearMap.range (scalarEuler w a t)).add_mem hf hg
  | monomial e c =>
      refine ⟨(a + t * (Finsupp.weight w e : K))⁻¹ • monomial e c, ?_⟩
      rw [map_smul, scalarEuler_homogeneous w a t _ _
        (isWeightedHomogeneous_monomial w e c rfl),
        smul_smul, inv_mul_cancel₀ (hne e), one_smul]

theorem component_scalarEuler (w : ι → ℕ) (a t : K) (d : ℕ) (f : P) :
    weightedHomogeneousComponent w d (scalarEuler w a t f) =
      (a + t * (d : K)) • weightedHomogeneousComponent w d f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [map_add, hf, hg, smul_add]
  | monomial e c =>
    have hm := isWeightedHomogeneous_monomial w e c rfl
    rw [scalarEuler_homogeneous w a t _ _ hm, map_smul]
    by_cases hd : d = Finsupp.weight w e
    · subst d
      rfl
    · rw [hm.weightedHomogeneousComponent_ne d hd]
      simp only [smul_zero]

theorem range_scalarEuler_eq_projection_kernel (w : ι → ℕ) (a t : K) (d : ℕ)
    (hd : a + t * (d : K) = 0)
    (hne : ∀ j : ℕ, j ≠ d → a + t * (j : K) ≠ 0) :
    LinearMap.range (scalarEuler w a t) =
      LinearMap.ker (weightedHomogeneousComponent w d : P →ₗ[K] P) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker, component_scalarEuler, hd, zero_smul]
  · intro f hf
    classical
    have hf0 : weightedHomogeneousComponent w d f = 0 := LinearMap.mem_ker.mp hf
    let s : Finset ℕ := (weightedHomogeneousComponent_finsupp (w := w) f).toFinset
    have hsum : ∑ j ∈ s, weightedHomogeneousComponent w j f = f := by
      calc
        _ = ∑ᶠ j, weightedHomogeneousComponent w j f :=
          (finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) f)).symm
        _ = f := sum_weightedHomogeneousComponent w f
    rw [← hsum]
    apply (LinearMap.range (scalarEuler w a t)).sum_mem
    intro j _
    by_cases hj : j = d
    · subst j
      rw [hf0]
      exact (LinearMap.range (scalarEuler w a t)).zero_mem
    · refine ⟨(a + t * (j : K))⁻¹ • weightedHomogeneousComponent w j f, ?_⟩
      rw [map_smul, scalarEuler_homogeneous w a t j _
        (weightedHomogeneousComponent_isWeightedHomogeneous j f),
        smul_smul, inv_mul_cancel₀ (hne j hj), one_smul]

theorem homogeneous_projection_idempotent (w : ι → ℕ) (d : ℕ) (f : P) :
    weightedHomogeneousComponent w d (weightedHomogeneousComponent w d f) =
      weightedHomogeneousComponent w d f :=
  (weightedHomogeneousComponent_isWeightedHomogeneous d f).weightedHomogeneousComponent_same

/-- The actual degree-`d` part of a polynomial quotient, presented as an image. -/
def quotientComponent (w : ι → ℕ) (d : ℕ) (U : Submodule K P) :
    Submodule K (P ⧸ U) :=
  LinearMap.range (U.mkQ.comp (weightedHomogeneousComponent w d))

theorem projection_range (w : ι → ℕ) (d : ℕ) :
    LinearMap.range (weightedHomogeneousComponent w d : P →ₗ[K] P) =
      weightedHomogeneousSubmodule K w d := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact weightedHomogeneousComponent_isWeightedHomogeneous d g
  · intro hf
    exact ⟨f, (show f.IsWeightedHomogeneous w d from hf).weightedHomogeneousComponent_same⟩

theorem quotientComponent_eq_map (w : ι → ℕ) (d : ℕ) (U : Submodule K P) :
    quotientComponent w d U = (weightedHomogeneousSubmodule K w d).map U.mkQ := by
  rw [quotientComponent, LinearMap.range_comp, projection_range]

def resonantQuotientEquiv (w : ι → ℕ) (a t : K) (d : ℕ)
    (hd : a + t * (d : K) = 0)
    (hne : ∀ j : ℕ, j ≠ d → a + t * (j : K) ≠ 0)
    (U : Submodule K P)
    (hU : ∀ f ∈ U, weightedHomogeneousComponent w d f ∈ U) :
    (P ⧸ (LinearMap.range (scalarEuler w a t) ⊔ U)) ≃ₗ[K] quotientComponent w d U :=
  (Submodule.quotEquivOfEq _ _
    (congrArg (fun S : Submodule K P => S ⊔ U)
      (range_scalarEuler_eq_projection_kernel w a t d hd hne))).trans
    (ProjectionQuotient.projectedQuotientEquiv (weightedHomogeneousComponent w d)
      (homogeneous_projection_idempotent w d) U hU)

end PaperVerification.EulerResonance
