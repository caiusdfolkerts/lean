module

public import PaperVerification.VectorEulerGrading
public import PaperVerification.JacobianLinearAction

/-!
# Arbitrary linear-group naturality for the vector Euler defect

The target action is coordinatewise pullback by the actual inverse matrix;
the labels of the equations are fixed. The chain rule and divergence
conjugation identity establish stability of the coefficient and hit spaces.
The canonical defect map intertwines these actual quotient actions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.VectorEuler

variable {K ι κ G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι] [Group G]
local notation "P" => MvPolynomial ι K
local notation "M" => κ → P
local notation "GL" => (Matrix ι ι K)ˣ

def targetRepresentation (ρ : G →* GL) : Representation K G M where
  toFun g := LinearMap.pi fun a =>
    (JacobianLinearAction.polynomialRepresentation ρ g).comp (LinearMap.proj a)
  map_one' := by
    apply LinearMap.ext
    intro v
    funext a
    exact congrArg (fun f : Module.End K P => f (v a))
      (JacobianLinearAction.polynomialRepresentation ρ).map_one
  map_mul' g g' := by
    apply LinearMap.ext
    intro v
    funext a
    exact congrArg (fun f : Module.End K P => f (v a))
      ((JacobianLinearAction.polynomialRepresentation ρ).map_mul g g')

@[simp] theorem targetRepresentation_apply (ρ : G →* GL) (g : G) (v : M) (a : κ) :
    targetRepresentation ρ g v a =
      JacobianLinearAction.polynomialRepresentation ρ g (v a) := rfl

theorem normalizedJacobian_transform (F : κ → P) (h : κ → ℕ) (A : GL)
    (hF : ∀ a, linearSubst (A : Matrix ι ι K) (F a) = F a) (v : ι → P) :
    VectorJacobian.normalizedJacobianMap F h (JacobianLinearAction.transformVectorField A v) =
      fun a => linearSubst (A : Matrix ι ι K) (VectorJacobian.normalizedJacobianMap F h v a) := by
  funext a
  have hc (v' : ι → P) : VectorJacobian.jacobianMap F v' a =
      KoszulSyzygies.coefficient (JacobianDivergence.gradient (F a)) v' := by
    simp only [VectorJacobian.jacobianMap_apply, KoszulSyzygies.coefficient_apply,
      JacobianDivergence.gradient, mul_comm]
  change (h a : K)⁻¹ • VectorJacobian.jacobianMap F
      (JacobianLinearAction.transformVectorField A v) a =
    linearSubst (A : Matrix ι ι K) ((h a : K)⁻¹ • VectorJacobian.jacobianMap F v a)
  rw [map_smul, hc, hc]
  congr 1
  simpa only [hF a] using JacobianLinearAction.coefficient_transform A (F a) v

theorem aggregate_transform (F : κ → P) (h : κ → ℕ) (t : K) (A : GL)
    (hF : ∀ a, linearSubst (A : Matrix ι ι K) (F a) = F a) (v : ι → P) :
    aggregate F h t (JacobianLinearAction.transformVectorField A v) =
      fun a => linearSubst (A : Matrix ι ι K) (aggregate F h t v a) := by
  rw [aggregate, EulerReduction.perturbed_apply, normalizedJacobian_transform F h A hF v,
    JacobianLinearAction.divergence_transform]
  funext a
  simp only [aggregate, EulerReduction.perturbed_apply, Pi.add_apply,
    Pi.smul_apply, potential_apply, map_add, map_smul, map_mul, hF]

theorem targetRepresentation_preserves_coefficient (ρ : G →* GL)
    (F : κ → P) (h : κ → ℕ)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a)
    (g : G) (v : M) (hv : v ∈ coefficientSpace F h) :
    targetRepresentation ρ g v ∈ coefficientSpace F h := by
  obtain ⟨u, rfl⟩ := hv
  exact ⟨JacobianLinearAction.transformVectorField (ρ g⁻¹) u,
    normalizedJacobian_transform F h (ρ g⁻¹) (hF g⁻¹) u⟩

theorem targetRepresentation_preserves_hit (ρ : G →* GL)
    (F : κ → P) (h : κ → ℕ) (t : K)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a)
    (g : G) (v : M) (hv : v ∈ hit F h t) :
    targetRepresentation ρ g v ∈ hit F h t := by
  obtain ⟨u, rfl⟩ := hv
  exact ⟨JacobianLinearAction.transformVectorField (ρ g⁻¹) u,
    aggregate_transform F h t (ρ g⁻¹) (hF g⁻¹) u⟩

def hitQuotientRepresentation (ρ : G →* GL) (F : κ → P) (h : κ → ℕ) (t : K)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a) :
    Representation K G (M ⧸ hit F h t) :=
  (targetRepresentation ρ).quotient (hit F h t)
    (fun g v hv => targetRepresentation_preserves_hit ρ F h t hF g v hv)

@[simp] theorem hitQuotientRepresentation_mk (ρ : G →* GL)
    (F : κ → P) (h : κ → ℕ) (t : K)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a) (g : G) (v : M) :
    hitQuotientRepresentation ρ F h t hF g ((hit F h t).mkQ v) =
      (hit F h t).mkQ (targetRepresentation ρ g v) := rfl

theorem hitQuotientRepresentation_preserves_defect (ρ : G →* GL)
    (F : κ → P) (h : κ → ℕ) (t : K)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a)
    (g : G) (x : M ⧸ hit F h t) (hx : x ∈ defectImage F h t) :
    hitQuotientRepresentation ρ F h t hF g x ∈ defectImage F h t := by
  obtain ⟨v, hv, rfl⟩ := hx
  rw [hitQuotientRepresentation_mk]
  exact ⟨targetRepresentation ρ g v,
    targetRepresentation_preserves_coefficient ρ F h hF g v hv, rfl⟩

/-- The action on the image model of `J/H` is the actual quotient restriction. -/
def defectRepresentation (ρ : G →* GL) (F : κ → P) (h : κ → ℕ) (t : K)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a) :
    Representation K G (defectImage F h t) :=
  (hitQuotientRepresentation ρ F h t hF).subrepresentation (defectImage F h t)
    (fun g x hx => hitQuotientRepresentation_preserves_defect ρ F h t hF g x hx)

def coefficientRepresentation (ρ : G →* GL) (F : κ → P) (h : κ → ℕ)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a) :
    Representation K G (coefficientSpace F h) :=
  (targetRepresentation ρ).subrepresentation (coefficientSpace F h)
    (fun g v hv => targetRepresentation_preserves_coefficient ρ F h hF g v hv)

/-- The quotient action on the literal `J/H`, before identifying its image. -/
def defectQuotientRepresentation (ρ : G →* GL) (F : κ → P) (h : κ → ℕ) (t : K)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a) :
    Representation K G (Defect F h t) :=
  (coefficientRepresentation ρ F h hF).quotient
    ((hit F h t).comap (coefficientSpace F h).subtype)
    (fun g v hv => targetRepresentation_preserves_hit ρ F h t hF g v hv)

theorem defectEquivImage_intertwines (ρ : G →* GL) (F : κ → P) (h : κ → ℕ) (t : K)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a)
    (g : G) (x : Defect F h t) :
    defectEquivImage F h t (defectQuotientRepresentation ρ F h t hF g x) =
      defectRepresentation ρ F h t hF g (defectEquivImage F h t x) := by
  obtain ⟨v, rfl⟩ := ((hit F h t).comap (coefficientSpace F h).subtype).mkQ_surjective x
  apply Subtype.ext
  rfl

def homogeneousPolynomialRepresentation (ρ : G →* GL) (w : ι → ℕ) (d : ℕ)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K)) :
    Representation K G (weightedHomogeneousSubmodule K w d) :=
  (JacobianLinearAction.polynomialRepresentation ρ).subrepresentation
    (weightedHomogeneousSubmodule K w d)
    (fun g p hp => JacobianLinearAction.polynomialRepresentation_preserves_weights ρ w hW g hp)

theorem potentialToQuotient_intertwines (ρ : G →* GL)
    (F : κ → P) (h : κ → ℕ) (t : K)
    (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a)
    (g : G) (p : P) :
    potentialToQuotient F h t (JacobianLinearAction.polynomialRepresentation ρ g p) =
      hitQuotientRepresentation ρ F h t hF g (potentialToQuotient F h t p) := by
  change (hit F h t).mkQ (potential F (JacobianLinearAction.polynomialRepresentation ρ g p)) =
    hitQuotientRepresentation ρ F h t hF g ((hit F h t).mkQ (potential F p))
  rw [hitQuotientRepresentation_mk]
  congr 1
  funext a
  change F a * linearSubst (ρ g⁻¹ : Matrix ι ι K) p =
    linearSubst (ρ g⁻¹ : Matrix ι ι K) (F a * p)
  rw [map_mul, hF]

/-- The canonical `p ↦ [F p]` isomorphism is equivariant for arbitrary
invertible linear substitutions preserving the weights and every equation.
No permutation-only, diagonal-only, or supplied stability hypothesis occurs. -/
theorem homogeneousDefectEquiv_intertwines (ρ : G →* GL)
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h))
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K))
    (hFix : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a)
    (g : G) (p : weightedHomogeneousSubmodule K w d) :
    homogeneousDefectEquiv F h w t d hh hF hC hres
        (homogeneousPolynomialRepresentation ρ w d hW g p) =
      defectRepresentation ρ F h t hFix g
        (homogeneousDefectEquiv F h w t d hh hF hC hres p) := by
  apply Subtype.ext
  exact potentialToQuotient_intertwines ρ F h t hFix g p

end PaperVerification.VectorEuler
