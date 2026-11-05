module

public import PaperVerification.JacobianEquivariantTowers
public import PaperVerification.JacobianEquivariantDefect
public import Mathlib.Algebra.Exact.Basic

/-!
# The natural equivariant short exact sequence

The projection from the literal hit quotient to the actual Milnor quotient
has kernel the literal Jacobian defect. Both maps are induced from polynomial
representatives and intertwine the actual coordinate actions. A homogeneous
equivariant section is constructed by averaging polynomial Milnor lifts and
then taking their actual classes modulo the hit space.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.JacobianLinearAction

open MvPolynomial JacobianDivergence

variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
variable [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ

/-- The natural projection `P/H_t(F) → P/J(F)`, induced by the identity on
polynomials and the proved inclusion of the hit space in the Jacobian ideal. -/
def hitToMilnor (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    (P ⧸ EulerJacobian.hit (gradient F) F t) →ₗ[K] MilnorQuotient F :=
  Submodule.factor (hit_le_jacobian F w h t hh hF)

@[simp] theorem hitToMilnor_mk (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) (p : P) :
    hitToMilnor F w h t hh hF ((EulerJacobian.hit (gradient F) F t).mkQ p) =
      (jacobianSubmodule F).mkQ p := rfl

theorem hitToMilnor_surjective (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    Function.Surjective (hitToMilnor F w h t hh hF) := by
  intro x
  obtain ⟨p, rfl⟩ := (jacobianSubmodule F).mkQ_surjective x
  exact ⟨(EulerJacobian.hit (gradient F) F t).mkQ p, rfl⟩

theorem hitToMilnor_kernel (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    LinearMap.ker (hitToMilnor F w h t hh hF) = defectImage F t := by
  change LinearMap.ker (Submodule.factor (hit_le_jacobian F w h t hh hF)) =
    (jacobianSubmodule F).map (EulerJacobian.hit (gradient F) F t).mkQ
  rw [Submodule.factor, Submodule.ker_mapQ, Submodule.comap_id]

theorem hitToMilnor_intertwines (ρ : G →* GL)
    (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (g : G) (x : P ⧸ EulerJacobian.hit (gradient F) F t) :
    hitToMilnor F w h t hh hF (hitQuotientRepresentation ρ F t hFix g x) =
      milnorRepresentation ρ F hFix g (hitToMilnor F w h t hh hF x) := by
  obtain ⟨p, rfl⟩ := (EulerJacobian.hit (gradient F) F t).mkQ_surjective x
  rfl

/-- The natural quotient projection preserves every actual homogeneous piece. -/
theorem hitToMilnor_preserves_components
    (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (d : ℕ) (x : P ⧸ EulerJacobian.hit (gradient F) F t)
    (hx : x ∈ EulerResonance.quotientComponent w d
      (EulerJacobian.hit (gradient F) F t)) :
    hitToMilnor F w h t hh hF x ∈
      EulerResonance.quotientComponent w d (jacobianSubmodule F) := by
  rw [EulerResonance.quotientComponent_eq_map] at hx ⊢
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨p, hp, rfl⟩

/-- The natural map from the literal `J(F)/H_t(F)` to `P/H_t(F)`. -/
def defectInjection (F : P) (t : K) :
    DefectQuotient F t →ₗ[K] (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (defectImage F t).subtype.comp (defectQuotientEquivImage F t).toLinearMap

@[simp] theorem defectInjection_mk (F : P) (t : K) (p : jacobianSubmodule F) :
    defectInjection F t
        (((EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype).mkQ p) =
      (EulerJacobian.hit (gradient F) F t).mkQ p.val := rfl

theorem defectInjection_injective (F : P) (t : K) :
    Function.Injective (defectInjection F t) := by
  intro x y hxy
  exact (defectQuotientEquivImage F t).injective (Subtype.ext hxy)

theorem defectInjection_range (F : P) (t : K) :
    LinearMap.range (defectInjection F t) = defectImage F t := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (defectQuotientEquivImage F t x).property
  · intro hy
    obtain ⟨x, hx⟩ := (defectQuotientEquivImage F t).surjective ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

theorem defectInjection_intertwines (ρ : G →* GL) (F : P) (t : K)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (g : G) (x : DefectQuotient F t) :
    defectInjection F t (defectQuotientRepresentation ρ F t hFix g x) =
      hitQuotientRepresentation ρ F t hFix g (defectInjection F t x) :=
  congrArg Subtype.val (defectQuotientEquivImage_intertwines ρ F t hFix g x)

/-- Exactness of the paper's actual natural sequence, with both endpoint
conditions recorded explicitly. -/
theorem natural_short_exact (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    Function.Injective (defectInjection F t) ∧
      Function.Exact (defectInjection F t) (hitToMilnor F w h t hh hF) ∧
      Function.Surjective (hitToMilnor F w h t hh hF) := by
  refine ⟨defectInjection_injective F t, ?_, hitToMilnor_surjective F w h t hh hF⟩
  rw [LinearMap.exact_iff, hitToMilnor_kernel, defectInjection_range]

/-- The natural short exact sequence splits by an actual homogeneous
coordinate-equivariant map. The polynomial section is constructed by the
preceding finite-group averaging theorem, not supplied as an assumption. -/
theorem exists_equivariant_homogeneous_hit_section [Fintype G] {n : ℕ}
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ)
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hFix : ∀ g, linearSubst (ρ g : Matrix (Fin n) (Fin n) K) F = F)
    (hW : ∀ g, RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) K)) :
    ∃ s : MilnorQuotient F →ₗ[K]
      (MvPolynomial (Fin n) K ⧸ EulerJacobian.hit (gradient F) F t),
      (∀ x, hitToMilnor F w h t hh hF (s x) = x) ∧
      (∀ g x, s (milnorRepresentation ρ F hFix g x) =
        hitQuotientRepresentation ρ F t hFix g (s x)) ∧
      ∀ d x, x ∈ EulerResonance.quotientComponent w d (jacobianSubmodule F) →
        s x ∈ EulerResonance.quotientComponent w d
          (EulerJacobian.hit (gradient F) F t) := by
  obtain ⟨s, hsq, hsG, hsgrade⟩ :=
    exists_actual_equivariant_milnor_section F w h hF ρ hFix hW
  let q : MilnorQuotient F →ₗ[K]
      (MvPolynomial (Fin n) K ⧸ EulerJacobian.hit (gradient F) F t) :=
    (EulerJacobian.hit (gradient F) F t).mkQ.comp s
  refine ⟨q, ?_, ?_, ?_⟩
  · intro x
    change hitToMilnor F w h t hh hF
      ((EulerJacobian.hit (gradient F) F t).mkQ (s x)) = x
    rw [hitToMilnor_mk, hsq]
  · intro g x
    change (EulerJacobian.hit (gradient F) F t).mkQ
      (s (milnorRepresentation ρ F hFix g x)) =
        hitQuotientRepresentation ρ F t hFix g
          ((EulerJacobian.hit (gradient F) F t).mkQ (s x))
    rw [hsG, hitQuotientRepresentation_mk]
  · intro d x hx
    rw [EulerResonance.quotientComponent_eq_map]
    exact ⟨s x, hsgrade d x hx, rfl⟩

end PaperVerification.JacobianLinearAction
