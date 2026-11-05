module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.LinearMap.End

/-! # The actual linear action on a stable quotient -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.QuotientLinearAction

variable {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]

def action (ρ : G →* Module.End K V) (U : Submodule K V)
    (hU : ∀ g x, x ∈ U → ρ g x ∈ U) : G →* Module.End K (V ⧸ U) where
  toFun g := U.mapQ U (ρ g) (fun _ hx => hU g _ hx)
  map_one' := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := U.mkQ_surjective z
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, map_one, Module.End.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := U.mkQ_surjective z
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, map_mul, Module.End.mul_apply]

theorem action_mkQ (ρ : G →* Module.End K V) (U : Submodule K V)
    (hU : ∀ g x, x ∈ U → ρ g x ∈ U) (g : G) (x : V) :
    action ρ U hU g (U.mkQ x) = U.mkQ (ρ g x) := rfl

theorem action_preserves_image_piece {D : Type*}
    (ρ : G →* Module.End K V) (U : Submodule K V)
    (hU : ∀ g x, x ∈ U → ρ g x ∈ U) (A : D → Submodule K V)
    (hA : ∀ g d x, x ∈ A d → ρ g x ∈ A d) (g : G) (d : D)
    (z : V ⧸ U) (hz : z ∈ (A d).map U.mkQ) :
    action ρ U hU g z ∈ (A d).map U.mkQ := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [action_mkQ]
  exact ⟨ρ g x, hA g d x hx, rfl⟩

end PaperVerification.QuotientLinearAction
