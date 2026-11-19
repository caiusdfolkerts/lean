module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv

/-! Compatibility names for the original public cone-map helpers.
All fan equivalence definitions and theorems are owned by the canonical Tau Ceti module. -/

@[expose] public section
namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

def coneMap (e : FanEquiv Φ Ψ) : Φ.cones → Ψ.cones := fun σ ↦
  ⟨PointedCone.map (e.realEquiv : V →ₗ[ℝ] V') σ.1, (e.map_mem σ.1).2 σ.2⟩

@[simp]
theorem coneMap_coe (e : FanEquiv Φ Ψ) (σ : Φ.cones) :
    (coneMap e σ : PointedCone ℝ V') =
      PointedCone.map (e.realEquiv : V →ₗ[ℝ] V') σ.1 :=
  (rfl)


end TauCeti.Toric.FanEquiv
