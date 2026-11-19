module

public import TauCeti.Geometry.Toric.Algebraic.Regular
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Integral translates of affine normal slices

On a regular cone, integral values on its primitive rays extend to an
ambient integral character. If the cone spans the normal space, its
entire affine annihilator slice is therefore an integral translate.
The complementary lattice basis coordinates are assigned zero.
-/

@[expose] public noncomputable section

open Set TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- Integral primitive-ray values determine the restriction of an actual
ambient integral character to the full real span of a regular cone. -/
theorem regularCone_realCharacter_agrees_on_span
    (hi : IsIntegralLattice i) (regular : IsRegularCone i σ)
    (x : Module.Dual ℝ V)
    (integral : ∀ ρ : ToricRay σ,
      ∃ z : ℤ, x (i (primitiveGenerator hi regular.toIsToricCone ρ)) = (z : ℝ)) :
    ∃ m : N →+ ℤ, ∀ v ∈ Submodule.span ℝ (σ : Set V), hi.realCharacter m v = x v := by
  classical
  let z : ToricRay σ → ℤ := fun ρ => Classical.choose (integral ρ)
  obtain ⟨l,basis,hbasis⟩ := regular.exists_basis_sum
  let m : N →+ ℤ :=
    (basis.constr ℤ (Sum.elim z (fun _ : Fin l => 0))).toAddMonoidHom
  have values (ρ : ToricRay σ) :
      m (primitiveGenerator hi regular.toIsToricCone ρ) = z ρ := by
    rw [← (hbasis ρ).eq_primitiveGenerator hi regular.toIsToricCone]
    simp [m]
  have generators : i '' Set.range (primitiveGenerator hi regular.toIsToricCone) ⊆
      (LinearMap.ker (hi.realCharacter m - x) : Set V) := by
    rintro _ ⟨_,⟨ρ,rfl⟩,rfl⟩
    change hi.realCharacter m (i (primitiveGenerator hi regular.toIsToricCone ρ)) -
      x (i (primitiveGenerator hi regular.toIsToricCone ρ)) = 0
    rw [hi.realCharacter_apply,values,Classical.choose_spec (integral ρ)]
    simp only [z,sub_self]
  have cone : σ ≤ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m - x)) := by
    rw [← regular.toIsToricCone.hull_primitiveGenerator hi]
    exact Submodule.span_le.mpr generators
  have span : Submodule.span ℝ (σ : Set V) ≤ LinearMap.ker (hi.realCharacter m - x) :=
    Submodule.span_le.mpr cone
  refine ⟨m,fun v hv => ?_⟩
  exact sub_eq_zero.mp (span hv)

/-- A regular cone spanning a normal space supplies the integral
translate of the complete affine annihilator slice. -/
theorem regularCone_integralAffineSlice
    (hi : IsIntegralLattice i) (regular : IsRegularCone i σ)
    (W : Submodule ℝ V) (spans : Submodule.span ℝ (σ : Set V) = W)
    (x : Module.Dual ℝ V)
    (integral : ∀ ρ : ToricRay σ,
      ∃ z : ℤ, x (i (primitiveGenerator hi regular.toIsToricCone ρ)) = (z : ℝ)) :
    ∃ m : N →+ ℤ, ∀ y : Module.Dual ℝ V,
      y - x ∈ W.dualAnnihilator ↔
        y - hi.realCharacter m ∈ W.dualAnnihilator := by
  obtain ⟨m,agrees⟩ := regularCone_realCharacter_agrees_on_span hi regular x integral
  have shift : hi.realCharacter m - x ∈ W.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    change hi.realCharacter m v - x v = 0
    rw [agrees v (spans.symm ▸ hv),sub_self]
  refine ⟨m,fun y => ⟨?_,?_⟩⟩
  · intro h
    convert W.dualAnnihilator.sub_mem h shift using 1 <;> abel
  · intro h
    convert W.dualAnnihilator.add_mem h shift using 1 <;> abel

end ToricPower

end
