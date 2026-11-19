module

public import ToricPower.DualDiagonalStrip
public import ToricPower.DiagonalToricWeights

/-!
# The exact supported characters of the dual diagonal

On the product of two smooth toric charts the open dual strip is
nonempty precisely when the total character has value at least `-1`
on every common ray. These are exactly the monomial inequalities for
the reduced toric boundary divisor on the intersection chart.

For sufficiency, choose integral characters taking value one on each
of the two cones. Decompose twice the desired character plus these
two local characters in the actual intersection dual semigroup.
Half the difference of the first character and the first summand is
an interior strip point. Thus strict endpoints require no unproved
relative-interior theorem and no full-dimensional cone hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric ToricPower.IntegralArrangement Set
open scoped Classical BigOperators

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

include regular

/-- Smoothness supplies an actual integral character taking value one
on every primitive ray of an arbitrary cone, including lower dimensions. -/
theorem fanCone_exists_unitCharacter (σ : fan.cones) :
    ∃ q : N →+ ℤ, ∀ ρ : fan.Ray, ρ.toCone ≤ σ →
      q (fanRayPrimitiveGenerator fan ρ) = 1 := by
  obtain ⟨q, hq⟩ := regularCone_exists_divisorCharacter fan.lattice
    (Fan.isRegular_iff.mp regular _ σ.property) (fun _ => (1 : ℤ))
  refine ⟨q, fun ρ hρ => ?_⟩
  let r := ρ.toToricRay fan σ hρ
  have rayEquality : Fan.Ray.ofToricRay fan σ r = ρ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have primitive := fanRayPrimitiveGenerator_ofToricRay fan σ r
  rw [rayEquality] at primitive
  rw [primitive]
  exact hq r

/-- Full integral character criterion for the actual open dual strip. -/
theorem fan_dualDiagonalStrip_nonempty_iff (σ τ : fan.cones) (u : Fin n → ℤ) :
    (dualDiagonalStrip A (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ) u).Nonempty ↔
      ∀ ρ : fan.Ray, ρ.toCone ≤ σ ⊓ τ →
        -1 ≤ basis.equivFun.symm u (fanRayPrimitiveGenerator fan ρ) := by
  constructor
  · rintro ⟨x, hx⟩ ρ hρ
    have hσ : rays.symm ρ ∈ fanConeRaySet fan rays σ := by
      change (rays (rays.symm ρ)).toCone ≤ σ
      rw [Equiv.apply_symm_apply]
      exact le_trans hρ inf_le_left
    have hτ : rays.symm ρ ∈ fanConeRaySet fan rays τ := by
      change (rays (rays.symm ρ)).toCone ≤ τ
      rw [Equiv.apply_symm_apply]
      exact le_trans hρ inf_le_right
    have upper := hx.1 (rays.symm ρ) hσ
    have lower := hx.2 (rays.symm ρ) hτ
    have integralBound : (-2 : ℤ) < rayPairing A u (rays.symm ρ) := by
      exact_mod_cast (show (-2 : ℝ) < (rayPairing A u (rays.symm ρ) : ℝ) by linarith)
    rw [fanArrangementMatrix_character] at integralBound
    omega
  · intro admissible
    obtain ⟨qσ, hσ⟩ := fanCone_exists_unitCharacter fan regular σ
    obtain ⟨qτ, hτ⟩ := fanCone_exists_unitCharacter fan regular τ
    let m := basis.equivFun.symm u
    let w : N →+ ℤ := m + m + qσ + qτ
    have nonnegative : w ∈ dualSemigroup fan.lattice (σ.val ⊓ τ.val) := by
      apply (mem_dualSemigroup_iff_primitiveGenerator fan.lattice
        (fan.isToricCone (σ ⊓ τ).property) w).mpr
      intro ρ
      let ρf := Fan.Ray.ofToricRay fan (σ ⊓ τ) ρ
      have common : ρf.toCone ≤ σ ⊓ τ := Fan.Ray.toCone_ofToricRay_le fan (σ ⊓ τ) ρ
      have bound := admissible ρf common
      have first := hσ ρf (le_trans common inf_le_left)
      have second := hτ ρf (le_trans common inf_le_right)
      rw [fanRayPrimitiveGenerator_ofToricRay] at bound first second
      change 0 ≤ m (primitiveGenerator fan.lattice (fan.isToricCone (σ ⊓ τ).property) ρ) +
        m (primitiveGenerator fan.lattice (fan.isToricCone (σ ⊓ τ).property) ρ) +
        qσ (primitiveGenerator fan.lattice (fan.isToricCone (σ ⊓ τ).property) ρ) +
        qτ (primitiveGenerator fan.lattice (fan.isToricCone (σ ⊓ τ).property) ρ)
      change -1 ≤ m (primitiveGenerator fan.lattice (fan.isToricCone (σ ⊓ τ).property) ρ)
        at bound
      omega
    rw [fan.dualSemigroup_inf_eq_sup σ.property τ.property,
      AddSubmonoid.mem_sup] at nonnegative
    obtain ⟨a, ha, b, hb, hab⟩ := nonnegative
    refine ⟨(1 / 2 : ℝ) • latticeLift (basis.equivFun (qσ - a)), ?_, ?_⟩
    · intro ρ hρ
      have nonnegative := (mem_dualSemigroup fan.lattice a).mp ha
        (fanRayPrimitiveGenerator_mem_cone fan σ (rays ρ) hρ)
      rw [fan.lattice.realCharacter_apply] at nonnegative
      have first := hσ (rays ρ) hρ
      rw [map_smul, integralRowForm_latticeLift, fanArrangementMatrix_basis_character,
        AddMonoidHom.sub_apply, Int.cast_sub, first]
      norm_num only [Int.cast_one, smul_eq_mul]
      linarith
    · intro ρ hρ
      have nonnegative := (mem_dualSemigroup fan.lattice b).mp hb
        (fanRayPrimitiveGenerator_mem_cone fan τ (rays ρ) hρ)
      rw [fan.lattice.realCharacter_apply] at nonnegative
      have second := hτ (rays ρ) hρ
      have total := congrArg (fun χ : N →+ ℤ => χ (fanRayPrimitiveGenerator fan (rays ρ))) hab
      change a (fanRayPrimitiveGenerator fan (rays ρ)) + b (fanRayPrimitiveGenerator fan (rays ρ)) =
        m (fanRayPrimitiveGenerator fan (rays ρ)) + m (fanRayPrimitiveGenerator fan (rays ρ)) +
        qσ (fanRayPrimitiveGenerator fan (rays ρ)) + qτ (fanRayPrimitiveGenerator fan (rays ρ))
        at total
      rw [second] at total
      have realTotal :
          (a (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) +
            (b (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) =
          (m (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) +
            (m (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) +
            (qσ (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) + 1 := by
        exact_mod_cast total
      have pairing := fanArrangementMatrix_character fan basis rays u (rays ρ)
      simp only [Equiv.symm_apply_apply] at pairing
      rw [map_smul, integralRowForm_latticeLift, fanArrangementMatrix_basis_character,
        AddMonoidHom.sub_apply, Int.cast_sub, pairing]
      change -(m (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) - 1 <
        (1 / 2 : ℝ) * ((qσ (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) -
          (a (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ))
      linarith

end ToricPower
