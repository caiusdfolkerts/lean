module

public import ToricPower.DiagonalFanLabels
public import ToricPower.DiagonalChartAugmentation
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation

/-!
# The local augmentation weights are precisely the toric diagonal weights

The numerical arrangement matrix is constructed from the actual fan rays
and a basis of the full integral character lattice.  A nonempty numerical
strip gives a real functional nonnegative on the first cone whose difference
from the total character is nonnegative on the second.  Hence its total
character belongs to the dual semigroup of the intersection cone.

Conversely, the proved toric separation theorem decomposes any such
integral character as a sum of characters nonnegative on the two cones.
This supplies an integral point of the literal strip.  Thus the target
weights of the cellular augmentation are exactly, without a saturation
or finite-character restriction, the monomials of the actual intersection
chart. No smoothness or completeness hypothesis is needed here.

Candidate until the pinned compiler checks the complete source closure.
-/

@[expose] public noncomputable section

open TauCeti.Toric ToricPower.IntegralArrangement Set
open scoped Classical BigOperators

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

/-- The actual rays contained in one fan cone, in the chosen enumeration. -/
def fanConeRaySet (σ : fan.cones) : Set (Fin s) :=
  {ρ | (rays ρ).toCone ≤ σ}

/-- Every primitive fan-ray vector belongs to each cone containing that
ray; no full-dimensional chart is chosen. -/
theorem fanRayPrimitiveGenerator_mem_cone (σ : fan.cones) (ρ : fan.Ray)
    (hρ : ρ.toCone ≤ σ) : latticeMap (fanRayPrimitiveGenerator fan ρ) ∈ σ.val := by
  apply hρ
  exact primitiveGenerator_mem fan.lattice (fan.isToricCone ρ.val.property)
    (Fan.Ray.toToricRay fan ρ ρ.val le_rfl)

theorem fanArrangementMatrix_basis_character (m : N →+ ℤ) (ρ : Fin s) :
    rayPairing A (basis.equivFun m) ρ = m (fanRayPrimitiveGenerator fan (rays ρ)) := by
  simpa only [Equiv.symm_apply_apply,LinearEquiv.symm_apply_apply] using
    fanArrangementMatrix_character fan basis rays (basis.equivFun m) (rays ρ)

/-- A coordinate real character is an actual real-linear functional on
the lattice's ambient real vector space. -/
def fanCoordinateRealCharacter (x : Fin n → ℝ) : V →ₗ[ℝ] ℝ :=
  ∑ j, x j • fan.lattice.realCharacter (basis j)

theorem fanCoordinateRealCharacter_ray (x : Fin n → ℝ) (ρ : Fin s) :
    fanCoordinateRealCharacter fan basis x
        (latticeMap (fanRayPrimitiveGenerator fan (rays ρ))) =
      integralRowForm A ρ x := by
  simp only [fanCoordinateRealCharacter,LinearMap.sum_apply,LinearMap.smul_apply,
    fan.lattice.realCharacter_apply,smul_eq_mul]
  simp only [integralRowForm,fanArrangementMatrix]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- The primitive-ray test applies to every real-linear functional,
not only to integral characters. -/
theorem linear_nonnegative_on_toric_cone (σ : fan.cones) (φ : V →ₗ[ℝ] ℝ)
    (hφ : ∀ ρ : ToricRay σ.val,
      0 ≤ φ (latticeMap (primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ))) :
    ∀ v ∈ σ.val, 0 ≤ φ v := by
  have hdual : φ ∈ PointedCone.dual (Module.Dual.eval ℝ V)
      (latticeMap '' Set.range
        (primitiveGenerator fan.lattice (fan.isToricCone σ.property))) := by
    rintro _ ⟨_,⟨ρ,rfl⟩,rfl⟩
    exact hφ ρ
  rw [← PointedCone.dual_hull,
    (fan.isToricCone σ.property).hull_primitiveGenerator fan.lattice] at hdual
  exact fun v hv => hdual hv

/-- Numerical ray inequalities are equivalent to actual membership in
the integral dual semigroup of the cone. -/
theorem fan_rayCharacterMonoid_iff (σ : fan.cones) (u : Fin n → ℤ) :
    u ∈ rayCharacterMonoid A (fanConeRaySet fan rays σ) ↔
      basis.equivFun.symm u ∈ dualSemigroup fan.lattice σ.val := by
  constructor
  · intro hu
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone σ.property)]
    intro ρ
    let ρf := Fan.Ray.ofToricRay fan σ ρ
    have hρ : rays.symm ρf ∈ fanConeRaySet fan rays σ := by
      change (rays (rays.symm ρf)).toCone ≤ σ
      rw [Equiv.apply_symm_apply]
      exact Fan.Ray.toCone_ofToricRay_le fan σ ρ
    have h := hu (rays.symm ρf) hρ
    rw [fanArrangementMatrix_character,fanRayPrimitiveGenerator_ofToricRay] at h
    exact h
  · intro hu ρ hρ
    have h := (mem_dualSemigroup fan.lattice (basis.equivFun.symm u)).mp hu
      (fanRayPrimitiveGenerator_mem_cone fan σ (rays ρ) hρ)
    rw [fan.lattice.realCharacter_apply] at h
    have h' : 0 ≤ basis.equivFun.symm u (fanRayPrimitiveGenerator fan (rays ρ)) := by
      exact_mod_cast h
    rw [← fanArrangementMatrix_character fan basis rays u (rays ρ)] at h'
    simpa only [Equiv.symm_apply_apply] using h'

/-- A coordinate presentation of the genuine cone semigroup, retaining
all ambient lattice directions for non-full-dimensional cones. -/
def fanRayCharacterMonoidEquiv (σ : fan.cones) :
    rayCharacterMonoid A (fanConeRaySet fan rays σ) ≃+
      dualSemigroup fan.lattice σ.val where
  toFun u := ⟨basis.equivFun.symm u.val,
    (fan_rayCharacterMonoid_iff fan basis rays σ u.val).mp u.property⟩
  invFun m := ⟨basis.equivFun m.val,
    (fan_rayCharacterMonoid_iff fan basis rays σ (basis.equivFun m.val)).mpr
      (by simpa only [LinearEquiv.symm_apply_apply] using m.property)⟩
  left_inv u := by apply Subtype.ext; exact basis.equivFun.apply_symm_apply u.val
  right_inv m := by apply Subtype.ext; exact basis.equivFun.symm_apply_apply m.val
  map_add' u v := by apply Subtype.ext; exact basis.equivFun.symm.map_add u.val v.val

/-- The exact nonemptiness criterion for the actual numerical weight
strip, identified with the actual intersection-chart semigroup. -/
theorem fan_diagonalStrip_nonempty_iff (σ τ : fan.cones) (u : Fin n → ℤ) :
    (diagonalStrip A (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ) u).Nonempty ↔
      basis.equivFun.symm u ∈ dualSemigroup fan.lattice (σ.val ⊓ τ.val) := by
  constructor
  · rintro ⟨x,hx⟩
    let φ := fanCoordinateRealCharacter fan basis x
    have hleft : ∀ v ∈ σ.val, 0 ≤ φ v := by
      apply linear_nonnegative_on_toric_cone fan σ φ
      intro ρ
      let ρf := Fan.Ray.ofToricRay fan σ ρ
      have hr : rays.symm ρf ∈ fanConeRaySet fan rays σ := by
        change (rays (rays.symm ρf)).toCone ≤ σ
        rw [Equiv.apply_symm_apply]
        exact Fan.Ray.toCone_ofToricRay_le fan σ ρ
      have h := hx.1 (rays.symm ρf) hr
      rw [← fanCoordinateRealCharacter_ray] at h
      simpa only [ρf, φ, Equiv.apply_symm_apply,
        fanRayPrimitiveGenerator_ofToricRay] using h
    have hright : ∀ v ∈ τ.val, 0 ≤ (fan.lattice.realCharacter (basis.equivFun.symm u) - φ) v := by
      apply linear_nonnegative_on_toric_cone fan τ _
      intro ρ
      let ρf := Fan.Ray.ofToricRay fan τ ρ
      have hr : rays.symm ρf ∈ fanConeRaySet fan rays τ := by
        change (rays (rays.symm ρf)).toCone ≤ τ
        rw [Equiv.apply_symm_apply]
        exact Fan.Ray.toCone_ofToricRay_le fan τ ρ
      have h := hx.2 (rays.symm ρf) hr
      rw [← fanCoordinateRealCharacter_ray,fanArrangementMatrix_character] at h
      simp only [ρf, Equiv.apply_symm_apply,fanRayPrimitiveGenerator_ofToricRay] at h
      simp only [LinearMap.sub_apply,fan.lattice.realCharacter_apply]
      simpa only [φ] using sub_nonneg.mpr h
    rw [mem_dualSemigroup]
    intro v hv
    have h₁ := hleft v hv.1
    have h₂ := hright v hv.2
    change 0 ≤ fan.lattice.realCharacter (basis.equivFun.symm u) v - φ v at h₂
    linarith
  · intro hu
    rw [fan.dualSemigroup_inf_eq_sup σ.property τ.property,AddSubmonoid.mem_sup] at hu
    obtain ⟨a,ha,b,hb,hab⟩ := hu
    refine ⟨latticeLift (basis.equivFun a),?_,?_⟩
    · intro ρ hρ
      rw [integralRowForm_latticeLift,fanArrangementMatrix_basis_character]
      have h := (mem_dualSemigroup fan.lattice a).mp ha
        (fanRayPrimitiveGenerator_mem_cone fan σ (rays ρ) hρ)
      simpa only [fan.lattice.realCharacter_apply] using h
    · intro ρ hρ
      rw [integralRowForm_latticeLift,fanArrangementMatrix_basis_character]
      have hbρ := (mem_dualSemigroup fan.lattice b).mp hb
        (fanRayPrimitiveGenerator_mem_cone fan τ (rays ρ) hρ)
      rw [fan.lattice.realCharacter_apply] at hbρ
      have habρ := congrArg (fun m : N →+ ℤ => m (fanRayPrimitiveGenerator fan (rays ρ))) hab
      have hmatrix := fanArrangementMatrix_character fan basis rays u (rays ρ)
      simp only [Equiv.symm_apply_apply] at hmatrix
      rw [hmatrix]
      have hsum :
          (a (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) +
            (b (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) =
          (basis.equivFun.symm u (fanRayPrimitiveGenerator fan (rays ρ)) : ℝ) := by
        exact_mod_cast habρ
      linarith

/-- The target basis of the actual chart augmentation is in explicit
bijection with the monomials of the genuine intersection chart. -/
def diagonalSupportedWeightEquiv (σ τ : fan.cones) :
    DiagonalSupportedWeight A (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ) ≃
      dualSemigroup fan.lattice (σ.val ⊓ τ.val) where
  toFun u := ⟨basis.equivFun.symm u.val,
    (fan_diagonalStrip_nonempty_iff fan basis rays σ τ u.val).mp u.property⟩
  invFun m := ⟨basis.equivFun m.val,
    (fan_diagonalStrip_nonempty_iff fan basis rays σ τ (basis.equivFun m.val)).mpr
      (by simpa only [LinearEquiv.symm_apply_apply] using m.property)⟩
  left_inv u := by apply Subtype.ext; exact basis.equivFun.apply_symm_apply u.val
  right_inv m := by apply Subtype.ext; exact basis.equivFun.symm_apply_apply m.val

end ToricPower
