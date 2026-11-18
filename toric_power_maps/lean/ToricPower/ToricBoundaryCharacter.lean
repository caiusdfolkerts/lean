module

public import ToricPower.DivisorWeightCartierAtlas
public import TauCeti.Geometry.Toric.Algebraic.FaceLocalization

/-!
# The boundary divisor of an affine toric chart

For a cone `σ`, put coefficient zero on its rays and coefficient one on
all remaining rays. Smoothness gives integral local equations. Their
nonvanishing face in another cone `τ` is exactly `τ ∩ σ`, so the complement
of this effective Cartier boundary is the actual chart `U_σ`.

The chosen equation on `σ` itself is literally zero. This normalization
will let a local section on `U_σ` be extended without an extra unit factor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TauCeti.Toric

attribute [local instance] Classical.propDecidable

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The reduced invariant boundary outside the chart indexed by `σ`. -/
def toricChartBoundaryCoefficients (fan : Fan i) (σ : fan.cones) : fan.Ray → ℤ :=
  fun ρ => if ρ.toCone.val ≤ σ.val then 0 else 1

/-- Local boundary equations, normalized to be zero on the chosen chart. -/
def toricChartBoundaryCharacter (fan : Fan i) (regular : fan.IsRegular)
    (σ τ : fan.cones) : N →+ ℤ :=
  if τ = σ then 0 else
    coneDivisorCharacter fan regular (toricChartBoundaryCoefficients fan σ) τ

@[simp]
theorem toricChartBoundaryCharacter_self (fan : Fan i) (regular : fan.IsRegular)
    (σ : fan.cones) : toricChartBoundaryCharacter fan regular σ σ = 0 := by
  simp [toricChartBoundaryCharacter]

theorem toricChartBoundaryCharacter_ray (fan : Fan i) (regular : fan.IsRegular)
    (σ τ : fan.cones) (ρ : ToricRay τ.val) :
    toricChartBoundaryCharacter fan regular σ τ
        (primitiveGenerator fan.lattice (fan.isToricCone τ.property) ρ) =
      if ρ.toPointedCone ≤ σ.val then 0 else 1 := by
  classical
  by_cases h : τ = σ
  · subst τ
    simp [toricChartBoundaryCharacter, ρ.1.isFaceOf.le]
  · simp only [toricChartBoundaryCharacter, if_neg h, coneDivisorCharacter_ray,
      coneDivisorCoefficients, toricChartBoundaryCoefficients, Fan.Ray.toCone_ofToricRay]

theorem toricChartBoundaryCharacter_mem_dual (fan : Fan i) (regular : fan.IsRegular)
    (σ τ : fan.cones) :
    toricChartBoundaryCharacter fan regular σ τ ∈ dualSemigroup fan.lattice τ.val := by
  rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone τ.property)]
  intro ρ
  rw [toricChartBoundaryCharacter_ray]
  split_ifs <;> norm_num

/-- A ray is contained in a pointed cone precisely when its primitive
generator lies there. No simpliciality of the target cone is needed. -/
theorem toricRay_le_iff_primitiveGenerator_mem (lattice : IsIntegralLattice i)
    {τ : PointedCone ℝ V} (toric : IsToricCone i τ)
    (ρ : ToricRay τ) (F : PointedCone ℝ V) :
    ρ.toPointedCone ≤ F ↔ i (primitiveGenerator lattice toric ρ) ∈ F := by
  constructor
  · intro contained
    exact contained (primitiveGenerator_mem lattice toric ρ)
  · intro present
    rw [ρ.eq_hull_singleton (toric.salient.anti ρ.1.isFaceOf.le)
      (primitiveGenerator_mem lattice toric ρ)
      (by simpa using lattice.injective.ne (primitiveGenerator_ne_zero lattice toric ρ))]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr present)

/-- The boundary equation cuts precisely the overlap face with the chosen
affine chart, including when either cone has lower dimension. -/
theorem toricChartBoundaryCharacter_zeroFace (fan : Fan i) (regular : fan.IsRegular)
    (σ τ : fan.cones) :
    τ.val ⊓ PointedCone.ofSubmodule
        (LinearMap.ker (fan.lattice.realCharacter
          (toricChartBoundaryCharacter fan regular σ τ))) = (τ ⊓ σ).val := by
  let toric := fan.isToricCone τ.property
  apply PointedCone.inf_ker_eq_of_eq_hull
    (toric.hull_primitiveGenerator fan.lattice).symm
    (fan.isFaceOf_of_le τ.property (τ ⊓ σ).property inf_le_left)
  · rintro _ ⟨x, ⟨ρ, rfl⟩, rfl⟩
    rw [IsIntegralLattice.realCharacter_apply, toricChartBoundaryCharacter_ray]
    split_ifs <;> norm_num
  · rintro _ ⟨x, ⟨ρ, rfl⟩, rfl⟩
    rw [IsIntegralLattice.realCharacter_apply, toricChartBoundaryCharacter_ray]
    have hτ : i (primitiveGenerator fan.lattice toric ρ) ∈ τ.val :=
      ρ.1.isFaceOf.le (primitiveGenerator_mem fan.lattice toric ρ)
    rw [Fan.coe_inf, Submodule.mem_inf]
    simp only [hτ, true_and]
    rw [← toricRay_le_iff_primitiveGenerator_mem fan.lattice toric ρ σ.val]
    split_ifs <;> simp_all

end ToricPower

end
