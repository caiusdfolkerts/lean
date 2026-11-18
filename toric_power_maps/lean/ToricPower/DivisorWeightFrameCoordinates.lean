module

public import ToricPower.DivisorWeightFrameValues

/-!
# Computational values of the actual affine residue frames

The direct-sum equivalence is conjugated by the specified local Cartier
trivializations. Its image on each standard generator is the regular
monomial χ^(q_b+u−ell q_floor). These are exactly the local values of the
canonical global rational-function morphisms.

Development source: this file is unverified until its current source hash
has passed the ordinary pinned checker.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric MonoidAlgebra

namespace ToricPower


universe u v w

variable {N : Type u} {V : Type v} {κ : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [Fintype κ] {i : N →+ V}

/-- Bundling a linear equivalence does not change its underlying map. -/
theorem moduleLinearEquiv_hom_apply {R : Type*} {M P : Type w} [Ring R]
    [AddCommGroup M] [AddCommGroup P] [Module R M] [Module R P]
    (e : M ≃ₗ[R] P) (x : M) : e.toModuleIso.hom x = e x := rfl

/-- The inverse bundled map is the inverse linear equivalence. -/
theorem moduleLinearEquiv_inv_apply {R : Type*} {M P : Type w} [Ring R]
    [AddCommGroup M] [AddCommGroup P] [Module R M] [Module R P]
    (e : M ≃ₗ[R] P) (x : P) : e.toModuleIso.inv x = e.symm x := rfl

/-- A pointwise module isomorphism acts pointwise, also after bundling. -/
theorem modulePiCongrRight_hom_apply {R : Type*} [Ring R] {I : Type*}
    {M P : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (M i)] [∀ i, Module R (P i)]
    (e : ∀ i, M i ≃ₗ[R] P i) (x : ∀ i, M i) (j : I) :
    (LinearEquiv.piCongrRight e) x j = e j (x j) := rfl

/-- The actual chart frame has its prescribed Laurent value. -/
theorem toricDivisorChartModuleTrivialization_val (fan : Fan i)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (cone : fan.cones)
    (a : affineCoordinateRing fan.lattice cone.val) :
    (toricDivisorChartModuleTrivialization fan regular basis b cone a).val =
      mapDomain (rayChartPowerMonoidHom
        (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis) 1)
        (affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis a) *
      single (Multiplicative.ofAdd (-(basis.equivFun
        (coneDivisorCharacter fan regular b cone)))) 1 := by
  let A := characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis
  let q := basis.equivFun (coneDivisorCharacter fan regular b cone)
  have hq : coneDivisorCoefficients fan b cone = rayMap A q := by
    funext ρ
    change coneDivisorCoefficients fan b cone ρ =
      rayMap (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
        (basis.equivFun (coneDivisorCharacter fan regular b cone)) ρ
    rw [characterRayMatrix_apply, coneDivisorCharacter_ray]
  exact divisorCartierTrivialization_val ℂ A (coneDivisorCoefficients fan b cone) q hq
    (affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis a)

/-- In the ordinary divisor coordinates, a standard residue vector is the
corresponding local Cartier generator. This computation is separated from all
bundled isomorphism compositions. -/
theorem toricResidueFrameInput_single (fan : Fan i) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (cone : fan.cones) (residue : LatticeResidues κ ell)
    (hC : powerCoefficient (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
        (coneDivisorCoefficients fan b cone) (ell : ℤ) (latticeResidueRepresentative residue) =
      rayMap (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
        (basis.equivFun (coneDivisorCharacter fan regular
          (toricResidueCoefficients fan b ell
            (basis.equivFun.symm (latticeResidueRepresentative residue))) cone))) :
    (toricDivisorResidueCoefficientPiEquiv fan basis b ell cone).symm
      ((LinearEquiv.piCongrRight (fun other : LatticeResidues κ ell =>
        toricDivisorChartModuleTrivialization fan regular basis
          (toricResidueCoefficients fan b ell
            (basis.equivFun.symm (latticeResidueRepresentative other))) cone))
        (Pi.single residue 1)) =
    Pi.single residue (divisorCartierTrivialization ℂ
      (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
      (powerCoefficient (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
        (coneDivisorCoefficients fan b cone) (ell : ℤ) (latticeResidueRepresentative residue))
      (basis.equivFun (coneDivisorCharacter fan regular
        (toricResidueCoefficients fan b ell
          (basis.equivFun.symm (latticeResidueRepresentative residue))) cone)) hC 1) := by
  classical
  let frame := fun other : LatticeResidues κ ell =>
    toricDivisorChartModuleTrivialization fan regular basis
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative other))) cone
  apply (toricDivisorResidueCoefficientPiEquiv fan basis b ell cone).injective
  rw [LinearEquiv.apply_symm_apply]
  funext other
  apply Subtype.ext
  have first := LinearEquiv.piCongrRight_apply frame (Pi.single residue 1) other
  have last := toricDivisorResidueCoefficientPiEquiv_apply_val fan basis b ell cone
    (Pi.single residue (divisorCartierTrivialization ℂ
      (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
      (powerCoefficient (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
        (coneDivisorCoefficients fan b cone) (ell : ℤ) (latticeResidueRepresentative residue))
      (basis.equivFun (coneDivisorCharacter fan regular
        (toricResidueCoefficients fan b ell
          (basis.equivFun.symm (latticeResidueRepresentative residue))) cone)) hC 1)) other
  refine (congrArg Subtype.val first).trans (Eq.trans ?_ last.symm)
  by_cases same : other = residue
  · subst other
    simp only [Pi.single_eq_same]
    let A := characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis
    let q := basis.equivFun (coneDivisorCharacter fan regular
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue))) cone)
    let e := affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis
    have unit_value := congrArg
      (fun a => mapDomain (rayChartPowerMonoidHom A 1) a *
        single (Multiplicative.ofAdd (-q)) (1 : ℂ)) e.map_one
    exact (toricDivisorChartModuleTrivialization_val fan regular basis
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue))) cone 1).trans
      (unit_value.trans (divisorCartierTrivialization_val ℂ A _ q hC 1).symm)
  · simp only [Pi.single_eq_of_ne same, map_zero, Submodule.coe_zero]

end ToricPower
