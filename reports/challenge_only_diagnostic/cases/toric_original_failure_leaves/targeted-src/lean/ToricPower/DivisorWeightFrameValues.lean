module

public import ToricPower.DivisorWeightToricAffine

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

section Algebra

variable {ι κ : Type*} [Fintype κ]

/-- Inverse Cartier coordinates are multiplication by the local equation. -/
theorem divisorCartierTrivialization_symm_ambient (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (q : κ → ℤ) (hq : b = rayMap A q)
    (x : DivisorSectionModule R A b 1) :
    mapDomain (rayChartPowerMonoidHom A 1)
        ((divisorCartierTrivialization R A b q hq).symm x) =
      rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd q) 1 := by
  have h := congrArg (fun y : DivisorSectionModule R A b 1 =>
      rayPowerLaurentValue R A 1 y.1)
    ((divisorCartierTrivialization R A b q hq).apply_symm_apply x)
  change mapDomain (rayChartPowerMonoidHom A 1)
      ((divisorCartierTrivialization R A b q hq).symm x) *
      single (Multiplicative.ofAdd (-q)) 1 = rayPowerLaurentValue R A 1 x.1 at h
  rw [← h]
  simp [mul_assoc, single_mul_single, ← MonoidAlgebra.one_def]

/-- The sum map has the advertised value on a single arbitrary summand. -/
theorem divisorResidueSum_pi_single (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (u : LatticeResidues κ ell)
    (x : DivisorSectionModule R A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1) :
    divisorResidueSum R A b ell hell (Pi.single u x) =
      divisorResidueSummand R A b ell hell u x := by
  classical
  simp only [divisorResidueSum, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rw [Finset.sum_eq_single u]
  · simp only [Pi.single_eq_same]
  · intro v _ h
    rw [Pi.single_eq_of_ne h, map_zero]
  · intro h
    exact (h (Finset.mem_univ u)).elim

end Algebra

universe u v

variable {N : Type u} {V : Type v} {κ : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [Fintype κ] {i : N →+ V}

/-- The literal coordinate equivalence, expressed in all source and target
Cartier frames, is a genuine equivalence of modules for the chart power map. -/
def toricFramedResidueModuleIso (fan : Fan i) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) (cone : fan.cones) :
    ModuleCat.of (affineCoordinateRing fan.lattice cone.val)
      (LatticeResidues κ ell → affineCoordinateRing fan.lattice cone.val) ≅
    (ModuleCat.restrictScalars (chartPowerRingHom fan cone ell).hom).obj
      (ModuleCat.of (affineCoordinateRing fan.lattice cone.val)
        (affineCoordinateRing fan.lattice cone.val)) :=
  (LinearEquiv.piCongrRight (fun residue : LatticeResidues κ ell =>
    toricDivisorChartModuleTrivialization fan regular basis
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue))) cone)).toModuleIso ≪≫
    (toricDivisorPowerModuleIso fan basis b ell hell cone).symm ≪≫
    (ModuleCat.restrictScalars (chartPowerRingHom fan cone ell).hom).mapIso
      (toricDivisorChartModuleTrivialization fan regular basis b cone).symm.toModuleIso

/-- The frame exponent calculation is literal in the chosen lattice basis. -/
theorem normalizedToricResidueCharacter_coordinates (fan : Fan i) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ) (ell : ℕ)
    (residue : LatticeResidues κ ell) (cone : fan.cones) :
    basis.equivFun (normalizedToricResidueCharacter fan regular b ell
      (basis.equivFun.symm (latticeResidueRepresentative residue)) cone) =
    cartierResidueExponent ell (latticeResidueRepresentative residue)
      (basis.equivFun (coneDivisorCharacter fan regular b cone))
      (basis.equivFun (coneDivisorCharacter fan regular
        (toricResidueCoefficients fan b ell
          (basis.equivFun.symm (latticeResidueRepresentative residue))) cone)) := by
  simp only [normalizedToricResidueCharacter, cartierResidueExponent,
    map_sub, map_add, map_nsmul, LinearEquiv.apply_symm_apply, natCast_zsmul]

end ToricPower
