module

public import ToricPower.DivisorWeightGlobalSections
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Local comparison of the canonical global residue sum

The canonical global rational-monomial sum is compared on each actual
Cartier generator with the proved full affine residue decomposition. The
local comparisons imply that this single global morphism is an
isomorphism. The cover consists of all cones, with no completeness or
full-dimensionality assumption.

The elementary restriction-equivalence and finite-biproduct helpers are
adapted from BondalThomsen/Toric/Frobenius/MultiplicationGlobalResidueIso
at commit 9a2bdcdcf6b25710459f7f476c9c62de3039b7bb.

Development source: the exact current source must pass the pinned checker
before any declaration is reported as verified.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti.Toric
open scoped Classical

namespace ToricPower


universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

variable {κ : Type u} [Fintype κ]

set_option maxRecDepth 4096 in
/-- The actual chart comparison of each canonical global residue summand
with the proved affine residue basis. -/
theorem toricResidueSheafMap_chart_component (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) (cone : fan.cones) (residue : LatticeResidues κ ell) :
    letI := toricSchemeIntegral fan nonempty
    (toricCartierAffineFrame fan nonempty regular
        (toricResidueCoefficients fan b ell
          (basis.equivFun.symm (latticeResidueRepresentative residue))) cone).hom ≫
      (Scheme.Modules.restrictFunctor (fan.affineToricChartι cone)).map
        (toricResidueSheafMap fan nonempty regular b ell hell
          (basis.equivFun.symm (latticeResidueRepresentative residue))) ≫
      (toricCartierPushforwardChartIso fan nonempty regular b ell hell cone).hom =
    affineLinearSheafMap (chartPowerRingHom fan cone ell)
      (ModuleCat.ofHom (LinearMap.single (affineCoordinateRing fan.lattice cone.val)
        (fun _ : LatticeResidues κ ell => affineCoordinateRing fan.lattice cone.val) residue) ≫
          (toricFramedResidueModuleIso fan regular basis b ell hell cone).hom) := by
  letI := toricSchemeIntegral fan nonempty
  apply unitSheafHom_ext_top
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (affineCoordinateRing fan.lattice cone.val))).hom).injective
  have global := toricResidueSheafMap_chart_coordinate fan nonempty regular b ell hell
    (basis.equivFun.symm (latticeResidueRepresentative residue)) cone 1
  have affine := affineLinearSheafMap_top_coordinate (chartPowerRingHom fan cone ell)
    (ModuleCat.ofHom (LinearMap.single (affineCoordinateRing fan.lattice cone.val)
      (fun _ : LatticeResidues κ ell => affineCoordinateRing fan.lattice cone.val) residue) ≫
        (toricFramedResidueModuleIso fan regular basis b ell hell cone).hom) 1
  simp only [map_one, one_mul] at global
  rw [tildeUnit_toOpen_one] at affine
  simp only [ModuleCat.comp_apply, ModuleCat.ofHom_apply, LinearMap.single_apply] at affine
  exact global.trans ((toricFramedResidueModuleIso_single fan regular basis b ell hell cone residue).symm.trans
    affine.symm)

/-- All chosen source frames, assembled through the actual finite
biproduct restriction isomorphism. -/
abbrev toricResidueChartFrameIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (ell : ℕ) (cone : fan.cones) :
    (⨁ fun _ : LatticeResidues κ ell =>
      (SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf :
        (fan.affineToricChart cone).Modules)) ≅
      (⨁ toricResidueSheafFamily fan nonempty regular basis b ell).restrict
        (fan.affineToricChartι cone) :=
  finiteBiproductFrameRestrictionIso (fan.affineToricChartι cone)
    (toricResidueSheafFamily fan nonempty regular basis b ell)
    (fun residue => toricCartierAffineFrame fan nonempty regular
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue))) cone)


end ToricPower
