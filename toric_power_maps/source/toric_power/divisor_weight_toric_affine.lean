module

public import ToricPower.DivisorWeightRationalPushforward
public import ToricPower.DivisorWeightAffinePushforward
public import ToricPower.DivisorCoefficientTransport

/-!
# The residue decomposition on the actual toric affine charts

The coordinate-ring power maps are conjugate under the proved integral
lattice coordinate equivalence. Restriction of scalars therefore transports
the Laurent divisor decomposition to the actual toric chart rings. The
Cartier atlas comparison turns it into a decomposition of the genuine
restricted Cartier sheaves.

Development source: kernel checking of the exact current hash is required
before any theorem in this file is reported as verified.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric MonoidAlgebra

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} {κ : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [Fintype κ] {i : N →+ V}

/-- The actual toric power map acts by multiplication by the same integer on
integral character coordinates, including all complementary Laurent axes. -/
theorem affineToricRayChartRingEquiv_power (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (ell : ℕ) (cone : fan.cones)
    (a : affineCoordinateRing fan.lattice cone.val) :
    affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis
        (chartPowerRingHom fan cone ell a) =
      rayChartPowerEndomorphism ℂ
        (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis) ell
        (affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis a) := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simpa only [map_add, ha, hb]
  | single m z =>
      let e := affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis
      let E := dualSemigroupRayCoordinates fan.lattice (fan.isToricCone cone.property) basis
      have hp : chartPowerRingHom fan cone ell (single m z) =
          single (Multiplicative.ofAdd (ell • m.toAdd)) z := by
        rw [chartPowerRingHom_apply, mapDomain_single]
        rfl
      have he : e (single m z) = single (Multiplicative.ofAdd (E m.toAdd)) z :=
        affineToricRayChartRingEquiv_single fan.lattice (fan.isToricCone cone.property)
          basis m.toAdd z
      calc
        e (chartPowerRingHom fan cone ell (single m z)) =
            e (single (Multiplicative.ofAdd (ell • m.toAdd)) z) := congrArg e hp
        _ = single (Multiplicative.ofAdd (E (ell • m.toAdd))) z :=
          affineToricRayChartRingEquiv_single fan.lattice (fan.isToricCone cone.property)
            basis (ell • m.toAdd) z
        _ = single (Multiplicative.ofAdd (ell • E m.toAdd)) z :=
          congrArg (fun x => single (Multiplicative.ofAdd x) z) (map_nsmul E ell m.toAdd)
        _ = rayChartPowerEndomorphism ℂ
            (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis) ell
            (e (single m z)) := by
          rw [he, rayChartPowerEndomorphism, mapDomainRingHom_apply, mapDomain_single]
          rfl

/-- The two ways of changing scalar rings in the power square agree by the
actual equality of ring maps; the equivalence is the identity on sections. -/
def toricDivisorPowerRestrictScalarsIso (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ) (ell : ℕ)
    (cone : fan.cones) :
    (ModuleCat.restrictScalars (chartPowerRingHom fan cone ell).hom).obj
      (toricDivisorChartModule fan basis b cone) ≅
    (ModuleCat.restrictScalars
      (affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis).toRingHom).obj
      ((ModuleCat.restrictScalars (rayChartPowerEndomorphism ℂ
        (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis) ell)).obj
          (ModuleCat.of (RayChartRing ℂ (characterRayMatrix fan.lattice
            (fan.isToricCone cone.property) basis))
            (DivisorSectionModule ℂ (characterRayMatrix fan.lattice
              (fan.isToricCone cone.property) basis) (coneDivisorCoefficients fan b cone) 1))) := by
  let e := affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis
  let A := characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis
  let M := ModuleCat.of (RayChartRing ℂ A)
    (DivisorSectionModule ℂ A (coneDivisorCoefficients fan b cone) 1)
  have square : e.toRingHom.comp (chartPowerRingHom fan cone ell).hom =
      (rayChartPowerEndomorphism ℂ A ell).comp e.toRingHom := by
    apply RingHom.ext
    intro a
    exact affineToricRayChartRingEquiv_power fan basis ell cone a
  exact ((ModuleCat.restrictScalarsComp (chartPowerRingHom fan cone ell).hom
      e.toRingHom).app M).symm ≪≫
    (ModuleCat.restrictScalarsCongr square).app M ≪≫
    (ModuleCat.restrictScalarsComp e.toRingHom (rayChartPowerEndomorphism ℂ A ell)).app M


/-- Coordinate floor coefficients equal the coefficients of the global
floor divisor. The conversion on Laurent sections is literal identity. -/
def toricDivisorResidueCoefficientPiEquiv (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ) (ell : ℕ)
    (cone : fan.cones) :
    ((ModuleCat.restrictScalars
      (affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis).toRingHom).obj
      (ModuleCat.of (RayChartRing ℂ (characterRayMatrix fan.lattice
        (fan.isToricCone cone.property) basis))
        (∀ residue : LatticeResidues κ ell, DivisorSectionModule ℂ
          (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
          (powerCoefficient (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
            (coneDivisorCoefficients fan b cone) (ell : ℤ)
            (latticeResidueRepresentative residue)) 1))) ≃ₗ[
              affineCoordinateRing fan.lattice cone.val]
      (∀ residue : LatticeResidues κ ell, toricDivisorChartModule fan basis
        (toricResidueCoefficients fan b ell
          (basis.equivFun.symm (latticeResidueRepresentative residue))) cone) := by
  let A := characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis
  let e := affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis
  have hcoeff (residue : LatticeResidues κ ell) :
      powerCoefficient A (coneDivisorCoefficients fan b cone) (ell : ℤ)
        (latticeResidueRepresentative residue) =
      coneDivisorCoefficients fan (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue))) cone := by
    simpa only [LinearEquiv.apply_symm_apply] using
      (toricResidueCoefficients_chart fan basis b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue)) cone).symm
  let t := fun residue : LatticeResidues κ ell =>
    divisorCoefficientEqLinearEquiv ℂ A 1 _ _ (hcoeff residue)
  exact {
    toFun := fun x residue => t residue (x residue)
    invFun := fun x residue => (t residue).symm (x residue)
    left_inv := fun x => by funext residue; exact (t residue).symm_apply_apply _
    right_inv := fun x => by funext residue; exact (t residue).apply_symm_apply _
    map_add' := fun x y => by funext residue; exact (t residue).map_add _ _
    map_smul' := fun a x => by
      funext residue
      exact (t residue).map_smul (e a) (x residue) }


/-- Coefficient transport preserves every underlying Laurent section. -/
theorem toricDivisorResidueCoefficientPiEquiv_apply_val (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ) (ell : ℕ)
    (cone : fan.cones)
    (x : ∀ residue : LatticeResidues κ ell, DivisorSectionModule ℂ
      (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
      (powerCoefficient (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
        (coneDivisorCoefficients fan b cone) (ell : ℤ)
        (latticeResidueRepresentative residue)) 1)
    (residue : LatticeResidues κ ell) :
    (toricDivisorResidueCoefficientPiEquiv fan basis b ell cone x residue).val =
      (x residue).val := by
  apply divisorCoefficientEqLinearEquiv_apply_val
  simpa only [LinearEquiv.apply_symm_apply] using
    (toricResidueCoefficients_chart fan basis b ell
      (basis.equivFun.symm (latticeResidueRepresentative residue)) cone).symm

/-- The inverse coefficient transport has the same underlying sections.
The inverse law avoids unfolding the entire scalar-restriction equivalence. -/
theorem toricDivisorResidueCoefficientPiEquiv_inv_val (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ) (ell : ℕ)
    (cone : fan.cones)
    (x : ∀ residue : LatticeResidues κ ell, toricDivisorChartModule fan basis
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue))) cone)
    (residue : LatticeResidues κ ell) :
    ((toricDivisorResidueCoefficientPiEquiv fan basis b ell cone).symm x
      residue).val = (x residue).val := by
  apply divisorCoefficientEqLinearEquiv_symm_apply_val
  simpa only [LinearEquiv.apply_symm_apply] using
    (toricResidueCoefficients_chart fan basis b ell
      (basis.equivFun.symm (latticeResidueRepresentative residue)) cone).symm


/-- The full actual chart-module decomposition for every invariant divisor. -/
def toricDivisorPowerModuleIso (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) (cone : fan.cones) :
    (ModuleCat.restrictScalars (chartPowerRingHom fan cone ell).hom).obj
      (toricDivisorChartModule fan basis b cone) ≅
    ModuleCat.of (affineCoordinateRing fan.lattice cone.val)
      (∀ residue : LatticeResidues κ ell, toricDivisorChartModule fan basis
        (toricResidueCoefficients fan b ell
          (basis.equivFun.symm (latticeResidueRepresentative residue))) cone) :=
  toricDivisorPowerRestrictScalarsIso fan basis b ell cone ≪≫
    (ModuleCat.restrictScalars
      (affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis).toRingHom).mapIso
      (divisorPowerModuleIso ℂ
        (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
        (coneDivisorCoefficients fan b cone) ell hell) ≪≫
    (toricDivisorResidueCoefficientPiEquiv fan basis b ell cone).toModuleIso

/-- The chart power map is the spectrum of its literal coordinate-ring map. -/
theorem affinePowerMap_eq_chartPowerSpec (fan : Fan i) (ell : ℕ) (cone : fan.cones) :
    affinePowerMap fan ell cone = Spec.map (chartPowerRingHom fan cone ell) := by
  simp only [affinePowerMap, affineToricSchemeMap_def, chartPowerRingHom]

/-- On every cone, the actual Cartier-sheaf pushforward is the finite direct
sum of the actual restrictions of the global floor Cartier sheaves. -/
def toricAffineCartierPushforwardIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (Scheme.Modules.pushforward (affinePowerMap fan ell cone)).obj
      ((invariantCartierDivisor fan nonempty regular b).sheaf.restrict
        (fan.affineToricChartι cone)) ≅
    ⨁ (fun residue : LatticeResidues κ ell =>
      (toricResidueSheafFamily fan nonempty regular basis b ell residue).restrict
        (fan.affineToricChartι cone)) := by
  letI := toricSchemeIntegral fan nonempty
  let R := CommRingCat.of (affineCoordinateRing fan.lattice cone.val)
  let family : LatticeResidues κ ell → ModuleCat R := fun residue =>
    toricDivisorChartModule fan basis (toricResidueCoefficients fan b ell
      (basis.equivFun.symm (latticeResidueRepresentative residue))) cone
  letI : (tilde.functor R).PreservesZeroMorphisms := ⟨fun _ _ => tilde.map_zero⟩
  letI : (tilde.functor R).IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : PreservesBiproduct family (tilde.functor R) :=
    preservesBiproduct_of_preservesCoproduct _
  rw [affinePowerMap_eq_chartPowerSpec]
  exact (Scheme.Modules.pushforward (Spec.map (chartPowerRingHom fan cone ell))).mapIso
      (affineCartierDivisorModuleIso fan nonempty regular basis b cone).symm ≪≫
    affinePushforwardTildeIso (chartPowerRingHom fan cone ell)
      (toricDivisorChartModule fan basis b cone) ≪≫
    (tilde.functor R).mapIso (toricDivisorPowerModuleIso fan basis b ell hell cone) ≪≫
    (tilde.functor R).mapIso (moduleFiniteBiproductIsoPi family).symm ≪≫
    (tilde.functor R).mapBiproduct family ≪≫
    biproduct.mapIso (fun residue => affineCartierDivisorModuleIso fan nonempty regular basis
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue))) cone)

end ToricPower
