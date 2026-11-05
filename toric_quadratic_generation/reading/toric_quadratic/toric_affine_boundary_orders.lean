module

public import PaperVerification.ToricCoordinateOrders
public import PaperVerification.ToricFunctionFieldBridge
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

@[expose] public section

/-!
# From an actual affine boundary prime to scheme order

The stalk equivalence below is composed from the actual affine stalk
localization and the actual open-immersion stalk map. Its compatibility
with the coordinate-ring embedding in the generic stalk is proved.
Principal prime uniformizers therefore compute the scheme's ordinary
order function at the corresponding actual point.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical nonZeroDivisors

variable (R : CommRingCat.{u}) [IsDomain R] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec R ⟶ X) [IsOpenImmersion j]

local instance affineOpenStalkMap_isIso (p : PrimeSpectrum R) : IsIso (j.stalkMap p) :=
  (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion j)).2
    (show Spec R from p)

/-- The genuine affine localization isomorphism followed by the inverse
of the genuine open-immersion map on local rings. -/
def affineOpenStalkEquiv (p : PrimeSpectrum R) :
    Localization.AtPrime p.asIdeal ≃+* X.presheaf.stalk (j p) :=
  ((Spec.stalkIso R p).symm ≪≫ (asIso (j.stalkMap p)).symm).commRingCatIsoToRingEquiv

@[simp] theorem affineOpenStalkEquiv_stalkMap (p : PrimeSpectrum R)
    (r : Localization.AtPrime p.asIdeal) :
    j.stalkMap p (affineOpenStalkEquiv R j p r) = (Spec.stalkIso R p).inv r := by
  change (asIso (j.stalkMap p)).hom
    ((asIso (j.stalkMap p)).inv ((Spec.stalkIso R p).inv r)) =
      (Spec.stalkIso R p).inv r
  exact Iso.inv_hom_id_apply (asIso (j.stalkMap p)) _

theorem affineOpenStalkEquiv_algebraMap (p : PrimeSpectrum R) (r : R) :
    affineOpenStalkEquiv R j p (algebraMap R (Localization.AtPrime p.asIdeal) r) =
      X.presheaf.germ (j ''ᵁ (⊤ : (Spec R).Opens)) (j p) ⟨p, trivial, rfl⟩
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)) := by
  apply (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv.injective
  change j.stalkMap p
      (affineOpenStalkEquiv R j p (algebraMap R (Localization.AtPrime p.asIdeal) r)) =
    j.stalkMap p (X.presheaf.germ (j ''ᵁ (⊤ : (Spec R).Opens)) (j p) ⟨p,trivial,rfl⟩
      ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)))
  erw [affineOpenStalkEquiv_stalkMap, j.germ_stalkMap_apply]
  have hsec := congrArg (fun f => f ((Scheme.ΓSpecIso R).inv r)) (j.appIso_inv_app ⊤)
  erw [hsec]
  erw [(Spec R).presheaf.germ_res_apply
    (eqToHom (Scheme.Hom.preimage_image_eq j ⊤))]
  exact congrArg (fun f => f r) (Spec.algebraMap_stalkIso_inv (R := R) (x := p))

/-- The two routes to the actual generic stalk agree exactly. -/
theorem affineOpenStalkEquiv_functionField (p : PrimeSpectrum R) (r : R) :
    algebraMap (X.presheaf.stalk (j p)) X.functionField
        (affineOpenStalkEquiv R j p (algebraMap R (Localization.AtPrime p.asIdeal) r)) =
      affineOpenCoordinateMap R j r := by
  letI : Nonempty (j ''ᵁ (⊤ : (Spec R).Opens)) := openImmersion_image_nonempty j ⊤
  rw [affineOpenStalkEquiv_algebraMap]
  exact (X.algebraMap_germ_eq_germToFunctionField
    (U := j ''ᵁ (⊤ : (Spec R).Opens)) (x := j p) ⟨p,trivial,rfl⟩
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))).trans
    (openImmersionRegularToFunctionField_eq_germ_image j ⊤
      ((Scheme.ΓSpecIso R).inv r)).symm

theorem affineOpenCoordinateMap_injective : Function.Injective (affineOpenCoordinateMap R j) :=
  (openImmersionGlobalToFunctionField_injective j).comp
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective

/-- A DVR on the literal affine localization transports to the actual
scheme stalk; no regularity axiom is added to that stalk. -/
theorem affineOpen_stalk_isDiscreteValuationRing (p : PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] :
    IsDiscreteValuationRing (X.presheaf.stalk (j p)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (affineOpenStalkEquiv R j p)

theorem affineOpen_coheight_eq_one (p : PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] :
    Order.coheight (j p) = 1 := by
  letI := affineOpen_stalk_isDiscreteValuationRing R j p
  have h := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk (j p))
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_eq_coe.mp h

variable [IsNoetherianRing R] [IsLocallyNoetherian X]

/-- Exact scheme order of a nonzero principal prime generator on an
actual affine open chart. -/
theorem affineOpen_order_principalPrime (p : PrimeSpectrum R)
    (r : R) (hr : r ≠ 0) (hp : p.asIdeal = Ideal.span {r}) :
    X.ord (affineOpenCoordinateMap R j r) (j p) = 1 := by
  letI : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
    principalPrimeLocalization_isDiscreteValuationRing R
      (Localization.AtPrime p.asIdeal) p.asIdeal r hr hp
  letI := affineOpen_stalk_isDiscreteValuationRing R j p
  have hcodim := affineOpen_coheight_eq_one R j p
  have hr' : affineOpenCoordinateMap R j r ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr
  rw [X.ord_eq_iff hcodim hr']
  change Ring.ordFrac (X.presheaf.stalk (j p)) (affineOpenCoordinateMap R j r) =
    WithZero.exp (1 : ℤ)
  rw [← affineOpenStalkEquiv_functionField R j p r]
  apply Ring.ordFrac_irreducible
  exact (principalPrimeLocalization_generator_irreducible R
    (Localization.AtPrime p.asIdeal) p.asIdeal r hr hp).map
      (affineOpenStalkEquiv R j p).toMulEquiv

/-- An element outside the actual affine prime is a local unit, so its
scheme order is zero at the corresponding point. -/
theorem affineOpen_order_of_not_mem (p : PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] (r : R) (hr : r ∉ p.asIdeal) :
    X.ord (affineOpenCoordinateMap R j r) (j p) = 0 := by
  letI := affineOpen_stalk_isDiscreteValuationRing R j p
  have hu : IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) r) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff
      (S := Localization.AtPrime p.asIdeal) (I := p.asIdeal) r).mpr hr
  have hcodim := affineOpen_coheight_eq_one R j p
  have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hr' : affineOpenCoordinateMap R j r ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr0
  rw [X.ord_eq_iff hcodim hr']
  change Ring.ordFrac (X.presheaf.stalk (j p)) (affineOpenCoordinateMap R j r) =
    WithZero.exp (0 : ℤ)
  rw [← affineOpenStalkEquiv_functionField R j p r]
  have hu' : IsUnit ((affineOpenStalkEquiv R j p)
      (algebraMap R (Localization.AtPrime p.asIdeal) r)) :=
    hu.map (affineOpenStalkEquiv R j p).toRingHom
  simpa only [WithZero.exp_zero] using Ring.ordFrac_of_isUnit hu'

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineOpen_order_principalPrime

