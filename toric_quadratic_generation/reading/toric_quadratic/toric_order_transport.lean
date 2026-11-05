module

public import PaperVerification.ToricDominantFunctionField
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

/-!
# Transport of actual orders through isomorphisms

Ring order is transported using the order isomorphism of the actual ideal
lattices and the quotient-length formula. Its fraction-field extension is
then transported by writing an arbitrary fraction as a quotient. The
scheme statement uses the genuine maps on local and generic stalks.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

section Rings

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The module length defining order is preserved by the actual ring
isomorphism, including the infinite-length case. -/
theorem ord_ringEquiv (e : R ≃+* S) (r : R) :
    Ring.ord S (e r) = Ring.ord R r := by
  rw [Ring.ord,Ring.ord,Module.length_quotient,Module.length_quotient]
  simpa only [RingEquiv.idealComapOrderIso_symm_apply,
    Ideal.map_span,Set.image_singleton] using
    Order.coheight_orderIso e.idealComapOrderIso.symm (Ideal.span {r})

variable [IsDomain R] [IsDomain S]

theorem ordMonoidWithZeroHom_ringEquiv (e : R ≃+* S) (r : R) :
    Ring.ordMonoidWithZeroHom S (e r) = Ring.ordMonoidWithZeroHom R r := by
  by_cases hr : r=0
  · simp [hr]
  have her : e r≠0 := (map_ne_zero_iff e e.injective).mpr hr
  rw [Ring.ordMonoidWithZeroHom_eq_ord
      (mem_nonZeroDivisors_iff_ne_zero.mpr her),
    Ring.ordMonoidWithZeroHom_eq_ord
      (mem_nonZeroDivisors_iff_ne_zero.mpr hr),ord_ringEquiv]

variable [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    {K L : Type*} [Field K] [Field L]
    [Algebra R K] [Algebra S L] [IsFractionRing R K] [IsFractionRing S L]

/-- Functoriality of the existing fraction-field order under compatible
isomorphisms of the local ring and its fraction field. -/
theorem ordFrac_ringEquiv (e : R ≃+* S) (E : K ≃+* L)
    (hE : ∀ r : R,E (algebraMap R K r)=algebraMap S L (e r)) (z : K) :
    Ring.ordFrac S (E z) = Ring.ordFrac R z := by
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective R z
  by_cases ha : a=0
  · simp [ha]
  have hb' : b≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hea : e a≠0 := (map_ne_zero_iff e e.injective).mpr ha
  have heb : e b≠0 := (map_ne_zero_iff e e.injective).mpr hb'
  rw [map_div₀,hE,hE,map_div₀,map_div₀,
    Ring.ordFrac_eq_ord S hea,Ring.ordFrac_eq_ord S heb,
    Ring.ordFrac_eq_ord R ha,Ring.ordFrac_eq_ord R hb',
    ordMonoidWithZeroHom_ringEquiv,ordMonoidWithZeroHom_ringEquiv]

end Rings

section Schemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Restriction to an actual open subscheme preserves all local orders.
The equality includes the zero rational function and all codimensions. -/
theorem schemeOrder_openImmersion (j : Y ⟶ X) [IsOpenImmersion j]
    [IsDominant j] (y : Y) (z : X.functionField) :
    Y.ord (dominantFunctionFieldMap j z) y = X.ord z (j y) := by
  have hh : Order.coheight (j y)=Order.coheight y :=
    coheight_eq_of_isOpenImmersion j
  by_cases hy : Order.coheight y=1
  · have hx : Order.coheight (j y)=1 := hh.trans hy
    letI : Ring.KrullDimLE 1 (Y.presheaf.stalk y) :=
      krullDimLE_of_coheight_le hy.le
    letI : Ring.KrullDimLE 1 (X.presheaf.stalk (j y)) :=
      krullDimLE_of_coheight_le hx.le
    let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
    let E := openImmersionFunctionFieldEquiv j
    have hE (a : X.presheaf.stalk (j y)) :
        E (algebraMap (X.presheaf.stalk (j y)) X.functionField a) =
          algebraMap (Y.presheaf.stalk y) Y.functionField (e a) := by
      change dominantFunctionFieldMap j
          (algebraMap (X.presheaf.stalk (j y)) X.functionField a) = _
      exact dominantFunctionFieldMap_stalk j y a
    have ho : Y.ordHom y hy (dominantFunctionFieldMap j z) =
        X.ordHom (j y) hx z :=
      ordFrac_ringEquiv e E hE z
    rw [Y.ord_eq_ordHom_of_coheight_eq_one hy,
      X.ord_eq_ordHom_of_coheight_eq_one hx,ho]
  · have hx : Order.coheight (j y)≠1 := fun h=>hy (hh.symm.trans h)
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hy,
      Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- In particular, a scheme isomorphism preserves actual orders of
vanishing under its genuine pullback on rational functions. -/
theorem schemeOrder_iso (e : Y ≅ X) (y : Y) (z : X.functionField) :
    Y.ord (dominantFunctionFieldMap e.hom z) y = X.ord z (e.hom y) :=
  schemeOrder_openImmersion e.hom y z

end Schemes

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.ordFrac_ringEquiv
#print axioms PaperVerification.ToricSchemes.schemeOrder_iso
