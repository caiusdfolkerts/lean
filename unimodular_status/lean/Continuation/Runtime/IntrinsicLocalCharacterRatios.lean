module

public import Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.HasLimits

public import Continuation.Runtime.IntrinsicReconstruction
import all Continuation.Runtime.IntrinsicReconstruction
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Character components of a local torus equation

Let `U` be an affine open in a smooth variety with a dense equivariant open
split torus. If a Laurent polynomial is a unit on `U` intersected with that
torus, every character component divided by the polynomial is regular on
`U`. At every point of `U`, at least one such ratio is a local unit.

The proof uses the actual action on the scheme product. On the product's
boundary, the action graph fixes every codimension-one point, and therefore
preserves its order. Away from the boundary the denominator is a unit.
Normality makes the action ratio regular, and coefficient extraction in the
actual affine product ring gives the assertion. The argument works over
arbitrary fields, without a density assumption on rational torus points.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricCharacters
open scoped TensorProduct PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

local instance localCharacterLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- A Laurent polynomial is regular at every point of the original open
torus, as an element of the original variety's function field. -/
theorem laurentValue_mem_regularAt_torus
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (x : X.left) (hx : x ∈ T.torusOpen) :
    openTorusRationalAlgHom k n X.left T.torus.left f ∈
      regularAtSubring X.left x := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  let j : Spec R ⟶ X.left := T.torus.left
  letI : IsDomain R := torusCoordinateRing_isDomain k n
  letI : Nonempty (j ''ᵁ (⊤ : (Spec R).Opens)) :=
    openImmersion_image_nonempty j ⊤
  have hx' : x ∈ j ''ᵁ (⊤ : (Spec R).Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hx
  change affineOpenCoordinateMap R j f ∈ regularAtSubring X.left x
  rw [← affineChartSection_germ R j f]
  exact regular_germ_mem_regularAt X.left _ _ x hx'

/-- A unit of the Laurent coordinate ring is a unit in every original
local ring on the specified open torus. -/
theorem laurentUnit_isRegularUnitAt_torus
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : IsUnit f)
    (x : X.left) (hx : x ∈ T.torusOpen) :
    IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f) := by
  obtain ⟨unit, rfl⟩ := hf
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  have hv : value (unit : AddMonoidAlgebra k (Fin n → ℤ)) ≠ 0 :=
    (unit.isUnit.map value).ne_zero
  have hinv : value ((unit⁻¹ : (AddMonoidAlgebra k (Fin n → ℤ))ˣ) :
      AddMonoidAlgebra k (Fin n → ℤ)) = (value unit)⁻¹ := by
    apply mul_left_cancel₀ hv
    rw [← map_mul, Units.mul_inv, map_one, mul_inv_cancel₀ hv]
  refine ⟨T.laurentValue_mem_regularAt_torus _ x hx, ?_⟩
  rw [← hinv]
  exact T.laurentValue_mem_regularAt_torus _ x hx

/-- A rational function regular on the torus and a unit on its intersection
with `U` has a regular action/projection ratio over the entire product `T×U`.
No invariant affine neighbourhood or Cartier divisor is an input. -/
theorem local_action_ratio_regular
    (U : X.left.Opens) [Nonempty U] (r : X.left.functionField) (hr : r ≠ 0)
    (hregular : ∀ x ∈ T.torusOpen, r ∈ regularAtSubring X.left x)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x r) :
    let G := splitTorusOver k (Fin n → ℤ)
    letI : Nonempty ((snd G X).left ⁻¹ᵁ U) :=
      dominant_preimage_nonempty (snd G X).left U
    dominantFunctionFieldMap (γ[G,X]).left r /
      dominantFunctionFieldMap (snd G X).left r ∈
        ((G ⊗ X).left.germToFunctionField ((snd G X).left ⁻¹ᵁ U)).hom.range := by
  let G := splitTorusOver k (Fin n → ℤ)
  let Y := G ⊗ X
  let p := (snd G X).left
  let a := (γ[G,X]).left
  letI : IsLocallyNoetherian Y.left := T.product_locallyNoetherian
  letI : Smooth Y.hom := T.product_smooth
  letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
  have hpr : dominantFunctionFieldMap p r ≠ 0 :=
    (map_ne_zero_iff _ (dominantFunctionFieldMap_injective p)).mpr hr
  have har : dominantFunctionFieldMap a r ≠ 0 :=
    (map_ne_zero_iff _ (dominantFunctionFieldMap_injective a)).mpr hr
  apply (smooth_regular_range_iff_orders Y.hom (p ⁻¹ᵁ U) _
    (div_ne_zero har hpr)).mpr
  intro y hy
  by_cases hcodim : Order.coheight y = 1
  · by_cases hb : y ∈ T.productBoundary
    · have haction : dominantFunctionFieldMap a r =
          dominantFunctionFieldMap T.graphIso.hom (dominantFunctionFieldMap p r) := by
        have h := congrArg (fun φ => φ r)
          (dominantFunctionFieldMap_comp T.graphIso.hom p)
        change dominantFunctionFieldMap (T.graphIso.hom ≫ p) r = _ at h
        have he : T.graphIso.hom ≫ p = a := T.graph_hom_snd
        simp only [he, RingHom.comp_apply] at h
        exact h
      rw [rationalOrder_div har hpr, haction]
      erw [schemeOrder_iso]
      erw [T.graph_fixes_codimensionOne_boundary y hb hcodim, sub_self]
    · have hpT : p y ∈ T.torusOpen := Classical.not_not.mp hb
      have haT : a y ∈ T.torusOpen := by
        change y ∈ (γ[G,X]).left ⁻¹ᵁ T.torusOpen
        rw [T.action_preimage_torusOpen]
        exact hpT
      have hnum : dominantFunctionFieldMap a r ∈ regularAtSubring Y.left y :=
        dominantFunctionFieldMap_mem_regularAt a y r (hregular (a y) haT)
      have hden : IsRegularUnitAt Y.left y (dominantFunctionFieldMap p r) :=
        isRegularUnitAt_pullback p y r (hunit (p y) hy hpT)
      have hratio : dominantFunctionFieldMap a r / dominantFunctionFieldMap p r ∈
          regularAtSubring Y.left y := by
        simpa only [div_eq_mul_inv] using (regularAtSubring Y.left y).mul_mem hnum hden.2
      letI : IsIntegrallyClosed (Y.left.presheaf.stalk y) :=
        smooth_stalk_isIntegrallyClosed Y.hom y
      exact (rationalOrder_nonnegative_iff_regularAt y hcodim _
        (div_ne_zero har hpr)).mpr hratio
  · simp only [Scheme.ord_eq_zero_of_coheight_neq_one hcodim, le_refl]

/-- Every character term divided by the original Laurent equation is an
actual regular section on the given affine open. -/
theorem local_character_ratio_regular
    (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : f ≠ 0)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f))
    (m : Fin n → ℤ) :
    openTorusRationalAlgHom k n X.left T.torus.left
        (AddMonoidAlgebra.single m (f.coeff m)) /
      openTorusRationalAlgHom k n X.left T.torus.left f ∈
        (X.left.germToFunctionField U).hom.range := by
  let G := splitTorusOver k (Fin n → ℤ)
  let A := AddMonoidAlgebra k (Fin n → ℤ)
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  let p := (snd G X).left
  let q := value f
  have hq : q ≠ 0 :=
    (map_ne_zero_iff value (openTorusRationalAlgHom_injective k n X.left T.torus.left)).mpr hf
  let δf := Algebra.TensorProduct.map (AlgHom.id k A) value (Coalgebra.comul (R := k) f)
  let w : A ⊗[k] X.left.functionField := δf * (1 ⊗ₜ[k] q⁻¹)
  letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
  have hwvalue : torusProductRationalMap k n X w =
      dominantFunctionFieldMap (γ[G,X]).left q / dominantFunctionFieldMap p q := by
    have hden : torusProductRationalMap k n X (1 ⊗ₜ[k] q⁻¹) =
        (dominantFunctionFieldMap p q)⁻¹ := by
      simp only [torusProductRationalMap_tmul, map_one, _root_.one_mul, map_inv₀]
      rfl
    calc
      _ = torusProductRationalMap k n X δf *
          torusProductRationalMap k n X (1 ⊗ₜ[k] q⁻¹) := map_mul _ _ _
      _ = dominantFunctionFieldMap (γ[G,X]).left q *
          (dominantFunctionFieldMap p q)⁻¹ :=
        congrArg₂ (· * ·) (T.action_pullback_laurent f).symm hden
      _ = _ := (div_eq_mul_inv _ _).symm
  have hwregular : torusProductRationalMap k n X w ∈
      Set.range ((G ⊗ X).left.germToFunctionField (p ⁻¹ᵁ U)) := by
    rw [hwvalue]
    exact T.local_action_ratio_regular U q hq
      (T.laurentValue_mem_regularAt_torus f) hunit
  have hw := (torusProductRationalMap_mem_regularAffine_iff k n X U hU w).mp hwregular
  have hcoeff := characterCoefficient_mem_range k
    (BaseSections.regularValueAlgHom k U).toLinearMap m w hw
  rw [show characterCoefficient k m w =
      value (AddMonoidAlgebra.single m (f.coeff m)) * q⁻¹ from
    characterCoefficient_coaction_ratio k value f q⁻¹ m] at hcoeff
  obtain ⟨s, hs⟩ := hcoeff
  refine ⟨s, ?_⟩
  change X.left.germToFunctionField U s = _
  change X.left.germToFunctionField U s = value (AddMonoidAlgebra.single m (f.coeff m)) * q⁻¹ at hs
  simpa only [value, q, div_eq_mul_inv] using hs

/-- At each original point one character ratio is a unit in the actual
local ring. This follows from the exact sum of all the regular ratios being
one, not from an assumption about a monomial chart. -/
theorem exists_local_unit_character_ratio
    (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : f ≠ 0)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f))
    (x : X.left) (hx : x ∈ U) :
    ∃ m ∈ f.coeff.support, ∃ s : Γ(X.left,U),
      X.left.germToFunctionField U s =
        openTorusRationalAlgHom k n X.left T.torus.left
            (AddMonoidAlgebra.single m (f.coeff m)) /
          openTorusRationalAlgHom k n X.left T.torus.left f ∧
      IsUnit (X.left.presheaf.germ U x hx s) := by
  classical
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  have hv : value f ≠ 0 :=
    (map_ne_zero_iff value (openTorusRationalAlgHom_injective k n X.left T.torus.left)).mpr hf
  choose s hs using T.local_character_ratio_regular U hU f hf hunit
  have hsum : ∑ m ∈ f.coeff.support, s m = 1 := by
    apply X.left.germToFunctionField_injective U
    rw [map_sum, map_one]
    simp_rw [hs]
    rw [← Finset.sum_div, ← map_sum]
    change value (f.coeff.sum (fun m c => AddMonoidAlgebra.single m c)) / value f = 1
    rw [AddMonoidAlgebra.sum_coeff_single, div_self hv]
  have hunitSum : IsUnit (∑ m ∈ f.coeff.support, X.left.presheaf.germ U x hx (s m)) := by
    rw [← map_sum, hsum, map_one]
    exact isUnit_one
  obtain ⟨m, hm, hms⟩ := IsLocalRing.exists_of_isUnit_sum hunitSum
  exact ⟨m, hm, s m, hs m, hms⟩

end PaperVerification.ToricSchemes.SplitToricEmbedding
