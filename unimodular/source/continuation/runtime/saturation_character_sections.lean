module

public import Continuation.Runtime.SaturationCharacterCocycle
public import Continuation.Runtime.RationalOpenRestriction

/-!
# Global sections on an affine-open saturation

The original Laurent equation and every one of its character terms extend
as sections of the actual Cartier sheaf constructed on the saturation.
The key point is that saturation adds no boundary generic point to the
original open. The local character-ratio calculation therefore supplies
all the required codimension-one inequalities.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open PaperVerification.ToricCharacters

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [NoetherianSpace X.left]
    (T : SplitToricEmbedding k n X)

local instance saturationSectionsLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

variable (Y : X.left.Opens) [Nonempty Y]

local instance saturationSectionsIntegral : IsIntegral Y.toScheme :=
  isIntegral_of_isOpenImmersion Y.ι

local instance saturationSectionsSmooth : Smooth (Y.ι ≫ X.hom) := by infer_instance

local instance saturationSectionsOpenNoetherian : IsLocallyNoetherian Y.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian (Y.ι ≫ X.hom)

variable (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hY : (Y : Set X.left) =
      GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left))
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : f ≠ 0)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f))

/-- A Laurent function whose ratio to the original equation is regular on
the original affine open extends as an actual section on its saturation. -/
theorem laurent_mem_saturation_sectionValues
    (g : AddMonoidAlgebra k (Fin n → ℤ)) (hg : g ≠ 0)
    (hratio :
      openTorusRationalAlgHom k n X.left T.torus.left g /
        openTorusRationalAlgHom k n X.left T.torus.left f ∈
          (X.left.germToFunctionField U).hom.range) :
    dominantFunctionFieldMap Y.ι
        (openTorusRationalAlgHom k n X.left T.torus.left g) ∈
      (T.saturationCharacterCocycle Y U hU hY f hf hunit).toCartierData.sectionValueRange ⊤ := by
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  have hvalue : Function.Injective value :=
    openTorusRationalAlgHom_injective k n X.left T.torus.left
  have hvf : value f ≠ 0 := (map_ne_zero_iff value hvalue).mpr hf
  have hvg : value g ≠ 0 := (map_ne_zero_iff value hvalue).mpr hg
  have hpull : dominantFunctionFieldMap Y.ι (value g) ≠ 0 :=
    (map_ne_zero_iff _ (dominantFunctionFieldMap_injective Y.ι)).mpr hvg
  apply (RationalCartierCocycle.mem_sectionValueRange_iff_orders
    (Y.ι ≫ X.hom) _ ⊤ _ hpull).mpr
  intro y _
  rw [show (T.saturationCharacterCocycle Y U hU hY f hf hunit).toCartierData.weilCoefficient =
      T.cancelledBoundaryCoefficient Y (value f) from
    cartierCocycleOfOrderAtlas_weilCoefficient (Y.ι ≫ X.hom) _ _ _ _ _,
    schemeOrder_openImmersion]
  by_cases hb : Y.ι y ∈ T.boundary
  · rw [cancelledBoundaryCoefficient, if_pos hb]
    by_cases hcodim : Order.coheight (Y.ι y) = 1
    · have hySat : Y.ι y ∈ GroupAction.saturation
          (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left) := by
        rw [← hY]
        exact y.property
      have hyU : Y.ι y ∈ U :=
        (T.boundaryPrime_mem_saturation_iff U ⟨Y.ι y, hcodim, hb⟩).mp hySat
      obtain ⟨a, ha⟩ := hratio
      have hregular : value g / value f ∈ regularAtSubring X.left (Y.ι y) := by
        rw [← ha]
        exact regular_germ_mem_regularAt X.left U a (Y.ι y) hyU
      letI : IsIntegrallyClosed (X.left.presheaf.stalk (Y.ι y)) :=
        smooth_stalk_isIntegrallyClosed X.hom (Y.ι y)
      have hord := (rationalOrder_nonnegative_iff_regularAt (Y.ι y) hcodim
        (value g / value f) (div_ne_zero hvg hvf)).mpr hregular
      simpa only [rationalOrder_div hvg hvf, sub_eq_add_neg] using hord
    · simp only [Scheme.ord_eq_zero_of_coheight_neq_one hcodim,
        neg_zero, add_zero, le_refl]
  · rw [cancelledBoundaryCoefficient, if_neg hb, add_zero]
    by_cases hcodim : Order.coheight (Y.ι y) = 1
    · letI : IsIntegrallyClosed (X.left.presheaf.stalk (Y.ι y)) :=
        smooth_stalk_isIntegrallyClosed X.hom (Y.ι y)
      exact (rationalOrder_nonnegative_iff_regularAt (Y.ι y) hcodim (value g) hvg).mpr
        (T.laurentValue_mem_regularAt_torus g (Y.ι y) (Classical.not_not.mp hb))
    · simp only [Scheme.ord_eq_zero_of_coheight_neq_one hcodim, le_refl]

/-- The original equation itself is a genuine global section of the
constructed Cartier sheaf. -/
theorem equation_mem_saturation_sectionValues :
    dominantFunctionFieldMap Y.ι
        (openTorusRationalAlgHom k n X.left T.torus.left f) ∈
      (T.saturationCharacterCocycle Y U hU hY f hf hunit).toCartierData.sectionValueRange ⊤ := by
  apply T.laurent_mem_saturation_sectionValues Y U hU hY f hf hunit f hf
  have hvf : openTorusRationalAlgHom k n X.left T.torus.left f ≠ 0 :=
    (map_ne_zero_iff _ (openTorusRationalAlgHom_injective k n X.left T.torus.left)).mpr hf
  rw [div_self hvf]
  exact (X.left.germToFunctionField U).hom.range.one_mem

/-- Every nonzero character term is a genuine global section, with its
original coefficient and exponent. -/
theorem character_mem_saturation_sectionValues (m : CharacterTermIndex f) :
    (T.localCharacterFrame Y f m : Y.toScheme.functionField) ∈
      (T.saturationCharacterCocycle Y U hU hY f hf hunit).toCartierData.sectionValueRange ⊤ := by
  apply T.laurent_mem_saturation_sectionValues Y U hU hY f hf hunit
    (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val))
    (AddMonoidAlgebra.single_ne_zero.mpr (Finsupp.mem_support_iff.mp m.down.property))
  exact T.local_character_ratio_regular U hU f hf hunit m.down.val

/-- The global section whose value is the original Laurent equation. -/
def saturationEquationSection :
    Γ((T.saturationCharacterCocycle Y U hU hY f hf hunit).sheaf, ⊤) :=
  Classical.choose (T.equation_mem_saturation_sectionValues Y U hU hY f hf hunit)

theorem saturationEquationSection_value :
    (T.saturationCharacterCocycle Y U hU hY f hf hunit).toCartierData.sectionValue ⊤
      (T.saturationEquationSection Y U hU hY f hf hunit) =
      dominantFunctionFieldMap Y.ι
        (openTorusRationalAlgHom k n X.left T.torus.left f) :=
  Classical.choose_spec (T.equation_mem_saturation_sectionValues Y U hU hY f hf hunit)

/-- The global section retaining the exact original coefficient of a
character term. -/
def saturationCharacterSection (m : CharacterTermIndex f) :
    Γ((T.saturationCharacterCocycle Y U hU hY f hf hunit).sheaf, ⊤) :=
  Classical.choose (T.character_mem_saturation_sectionValues Y U hU hY f hf hunit m)

theorem saturationCharacterSection_value (m : CharacterTermIndex f) :
    (T.saturationCharacterCocycle Y U hU hY f hf hunit).toCartierData.sectionValue ⊤
      (T.saturationCharacterSection Y U hU hY f hf hunit m) =
      (T.localCharacterFrame Y f m : Y.toScheme.functionField) :=
  Classical.choose_spec (T.character_mem_saturation_sectionValues Y U hU hY f hf hunit m)

/-- Every point of the original affine open is a nonvanishing point of
the original equation as a section of the constructed Cartier sheaf. -/
theorem originalOpen_le_equationNonvanishing :
    Y.ι ⁻¹ᵁ U ≤ (T.saturationCharacterCocycle Y U hU hY f hf hunit).nonvanishingOpen
      (T.saturationEquationSection Y U hU hY f hf hunit) := by
  let C := T.saturationCharacterCocycle Y U hU hY f hf hunit
  let s := T.saturationEquationSection Y U hU hY f hf hunit
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  have hvf : value f ≠ 0 :=
    (map_ne_zero_iff value (openTorusRationalAlgHom_injective k n X.left T.torus.left)).mpr hf
  intro y hy
  obtain ⟨m, hm⟩ := C.covers y
  rw [C.nonvanishing_iff_value m s y hm,
    T.saturationEquationSection_value Y U hU hY f hf hunit]
  refine ⟨(map_ne_zero_iff _ (dominantFunctionFieldMap_injective Y.ι)).mpr hvf, ?_⟩
  obtain ⟨a, ha⟩ := T.local_character_ratio_regular U hU f hf hunit m.down.val
  have hreg : value (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val)) /
      value f ∈ regularAtSubring X.left (Y.ι y) := by
    rw [← ha]
    exact regular_germ_mem_regularAt X.left U a (Y.ι y) hy
  change dominantFunctionFieldMap Y.ι
      (value (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val))) /
      dominantFunctionFieldMap Y.ι (value f) ∈ regularAtSubring Y.toScheme y
  rw [← map_div₀]
  exact dominantFunctionFieldMap_mem_regularAt Y.ι y _ hreg

/-- The character sections cover the entire saturation: on each selected
frame open the corresponding section is exactly that frame. -/
theorem saturationCharacterSections_cover (y : Y.toScheme) :
    ∃ m : CharacterTermIndex f,
      y ∈ (T.saturationCharacterCocycle Y U hU hY f hf hunit).nonvanishingOpen
        (T.saturationCharacterSection Y U hU hY f hf hunit m) := by
  let C := T.saturationCharacterCocycle Y U hU hY f hf hunit
  obtain ⟨m, hm⟩ := C.covers y
  refine ⟨m, ?_⟩
  rw [C.nonvanishing_iff_value m _ y hm,
    T.saturationCharacterSection_value Y U hU hY f hf hunit m]
  refine ⟨(T.localCharacterFrame Y f m).ne_zero, ?_⟩
  change (T.localCharacterFrame Y f m : Y.toScheme.functionField) /
      (T.localCharacterFrame Y f m : Y.toScheme.functionField) ∈ regularAtSubring Y.toScheme y
  rw [div_self (T.localCharacterFrame Y f m).ne_zero]
  exact (regularAtSubring Y.toScheme y).one_mem

/-- The selected character section is nonvanishing on its entire frame
open. -/
theorem localCharacterFrameOpen_le_nonvanishing (m : CharacterTermIndex f) :
    T.localCharacterFrameOpen Y f m ≤
      (T.saturationCharacterCocycle Y U hU hY f hf hunit).nonvanishingOpen
        (T.saturationCharacterSection Y U hU hY f hf hunit m) := by
  let C := T.saturationCharacterCocycle Y U hU hY f hf hunit
  intro y hy
  rw [C.nonvanishing_iff_value m _ y hy,
    T.saturationCharacterSection_value Y U hU hY f hf hunit m]
  refine ⟨(T.localCharacterFrame Y f m).ne_zero, ?_⟩
  change (T.localCharacterFrame Y f m : Y.toScheme.functionField) /
      (T.localCharacterFrame Y f m : Y.toScheme.functionField) ∈ regularAtSubring Y.toScheme y
  rw [div_self (T.localCharacterFrame Y f m).ne_zero]
  exact (regularAtSubring Y.toScheme y).one_mem

/-- The ordinary nonvanishing open of a character section is exactly its
order-agreement frame open. In particular invariance is already available
from the finite union of invariant boundary components defining that open. -/
theorem saturationCharacter_nonvanishing_eq (m : CharacterTermIndex f) :
    (T.saturationCharacterCocycle Y U hU hY f hf hunit).nonvanishingOpen
        (T.saturationCharacterSection Y U hU hY f hf hunit m) =
      T.localCharacterFrameOpen Y f m := by
  let C := T.saturationCharacterCocycle Y U hU hY f hf hunit
  let s := T.saturationCharacterSection Y U hU hY f hf hunit m
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  apply le_antisymm _
    (T.localCharacterFrameOpen_le_nonvanishing Y U hU hY f hf hunit m)
  intro y hy
  apply (T.mem_boundaryOrderAgreementOpen (value f)
    (value (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val))) (Y.ι y)).mpr
  intro q hyq
  let W := Y.ι ''ᵁ C.nonvanishingOpen s
  have hyW : Y.ι y ∈ W := ⟨y, hy, rfl⟩
  have hqW : q.val ∈ W :=
    (specializes_iff_mem_closure.mpr hyq).mem_open W.isOpen hyW
  obtain ⟨z, hz, hzq⟩ := hqW
  change Y.ι z = q.val at hzq
  have hord := C.order_add_weilCoefficient_eq_zero_of_nonvanishing s z hz
  rw [T.saturationCharacterSection_value Y U hU hY f hf hunit m] at hord
  rw [show C.toCartierData.weilCoefficient =
      T.cancelledBoundaryCoefficient Y (value f) from
    cartierCocycleOfOrderAtlas_weilCoefficient (Y.ι ≫ X.hom) _ _ _ _ _] at hord
  change Y.toScheme.ord
      (dominantFunctionFieldMap Y.ι
        (value (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val)))) z +
      T.cancelledBoundaryCoefficient Y (value f) z = 0 at hord
  rw [schemeOrder_openImmersion, cancelledBoundaryCoefficient, hzq,
    if_pos q.property.2] at hord
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hord)

end PaperVerification.ToricSchemes.SplitToricEmbedding
