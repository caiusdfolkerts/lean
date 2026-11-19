module

public import Continuation.Runtime.SaturationCharacterSections
public import Continuation.Runtime.AffineTorusEquation

/-!
# The original affine open is the equation's exact nonvanishing locus

The equation and its Cartier frames were constructed on the saturation.
Here the ordinary nonvanishing open is shown to be exactly the original
affine open. The proof checks the torus directly in its actual local rings,
uses invariance of each boundary generic point, and then applies purity of
the complement of an affine open to exclude any additional points.
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

local instance saturationEquationLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

variable (Y : X.left.Opens) [Nonempty Y]

local instance saturationEquationIntegral : IsIntegral Y.toScheme :=
  isIntegral_of_isOpenImmersion Y.ι

local instance saturationEquationSmooth : Smooth (Y.ι ≫ X.hom) := by infer_instance

local instance saturationEquationOpenNoetherian : IsLocallyNoetherian Y.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian (Y.ι ≫ X.hom)

variable (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hY : (Y : Set X.left) =
      GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left))
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : f ≠ 0)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f))

/-- On the open torus, nonvanishing of the constructed section is exactly
inverse regularity of its original Laurent equation. -/
theorem saturationEquation_nonvanishing_on_torus
    (y : Y.toScheme) (hyT : Y.ι y ∈ T.torusOpen) :
    y ∈ (T.saturationCharacterCocycle Y U hU hY f hf hunit).nonvanishingOpen
        (T.saturationEquationSection Y U hU hY f hf hunit) ↔
      (openTorusRationalAlgHom k n X.left T.torus.left f)⁻¹ ∈
        regularAtSubring X.left (Y.ι y) := by
  let C := T.saturationCharacterCocycle Y U hU hY f hf hunit
  let s := T.saturationEquationSection Y U hU hY f hf hunit
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  have hvf : value f ≠ 0 :=
    (map_ne_zero_iff value (openTorusRationalAlgHom_injective k n X.left T.torus.left)).mpr hf
  have hrf : dominantFunctionFieldMap Y.ι (value f) ≠ 0 :=
    (map_ne_zero_iff _ (dominantFunctionFieldMap_injective Y.ι)).mpr hvf
  obtain ⟨m, hm⟩ := C.covers y
  have hc : f.coeff m.down.val ≠ 0 := Finsupp.mem_support_iff.mp m.down.property
  have hterm : IsUnit (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val) :
      AddMonoidAlgebra k (Fin n → ℤ)) :=
    isUnit_single_character k n (Units.mk0 _ hc) m.down.val
  have hframe : IsRegularUnitAt Y.toScheme y
      (T.localCharacterFrame Y f m : Y.toScheme.functionField) :=
    isRegularUnitAt_pullback Y.ι y _
      (T.laurentUnit_isRegularUnitAt_torus _ hterm (Y.ι y) hyT)
  rw [C.nonvanishing_iff_value m s y hm,
    T.saturationEquationSection_value Y U hU hY f hf hunit]
  change (dominantFunctionFieldMap Y.ι (value f) ≠ 0 ∧
      (T.localCharacterFrame Y f m : Y.toScheme.functionField) /
        dominantFunctionFieldMap Y.ι (value f) ∈ regularAtSubring Y.toScheme y) ↔ _
  rw [and_iff_right hrf]
  change (T.localCharacterFrame Y f m : Y.toScheme.functionField) /
      dominantFunctionFieldMap Y.ι (value f) ∈ regularAtSubring Y.toScheme y ↔ _
  rw [← regularAt_openImmersion_iff Y.ι y ((value f)⁻¹), map_inv₀]
  constructor
  · intro h
    have hp := (regularAtSubring Y.toScheme y).mul_mem hframe.2 h
    simpa only [div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ (T.localCharacterFrame Y f m).ne_zero, one_mul] using hp
  · intro h
    simpa only [div_eq_mul_inv] using
      (regularAtSubring Y.toScheme y).mul_mem hframe.1 h

/-- The nonvanishing open of the original equation is exactly the original
affine open, viewed inside its saturation. Every hypothesis refers to
actual schemes, local rings and the actual Laurent coordinate map. -/
theorem saturationEquation_nonvanishing_eq [X.left.IsSeparated]
    (hequation : ∀ x ∈ T.torusOpen,
      (openTorusRationalAlgHom k n X.left T.torus.left f)⁻¹ ∈
        regularAtSubring X.left x ↔ x ∈ U) :
    (T.saturationCharacterCocycle Y U hU hY f hf hunit).nonvanishingOpen
        (T.saturationEquationSection Y U hU hY f hf hunit) = Y.ι ⁻¹ᵁ U := by
  let C := T.saturationCharacterCocycle Y U hU hY f hf hunit
  let s := T.saturationEquationSection Y U hU hY f hf hunit
  let W := Y.ι ''ᵁ C.nonvanishingOpen s
  have hUY : U ≤ Y := by
    intro x hx
    change x ∈ (Y : Set X.left)
    rw [hY]
    exact GroupAction.subset_saturation _ _ _ hx
  have hUW : U ≤ W := by
    intro x hx
    let y : Y.toScheme := ⟨x, hUY hx⟩
    exact ⟨y, T.originalOpen_le_equationNonvanishing Y U hU hY f hf hunit hx, rfl⟩
  have hnormal : ∀ V : X.left.Opens, IsAffineOpen V → Nonempty V →
      IsIntegrallyClosed Γ(X.left,V) := by
    intro V hV hne
    letI := hne
    exact smooth_affineOpen_isIntegrallyClosed X.hom V hV
  have hWU : W = U := by
    apply affineOpen_eq_of_codimensionOne_membership hnormal U W hU hUW
    rintro x ⟨y, hy, rfl⟩ hcodim
    by_cases hb : Y.ι y ∈ T.boundary
    · apply (T.boundaryPrime_mem_saturation_iff U ⟨Y.ι y, hcodim, hb⟩).mp
      rw [← hY]
      exact y.property
    · have hyT : Y.ι y ∈ T.torusOpen := Classical.not_not.mp hb
      exact (hequation (Y.ι y) hyT).mp
        ((T.saturationEquation_nonvanishing_on_torus Y U hU hY f hf hunit y hyT).mp hy)
  have hpre := congrArg (fun V => Y.ι ⁻¹ᵁ V) hWU
  simpa only [W, Scheme.Hom.preimage_image_eq] using hpre

end PaperVerification.ToricSchemes.SplitToricEmbedding
