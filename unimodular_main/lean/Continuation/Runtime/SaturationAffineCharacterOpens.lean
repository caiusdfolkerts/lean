module

public import Continuation.Runtime.SaturationRatioFunctions
public import Continuation.Runtime.ToricCharacterSectionAffineness

/-!
# The saturation's invariant character opens are affine

This is the affine-neighbourhood conclusion of the original local Laurent
equation construction. The Cartier data, character sections, exact
nonvanishing opens and their invariance are supplied by the preceding
geometric proofs. The only scalar division is by a nonzero coefficient
already in the equation's finite support. The argument applies over an
arbitrary ground field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [NoetherianSpace X.left]
    [X.left.IsSeparated]
    (T : SplitToricEmbedding k n X)

local instance saturationAffineLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

variable (Y : X.left.Opens) [Nonempty Y]

local instance saturationAffineIntegral : IsIntegral Y.toScheme :=
  isIntegral_of_isOpenImmersion Y.ι

local instance saturationAffineSmooth : Smooth (Y.ι ≫ X.hom) := by infer_instance

local instance saturationAffineOpenNoetherian : IsLocallyNoetherian Y.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian (Y.ι ≫ X.hom)

variable (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hY : (Y : Set X.left) =
      GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left))
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : f ≠ 0)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f))
    (hequation : ∀ x ∈ T.torusOpen,
      (openTorusRationalAlgHom k n X.left T.torus.left f)⁻¹ ∈
        regularAtSubring X.left x ↔ x ∈ U)

include hequation in
/-- Every member of the actual finite invariant character cover of the
saturation is an affine open subscheme. -/
theorem saturationCharacterOpen_isAffine (m : CharacterTermIndex f) :
    IsAffineOpen (T.saturationCharacterOpen Y U hU hY f hf hunit m) := by
  classical
  let G := splitTorusOver k (Fin n → ℤ)
  let hInv := saturationOpen_invariant Y U hY
  letI := GroupAction.restrictedModObj X G Y hInv
  let Z := GroupAction.openOver X Y
  letI : IsIntegral (GroupAction.openOver X Y).left :=
    inferInstanceAs (IsIntegral Y.toScheme)
  letI : IsIntegral Z.left := inferInstanceAs (IsIntegral Y.toScheme)
  letI : NoetherianSpace (GroupAction.openOver X Y).left := by
    change NoetherianSpace (Y : Set X.left)
    infer_instance
  letI : Smooth (GroupAction.openOver X Y).hom :=
    inferInstanceAs (Smooth (Y.ι ≫ X.hom))
  letI : IsDominant (GroupAction.openInclusion X Y).left :=
    inferInstanceAs (IsDominant Y.ι)
  let S := T.restrictToInvariantOpen Y hInv (T.torusOpen_le_saturationOpen Y U hY)
  let C := T.saturationCharacterCocycle Y U hU hY f hf hunit
  let s := T.saturationEquationSection Y U hU hY f hf hunit
  let t := T.saturationCharacterSection Y U hU hY f hf hunit
  let w : CharacterTermIndex f → Fin n → ℤ := fun j => j.down.val
  let c : CharacterTermIndex f → k := fun j => f.coeff j.down.val
  letI : Fintype (CharacterTermIndex f) := Fintype.ofFinite _
  have hw : Function.Injective w := by
    intro i j hij
    apply ULift.ext
    exact Subtype.ext hij
  have hvalue : ∀ j, C.toCartierData.sectionValue ⊤ (t j) =
      openTorusRationalAlgHom k n Z.left S.torus.left
        (AddMonoidAlgebra.single (w j) (c j)) := by
    intro j
    rw [show C.toCartierData.sectionValue ⊤ (t j) =
      (T.localCharacterFrame Y f j : Y.toScheme.functionField) from
      T.saturationCharacterSection_value Y U hU hY f hf hunit j]
    exact T.laurentValue_pullback S (GroupAction.openInclusion X Y)
      (T.restrictToInvariantOpen_torus Y hInv (T.torusOpen_le_saturationOpen Y U hY)) _
  have hsupport : (∑ j : CharacterTermIndex f,
      AddMonoidAlgebra.single (w j) (c j)) = f := by
    calc
      _ = ∑ j : f.coeff.support, AddMonoidAlgebra.single j.val (f.coeff j.val) :=
        Equiv.sum_comp (Equiv.ulift : CharacterTermIndex f ≃ f.coeff.support) _
      _ = ∑ j ∈ f.coeff.support, AddMonoidAlgebra.single j (f.coeff j) :=
        Finset.sum_coe_sort f.coeff.support
          (fun j => AddMonoidAlgebra.single j (f.coeff j))
      _ = f := AddMonoidAlgebra.sum_coeff_single f
  have hsum : C.toCartierData.sectionValue ⊤ s =
      ∑ j, C.toCartierData.sectionValue ⊤ (t j) := by
    rw [show C.toCartierData.sectionValue ⊤ s =
      dominantFunctionFieldMap Y.ι
        (openTorusRationalAlgHom k n X.left T.torus.left f) from
      T.saturationEquationSection_value Y U hU hY f hf hunit]
    simp only [show ∀ j, C.toCartierData.sectionValue ⊤ (t j) =
        (T.localCharacterFrame Y f j : Y.toScheme.functionField) from
      T.saturationCharacterSection_value Y U hU hY f hf hunit]
    change dominantFunctionFieldMap Y.ι
        (openTorusRationalAlgHom k n X.left T.torus.left f) =
      ∑ j, dominantFunctionFieldMap Y.ι
        (openTorusRationalAlgHom k n X.left T.torus.left
          (AddMonoidAlgebra.single (w j) (c j)))
    rw [← map_sum, ← map_sum, hsupport]
  have hD : IsAffineOpen (C.nonvanishingOpen s) := by
    rw [show C.nonvanishingOpen s = Y.ι ⁻¹ᵁ U from
      T.saturationEquation_nonvanishing_eq Y U hU hY f hf hunit hequation]
    apply hU.preimage_of_isOpenImmersion Y.ι
    simpa only [Scheme.Opens.opensRange_ι] using
      (originalOpen_le_saturationOpen Y U hY)
  exact S.isAffine_characterSectionOpen C s t w hw c hvalue hsum hD m
    (Finsupp.mem_support_iff.mp m.down.property)
    (T.saturationCharacterOpen_invariant Y U hU hY f hf hunit m)
    (T.saturationCharacterOpen_contains_torus Y U hU hY f hf hunit m)

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.saturationCharacterOpen_isAffine
