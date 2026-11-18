module

public import Continuation.Runtime.InvariantOrderAgreement
public import Continuation.Runtime.CartierOrderAtlas

/-!
# Monomial Cartier frames on the saturation of an affine open

The local character-ratio theorem supplies a finite invariant cover on which
one character term has the same boundary orders as the original Laurent
equation. Transporting those character terms to the actual open subscheme's
function field gives ordinary Cartier transition data. The local equations
and their exact Weil coefficients are part of the proved interface.
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

local instance saturationAtlasLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- The finite support of the Laurent equation, lifted to the scheme's
universe so that it is a valid index type for its Cartier atlas. -/
abbrev CharacterTermIndex (f : AddMonoidAlgebra k (Fin n → ℤ)) :=
  ULift.{u} {m : Fin n → ℤ // m ∈ f.coeff.support}

variable (Y : X.left.Opens) [Nonempty Y]

local instance saturationOpenIntegral : IsIntegral Y.toScheme :=
  isIntegral_of_isOpenImmersion Y.ι

local instance saturationOpenSmooth : Smooth (Y.ι ≫ X.hom) := by infer_instance

local instance saturationOpenLocallyNoetherian : IsLocallyNoetherian Y.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian (Y.ι ≫ X.hom)

/-- The original Laurent term, viewed in the actual function field of the
open subscheme. Its nonzero coefficient makes it a genuine field unit. -/
def localCharacterFrame (f : AddMonoidAlgebra k (Fin n → ℤ))
    (m : CharacterTermIndex f) : Y.toScheme.functionFieldˣ := by
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  have hc : f.coeff m.down.val ≠ 0 := Finsupp.mem_support_iff.mp m.down.property
  have hterm : (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val) :
      AddMonoidAlgebra k (Fin n → ℤ)) ≠ 0 := AddMonoidAlgebra.single_ne_zero.mpr hc
  have hvalue : value (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val)) ≠ 0 :=
    (map_ne_zero_iff value (openTorusRationalAlgHom_injective k n X.left T.torus.left)).mpr hterm
  exact Units.mk0
    (dominantFunctionFieldMap Y.ι
      (value (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val))))
    ((map_ne_zero_iff _ (dominantFunctionFieldMap_injective Y.ι)).mpr hvalue)

/-- The actual open subscheme chart on which this character has the
required boundary orders. -/
def localCharacterFrameOpen (f : AddMonoidAlgebra k (Fin n → ℤ))
    (m : CharacterTermIndex f) : Y.toScheme.Opens :=
  Y.ι ⁻¹ᵁ T.boundaryOrderAgreementOpen
    (openTorusRationalAlgHom k n X.left T.torus.left f)
    (openTorusRationalAlgHom k n X.left T.torus.left
      (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val)))

/-- The boundary divisor obtained by cancelling the boundary orders of the
Laurent equation. The coefficients are measured in the original scheme. -/
def cancelledBoundaryCoefficient (r : X.left.functionField) (y : Y.toScheme) : ℤ := by
  classical
  exact if Y.ι y ∈ T.boundary then -X.left.ord r (Y.ι y) else 0

/-- The displayed character is an actual local equation with the usual
Cartier sign on its displayed open. -/
theorem localCharacterFrame_orders (f : AddMonoidAlgebra k (Fin n → ℤ))
    (m : CharacterTermIndex f) (y : Y.toScheme)
    (hy : y ∈ T.localCharacterFrameOpen Y f m) :
    Y.toScheme.ord (T.localCharacterFrame Y f m : Y.toScheme.functionField) y =
      -T.cancelledBoundaryCoefficient Y
        (openTorusRationalAlgHom k n X.left T.torus.left f) y := by
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  change Y.toScheme.ord
      (dominantFunctionFieldMap Y.ι
        (value (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val)))) y = _
  rw [schemeOrder_openImmersion]
  by_cases hb : Y.ι y ∈ T.boundary
  · rw [cancelledBoundaryCoefficient, if_pos hb, neg_neg]
    by_cases hheight : Order.coheight (Y.ι y) = 1
    · exact (T.mem_boundaryOrderAgreementOpen _ _ (Y.ι y)).mp hy
        ⟨Y.ι y, hheight, hb⟩ (subset_closure (Set.mem_singleton (Y.ι y)))
    · simp only [Scheme.ord_eq_zero_of_coheight_neq_one hheight]
  · rw [cancelledBoundaryCoefficient, if_neg hb, neg_zero]
    have hc : f.coeff m.down.val ≠ 0 := Finsupp.mem_support_iff.mp m.down.property
    have hterm : IsUnit (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val) :
        AddMonoidAlgebra k (Fin n → ℤ)) :=
      isUnit_single_character k n (Units.mk0 _ hc) m.down.val
    have hregular := T.laurentUnit_isRegularUnitAt_torus _ hterm
      (Y.ι y) (Classical.not_not.mp hb)
    exact rationalOrder_zero_of_isRegularUnitAt (Y.ι y) _
      ((hterm.map value).ne_zero) hregular

/-- These are a genuine cover of the saturation, derived from the local
unit ratios on the original affine open. -/
theorem localCharacterFrameOpen_covers
    (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hY : (Y : Set X.left) =
      GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left))
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : f ≠ 0)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f)) :
    ∀ y : Y.toScheme, ∃ m : CharacterTermIndex f,
      y ∈ T.localCharacterFrameOpen Y f m := by
  intro y
  have hy : Y.ι y ∈ GroupAction.saturation
      (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left) := by
    rw [← hY]
    exact y.property
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp
    (T.saturation_subset_characterOrderAgreementOpens U hU f hf hunit hy)
  exact ⟨ULift.up m, hm⟩

/-- The actual invertible fractional sheaf on the saturation. Its frames
are the displayed monomials, and their unit transitions follow from the
normal local-order criterion. -/
def saturationCharacterCocycle
    (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hY : (Y : Set X.left) =
      GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left))
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : f ≠ 0)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f)) :
    RationalCartierCocycle Y.toScheme :=
  cartierCocycleOfOrderAtlas (Y.ι ≫ X.hom)
    (T.cancelledBoundaryCoefficient Y
      (openTorusRationalAlgHom k n X.left T.torus.left f))
    (T.localCharacterFrameOpen Y f)
    (T.localCharacterFrameOpen_covers Y U hU hY f hf hunit)
    (T.localCharacterFrame Y f) (T.localCharacterFrame_orders Y f)

end PaperVerification.ToricSchemes.SplitToricEmbedding
