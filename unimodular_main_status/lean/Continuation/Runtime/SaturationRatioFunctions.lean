module

public import Continuation.Runtime.SaturationCharacterSections
public import Continuation.Runtime.SaturationEquationNonvanishing
public import Continuation.Runtime.CartierRatioOpenGeometry
public import Continuation.Runtime.ToricOpenRestriction

/-!
# The actual regular functions on a saturation's character opens

The saturation construction supplies global Cartier sections for the
original Laurent equation and for its character terms. Dividing them by
a nonvanishing character section gives ordinary regular functions. The
distinguished ratio is one, and the original equation's ratio has affine
nonvanishing open. These are the coefficient and affineness inputs for
the faithfully flat Laurent descent argument.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [NoetherianSpace X.left]
    (T : SplitToricEmbedding k n X)

local instance saturationRatioLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

variable (Y : X.left.Opens) [Nonempty Y]

local instance saturationRatioIntegral : IsIntegral Y.toScheme :=
  isIntegral_of_isOpenImmersion Y.ι

local instance saturationRatioSmooth : Smooth (Y.ι ≫ X.hom) := by infer_instance

local instance saturationRatioOpenNoetherian : IsLocallyNoetherian Y.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian (Y.ι ≫ X.hom)

variable (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hY : (Y : Set X.left) =
      GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left))
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : f ≠ 0)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f))

/-- The ordinary nonvanishing open of the specified character section. -/
abbrev saturationCharacterOpen (m : CharacterTermIndex f) : Y.toScheme.Opens :=
  (T.saturationCharacterCocycle Y U hU hY f hf hunit).nonvanishingOpen
    (T.saturationCharacterSection Y U hU hY f hf hunit m)

/-- The ordinary global regular function obtained by dividing one
character section by the displayed nonvanishing character section. -/
def saturationCharacterRatio (m j : CharacterTermIndex f) :
    Γ((T.saturationCharacterOpen Y U hU hY f hf hunit m).toScheme, ⊤) :=
  (T.saturationCharacterCocycle Y U hU hY f hf hunit).ratioGlobalSection
    (T.saturationCharacterSection Y U hU hY f hf hunit j)
    (T.saturationCharacterSection Y U hU hY f hf hunit m)

@[simp]
theorem saturationCharacterRatio_self (m : CharacterTermIndex f) :
    T.saturationCharacterRatio Y U hU hY f hf hunit m m = 1 :=
  (T.saturationCharacterCocycle Y U hU hY f hf hunit).ratioGlobalSection_self _

/-- The equation divided by the same character, as a literal regular
function on that character's nonvanishing open. -/
def saturationEquationRatio (m : CharacterTermIndex f) :
    Γ((T.saturationCharacterOpen Y U hU hY f hf hunit m).toScheme, ⊤) :=
  (T.saturationCharacterCocycle Y U hU hY f hf hunit).ratioGlobalSection
    (T.saturationEquationSection Y U hU hY f hf hunit)
    (T.saturationCharacterSection Y U hU hY f hf hunit m)

include hY in
/-- Saturation contains the original open, as an inequality of the
actual opens used for the restriction morphism. -/
theorem originalOpen_le_saturationOpen : U ≤ Y := by
  intro x hx
  change x ∈ (Y : Set X.left)
  rw [hY]
  exact GroupAction.subset_saturation _ _ _ hx

include hY in
/-- The saturation's actual restricted action is available independently
of its affineness or any choice of character section. -/
theorem saturationOpen_invariant :
    (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ Y =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ Y := by
  apply Opens.ext
  change _ ⁻¹' (Y : Set X.left) = _ ⁻¹' (Y : Set X.left)
  rw [hY]
  exact GroupAction.action_preimage_saturation _ _ _

/-- Each character open is invariant under the genuine action restricted
to the saturation. -/
theorem saturationCharacterOpen_invariant (m : CharacterTermIndex f) :
    let hInv := saturationOpen_invariant Y U hY
    letI := GroupAction.restrictedModObj X (splitTorusOver k (Fin n → ℤ)) Y hInv
    (γ[splitTorusOver k (Fin n → ℤ),GroupAction.openOver X Y]).left ⁻¹ᵁ
        T.saturationCharacterOpen Y U hU hY f hf hunit m =
      (snd (splitTorusOver k (Fin n → ℤ)) (GroupAction.openOver X Y)).left ⁻¹ᵁ
        T.saturationCharacterOpen Y U hU hY f hf hunit m := by
  let hInv := saturationOpen_invariant Y U hY
  letI := GroupAction.restrictedModObj X (splitTorusOver k (Fin n → ℤ)) Y hInv
  letI : IsModHom (splitTorusOver k (Fin n → ℤ)) (GroupAction.openInclusion X Y) :=
    GroupAction.openInclusion_isModHom X _ Y hInv
  rw [show T.saturationCharacterOpen Y U hU hY f hf hunit m =
      T.localCharacterFrameOpen Y f m from
    T.saturationCharacter_nonvanishing_eq Y U hU hY f hf hunit m]
  exact GroupAction.invariant_preimage _ (GroupAction.openInclusion X Y) _
    (T.boundaryOrderAgreementOpen_invariant _ _)

/-- The actual principal open of the equation ratio is affine. Its
affineness is inherited from the original affine open, through the
reciprocal Cartier ratio. -/
theorem saturationEquationRatio_basicOpen_isAffine [X.left.IsSeparated]
    (hequation : ∀ x ∈ T.torusOpen,
      (openTorusRationalAlgHom k n X.left T.torus.left f)⁻¹ ∈
        regularAtSubring X.left x ↔ x ∈ U)
    (m : CharacterTermIndex f) :
    IsAffineOpen ((T.saturationCharacterOpen Y U hU hY f hf hunit m).toScheme.basicOpen
      (T.saturationEquationRatio Y U hU hY f hf hunit m)) := by
  apply (T.saturationCharacterCocycle Y U hU hY f hf hunit).ratioGlobalSection_basicOpen_isAffine
  rw [T.saturationEquation_nonvanishing_eq Y U hU hY f hf hunit hequation]
  apply hU.preimage_of_isOpenImmersion Y.ι
  simpa only [Scheme.Opens.opensRange_ι] using
    (originalOpen_le_saturationOpen Y U hY)

include hY in
/-- The saturation contains the whole original torus, including all
scheme points over extensions of the ground field. -/
theorem torusOpen_le_saturationOpen : T.torusOpen ≤ Y := by
  intro x hx
  change x ∈ (Y : Set X.left)
  rw [hY]
  exact T.torusOpen_subset_saturation U hx

/-- Every character open contains the torus of the actual saturation. -/
theorem saturationCharacterOpen_contains_torus (m : CharacterTermIndex f) :
    let hInv := saturationOpen_invariant Y U hY
    letI := GroupAction.restrictedModObj X (splitTorusOver k (Fin n → ℤ)) Y hInv
    (T.restrictToInvariantOpen Y hInv (T.torusOpen_le_saturationOpen Y U hY)).torusOpen ≤
      T.saturationCharacterOpen Y U hU hY f hf hunit m := by
  let hInv := saturationOpen_invariant Y U hY
  letI := GroupAction.restrictedModObj X (splitTorusOver k (Fin n → ℤ)) Y hInv
  dsimp only
  rw [T.restrictToInvariantOpen_torusOpen,
    show T.saturationCharacterOpen Y U hU hY f hf hunit m =
      T.localCharacterFrameOpen Y f m from
      T.saturationCharacter_nonvanishing_eq Y U hU hY f hf hunit m]
  exact Y.ι.preimage_mono (T.torusOpen_le_boundaryOrderAgreementOpen _ _)

end PaperVerification.ToricSchemes.SplitToricEmbedding
