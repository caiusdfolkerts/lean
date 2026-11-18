module

public import Continuation.Runtime.SaturationAffineCharacterOpens
public import Continuation.Runtime.AffineTorusEquation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Invariant affine neighbourhoods of a smooth split toric variety

Every point of the original smooth separated toric scheme has an invariant
affine neighbourhood containing its specified dense torus. Start with an
ordinary affine neighbourhood, choose its genuine Laurent equation on the
torus, saturate by the whole group scheme, and use the finite character
cover of that saturation. Affineness of its members follows from the
faithfully flat Laurent argument.

The field is arbitrary. No projectivity, ampleness, invariant affine cover,
fan presentation, or density of rational torus points is assumed.
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
    [X.left.IsSeparated]
    (T : SplitToricEmbedding k n X)

local instance affineNeighbourhoodLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

include T in
/-- The actual torus action is open: its action graph identifies it with
a smooth projection. -/
theorem action_isOpenMap : IsOpenMap (γ[splitTorusOver k (Fin n → ℤ),X]).left := by
  let G := splitTorusOver k (Fin n → ℤ)
  let e := (Over.forget (Spec (CommRingCat.of k))).mapIso (ModObj.actionGraphIso G X)
  letI : Smooth G.hom := T.torus_smooth
  letI : Smooth (snd G X).left := by
    change Smooth (Limits.pullback.snd G.hom X.hom)
    infer_instance
  have ha : e.hom ≫ (snd G X).left = (γ[G,X]).left :=
    congrArg (fun f : G ⊗ X ⟶ X => f.left) (ModObj.actionGraphIso_hom_snd G X)
  letI : Smooth (γ[G,X]).left := by
    rw [← ha]
    infer_instance
  exact (γ[G,X]).left.isOpenMap

/-- Every original point has an actual invariant affine neighbourhood,
with the original dense torus and its original character lattice. -/
theorem exists_invariant_affine_neighbourhood (x : X.left) :
    ∃ W : X.left.Opens, x ∈ W ∧ IsAffineOpen W ∧ T.torusOpen ≤ W ∧
      (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ W =
        (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ W := by
  classical
  let G := splitTorusOver k (Fin n → ℤ)
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (x := x) (U := ⊤) (by trivial)
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨f, hf, hequation⟩ := T.exists_affineTorusEquation U hU
  have hunit : ∀ z ∈ U, z ∈ T.torusOpen → IsRegularUnitAt X.left z
      (openTorusRationalAlgHom k n X.left T.torus.left f) := by
    intro z hzU hzT
    exact ⟨T.laurentValue_mem_regularAt_torus f z hzT,
      (hequation z hzT).mpr hzU⟩
  let Y : X.left.Opens :=
    ⟨GroupAction.saturation G X (U : Set X.left),
      GroupAction.saturation_isOpen G X T.action_isOpenMap U.isOpen⟩
  have hY : (Y : Set X.left) = GroupAction.saturation G X (U : Set X.left) := rfl
  have hxY : x ∈ Y := GroupAction.subset_saturation G X (U : Set X.left) hxU
  letI : Nonempty Y := ⟨⟨x, hxY⟩⟩
  letI : IsIntegral Y.toScheme := isIntegral_of_isOpenImmersion Y.ι
  letI : Smooth (Y.ι ≫ X.hom) := by infer_instance
  letI : IsLocallyNoetherian Y.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Y.ι ≫ X.hom)
  let y : Y.toScheme := ⟨x, hxY⟩
  obtain ⟨m, hm⟩ := T.saturationCharacterSections_cover Y U hU hY f hf hunit y
  let V := T.saturationCharacterOpen Y U hU hY f hf hunit m
  let W : X.left.Opens := Y.ι ''ᵁ V
  have hV : IsAffineOpen V :=
    T.saturationCharacterOpen_isAffine Y U hU hY f hf hunit hequation m
  let A := T.boundaryOrderAgreementOpen
    (openTorusRationalAlgHom k n X.left T.torus.left f)
    (openTorusRationalAlgHom k n X.left T.torus.left
      (AddMonoidAlgebra.single m.down.val (f.coeff m.down.val)))
  have hW : W = Y ⊓ A := by
    change Y.ι ''ᵁ T.saturationCharacterOpen Y U hU hY f hf hunit m = _
    rw [show T.saturationCharacterOpen Y U hU hY f hf hunit m =
        T.localCharacterFrameOpen Y f m from
      T.saturationCharacter_nonvanishing_eq Y U hU hY f hf hunit m]
    change Y.ι ''ᵁ (Y.ι ⁻¹ᵁ A) = Y ⊓ A
    simpa only [Scheme.Opens.opensRange_ι] using
      (Y.ι.image_preimage_eq_opensRange_inf A)
  refine ⟨W, ⟨y, hm, rfl⟩, hV.image_of_isOpenImmersion Y.ι, ?_, ?_⟩
  · rw [hW]
    exact le_inf (T.torusOpen_le_saturationOpen Y U hY)
      (T.torusOpen_le_boundaryOrderAgreementOpen _ _)
  · rw [hW, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf,
      saturationOpen_invariant Y U hY,
      T.boundaryOrderAgreementOpen_invariant]

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_invariant_affine_neighbourhood
