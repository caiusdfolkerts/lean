module

public import PaperVerification.ToricBoundaryFixedPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

/-! # Actual geometric properties of the torus action product -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricCharacters

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))

/-- The already proved torus integrality with the literal over-object domain. -/
instance splitTorusOver_left_integral :
    IsIntegral (splitTorusOver k (Fin n→ℤ)).left :=
  splitTorus_integral k n

instance torusProduct_integral [IsIntegral X.left] [IsLocallyNoetherian X.left] :
    IsIntegral (splitTorusOver k (Fin n→ℤ) ⊗ X).left := by
  change IsIntegral (pullback (splitTorusOver k (Fin n→ℤ)).hom X.hom)
  infer_instance

/-- The self-action object's scheme is the same actual product scheme. -/
instance torusActionObject_integral [IsIntegral X.left] [IsLocallyNoetherian X.left] :
    IsIntegral (MonoidalLeftActionStruct.actionObj (splitTorusOver k (Fin n→ℤ)) X).left := by
  change IsIntegral (splitTorusOver k (Fin n→ℤ) ⊗ X).left
  exact torusProduct_integral k n X

instance torusProjection_surjective :
    Surjective (snd (splitTorusOver k (Fin n→ℤ)) X).left := by
  change Surjective (pullback.snd (splitTorusOver k (Fin n→ℤ)).hom X.hom)
  infer_instance

variable [ModObj (splitTorusOver k (Fin n→ℤ)) X]

instance torusAction_surjective : Surjective (γ[splitTorusOver k (Fin n→ℤ),X]).left := by
  constructor
  intro x
  let G := splitTorusOver k (Fin n→ℤ)
  let e : X ⟶ G⊗X := lift (1 : X ⟶ G) (𝟙 X)
  refine ⟨e.left x,?_⟩
  have h : e≫γ[G,X]=𝟙 X := by
    change (1 : X ⟶ G) • (𝟙 X)=𝟙 X
    exact one_smul _ _
  exact congrArg (fun f : X ⟶ X=>f.left x) h

namespace SplitToricEmbedding

variable {k n X} (T : SplitToricEmbedding k n X) [Smooth X.hom]

/-- The given immersion, exposed at the literal split-torus scheme type. -/
instance torus_scheme_isOpenImmersion :
    IsOpenImmersion (show splitTorus k (Fin n→ℤ) ⟶ X.left from T.torus.left) :=
  T.open_immersion

/-- The same given immersion, exposed at its actual affine spectrum type. -/
instance torus_coordinate_isOpenImmersion :
    IsOpenImmersion (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X.left
      from T.torus.left) :=
  T.open_immersion

/-- The actual torus inclusion respects the given structure maps. -/
instance torus_scheme_isOver :
    (show splitTorus k (Fin n→ℤ) ⟶ X.left from T.torus.left).IsOver
      (Spec (CommRingCat.of k)) where
  comp_over := T.torus.w

/-- The same structural compatibility at the literal coordinate spectrum. -/
instance torus_coordinate_isOver :
    (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X.left
      from T.torus.left).IsOver (Spec (CommRingCat.of k)) where
  comp_over := T.torus.w

include T in
theorem torus_smooth : Smooth (splitTorusOver k (Fin n→ℤ)).hom := by
  rw [← T.torus.w]
  infer_instance

include T in
/-- The ordinary smoothness of the action product follows from the
actual dense open torus immersion and base change. -/
theorem product_smooth : Smooth (splitTorusOver k (Fin n→ℤ) ⊗ X).hom := by
  let G := splitTorusOver k (Fin n→ℤ)
  letI : Smooth G.hom := T.torus_smooth
  letI : Smooth (snd G X).left := by
    change Smooth (pullback.snd G.hom X.hom)
    infer_instance
  rw [← (snd G X).w]
  infer_instance

include T in
theorem product_locallyNoetherian :
    IsLocallyNoetherian (splitTorusOver k (Fin n→ℤ) ⊗ X).left := by
  letI := T.product_smooth
  exact LocallyOfFiniteType.isLocallyNoetherian
    (splitTorusOver k (Fin n→ℤ) ⊗ X).hom

end SplitToricEmbedding

end PaperVerification.ToricSchemes
