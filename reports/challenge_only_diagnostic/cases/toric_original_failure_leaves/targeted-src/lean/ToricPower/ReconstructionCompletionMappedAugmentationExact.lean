module

public import ToricPower.SingleAugmentationComparison

/-! # Exactness of an actual mapped single-target augmentation

The original component square is used before a scheme or cellular model
is substituted. Both the coefficient comparison and its cancellation
retain the given mapped augmentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v'

variable {B : Type u} [Category.{v} B] [Abelian B]
  {C : Type u'} [Category.{v'} C] [Abelian C]
  (F : B ⥤ C) [F.Additive]
  {K : CochainComplex B ℕ} {L : CochainComplex C ℕ}
  {M : B} {P N : C} {n : ℕ}

/-- An original top-component square proves exactness of the mapped
augmentation followed by its canonical single-complex comparison. -/
theorem reconstruction_mappedSingleAugmentation_adjusted_quasiIso
    (f : K ⟶ (HomologicalComplex.single B (.up ℕ) n).obj M)
    (g : L ⟶ (HomologicalComplex.single C (.up ℕ) n).obj P)
    (e : (F.mapHomologicalComplex (.up ℕ)).obj K ≅ L)
    (t : F.obj M ≅ N) (u : P ≅ N) (q : L.X n ⟶ P)
    (component : singleAugmentationComponent g = q)
    (square : F.map (singleAugmentationComponent f) ≫ t.hom =
      e.hom.f n ≫ q ≫ u.hom)
    (exact : QuasiIso g) :
    QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map f ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app M) := by
  letI := exact
  let adjusted := (F.mapHomologicalComplex (.up ℕ)).map f ≫
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app M
  let original := g ≫ (HomologicalComplex.single C (.up ℕ) n).map u.hom
  haveI : QuasiIso original := inferInstance
  apply singleAugmentation_quasiIso_of_comparison adjusted original e t
  dsimp only [adjusted, original]
  rw [singleAugmentationComponent_map, singleAugmentationComponent_singleMap, component]
  exact square

/-- The same square proves exactness of the original mapped chain map,
before its canonical coefficient comparison. -/
theorem reconstruction_mappedSingleAugmentation_quasiIso
    (f : K ⟶ (HomologicalComplex.single B (.up ℕ) n).obj M)
    (g : L ⟶ (HomologicalComplex.single C (.up ℕ) n).obj P)
    (e : (F.mapHomologicalComplex (.up ℕ)).obj K ≅ L)
    (t : F.obj M ≅ N) (u : P ≅ N) (q : L.X n ⟶ P)
    (component : singleAugmentationComponent g = q)
    (square : F.map (singleAugmentationComponent f) ≫ t.hom =
      e.hom.f n ≫ q ≫ u.hom)
    (exact : QuasiIso g) :
    QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map f) := by
  haveI adjusted : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map f ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app M) :=
    reconstruction_mappedSingleAugmentation_adjusted_quasiIso F f g e t u q
      component square exact
  exact quasiIso_of_comp_right _
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app M)

end ToricPower

end
