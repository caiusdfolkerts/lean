module

public import ToricPower.MappedSingleAugmentation
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Genuine injective resolutions under an exact injective-preserving functor -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {A D E : Type*} [Category* A] [Category* D] [Category* E]
  [Abelian A] [Abelian D] [Abelian E]
  (F : A ⥤ D) [F.Additive] [F.PreservesHomology] [F.PreservesInjectiveObjects]
  {M : A} (J : InjectiveResolution M)

/-- The literal functor image is a genuine injective resolution. -/
def mappedInjectiveResolution : InjectiveResolution (F.obj M) where
  cocomplex := (F.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  injective n := F.injective_obj_of_injective (J.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app M ≫
    (F.mapHomologicalComplex (.up ℕ)).map J.ι

theorem mappedInjectiveResolution_zero :
    (mappedInjectiveResolution F J).ι.f 0 = F.map (J.ι.f 0) :=
  mappedSingleAugmentation_core_zero F J.ι

variable (G : D ⥤ E) [G.Additive] (H : A ⥤ E) [H.Additive]
  (comparison : F ⋙ G ≅ H) {V : E}

/-- The full section comparison retains the original augmentation,
provided its degree-zero coefficient map agrees under the given natural isomorphism. -/
theorem mappedInjectiveSection_comparison
    (a : V ⟶ G.obj (F.obj M)) (b : V ⟶ H.obj M)
    (same : a ≫ comparison.hom.app M = b) :
    mappedSingleAugmentation G a (mappedInjectiveResolution F J).ι ≫
      (Functor.mapHomologicalComplexCompIso comparison (.up ℕ)).hom.app J.cocomplex =
        mappedSingleAugmentation H b J.ι := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f,mappedSingleAugmentation_zero,
    mappedInjectiveResolution_zero]
  let f : M ⟶ J.cocomplex.X 0 := J.ι.f 0
  change (a ≫ G.map (F.map f)) ≫ comparison.hom.app (J.cocomplex.X 0) =
    b ≫ H.map f
  have natural := comparison.hom.naturality f
  change G.map (F.map f) ≫ comparison.hom.app (J.cocomplex.X 0) =
    comparison.hom.app M ≫ H.map f at natural
  rw [Category.assoc,natural,← Category.assoc,same]

/-- A genuine natural section comparison transports the canonical
augmentation quasi-isomorphism to the functor-image injective resolution. -/
theorem mappedInjectiveSection_quasiIso
    (a : V ⟶ G.obj (F.obj M)) (b : V ⟶ H.obj M)
    (same : a ≫ comparison.hom.app M = b)
    [QuasiIso (mappedSingleAugmentation H b J.ι)] :
    QuasiIso (mappedSingleAugmentation G a (mappedInjectiveResolution F J).ι) := by
  haveI : QuasiIso
      (mappedSingleAugmentation G a (mappedInjectiveResolution F J).ι ≫
        (Functor.mapHomologicalComplexCompIso comparison (.up ℕ)).hom.app J.cocomplex) := by
    rw [mappedInjectiveSection_comparison F J G H comparison a b same]
    infer_instance
  exact quasiIso_of_comp_right _
    ((Functor.mapHomologicalComplexCompIso comparison (.up ℕ)).hom.app J.cocomplex)

end ToricPower

end
