module
public import TauCeti.Algebra.Homology.DerivedCategory.Bounded.Basic
public import TauCeti.Algebra.Homology.DerivedCategory.Equivalence
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.Algebra.Homology.DerivedCategory.Bounded.Functor

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Shift.SingleFunctorsLift
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ZeroObject

/-!
# Categorical foundations of the toric generation argument

This compilation unit groups eight small dependency modules so that the
ordinary Lean compiler reads their common Mathlib environment once. Source
boundaries, namespaces, definitions, and proof bodies are preserved. The
compatibility import wrappers route the former module paths to this unit;
successful ordinary compilation remains required for verification.

The mathematical constructions are genuine thick envelopes, bounded derived
categories, termwise retracts of bounded complexes, and unbounded derived
Hom detection over a field. They do not assert the toric generation theorem
without its geometric and sheaf-theoretic inputs.
-/

/-! ## Source module `ToricPower.DerivedGeneratorTransfer`
Original SHA256: 4d1006cb1ae9a84c1e3798c61d76eac97920de65c25d16228d98f2fd8eb5d857.
The complete original source is retained in `third_party/categorical_sources`.
-/
section CategoricalSource05

/-!
# Classical generators under exact functors

This file uses Mathlib's actual triangulated envelope: finite sums, shifts,
cones, and retracts. The image theorem below isolates the categorical step in
Proposition 6.2. Its geometric application still requires a proof of the
retract condition for the actual finite direct-image functor.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe v₁ v₂ u₁ u₂

section Retracts

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- An inverse image of a retract-closed object property is retract-closed. -/
theorem inverseImage_stableUnderRetracts (P : ObjectProperty D)
    [P.IsStableUnderRetracts] (F : C ⥤ D) :
    (P.inverseImage F).IsStableUnderRetracts where
  of_retract r h := P.prop_of_retract (r.map F) h

/-- Vanishing of all maps out of a collection is inherited by retracts. -/
theorem rightOrthogonal_stableUnderRetracts [HasZeroMorphisms C]
    (P : ObjectProperty C) : P.rightOrthogonal.IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    intro Z f hZ
    rw [← cancel_mono r.i, zero_comp]
    exact hY (f ≫ r.i) hZ

end Retracts

section Triangulated

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]

/-- Exact functors send every object in a thick envelope into the thick
envelope of the images. This does not require fullness or faithfulness. -/
theorem exactFunctor_map_mem_triangEnvelope (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (P : ObjectProperty C) [P.Nonempty]
    {X : C} (hX : P.triangEnvelope X) :
    (P.map F).triangEnvelope (F.obj X) := by
  let := inverseImage_stableUnderRetracts (P.map F).triangEnvelope F
  have h : P.triangEnvelope ≤ ((P.map F).triangEnvelope.inverseImage F) := by
    refine (P.triangEnvelope_le_iff
      (Q := (P.map F).triangEnvelope.inverseImage F)).2 ?_
    intro Y hY
    exact (P.map F).le_triangEnvelope _ (P.prop_map_obj F hY)
  exact h X hX

/-- If every target is a retract of an image, an exact functor sends any
classical generating collection to a classical generating collection. -/
theorem map_classicalGenerator_of_retracts (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (P : ObjectProperty C) [P.Nonempty]
    (hP : P.IsClassicalTriangulatedGenerator)
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    (P.map F).IsClassicalTriangulatedGenerator := by
  apply le_antisymm le_top
  intro Y _
  obtain ⟨X, ⟨r⟩⟩ := hF Y
  apply (P.map F).triangEnvelope.prop_of_retract r
  apply exactFunctor_map_mem_triangEnvelope F P
  rw [hP]
  trivial

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The essential image of one object has the same thick envelope as its image. -/
theorem singleton_map_triangEnvelope (F : C ⥤ D) (G : C) :
    ((ObjectProperty.singleton G).map F).triangEnvelope =
      (ObjectProperty.singleton (F.obj G)).triangEnvelope := by
  apply le_antisymm
  · refine (((ObjectProperty.singleton G).map F).triangEnvelope_le_iff
      (Q := (ObjectProperty.singleton (F.obj G)).triangEnvelope)).2 ?_
    rintro Y ⟨X, hX, ⟨e⟩⟩
    have hX' : G = X := (ObjectProperty.singleton_iff G X).1 hX
    subst X
    exact (ObjectProperty.singleton (F.obj G)).triangEnvelope.prop_of_iso e
      ((ObjectProperty.singleton (F.obj G)).le_triangEnvelope _ (by simp))
  · refine ((ObjectProperty.singleton (F.obj G)).triangEnvelope_le_iff
      (Q := ((ObjectProperty.singleton G).map F).triangEnvelope)).2 ?_
    rw [ObjectProperty.singleton_le_iff]
    exact ((ObjectProperty.singleton G).map F).le_triangEnvelope _
      ((ObjectProperty.singleton G).prop_map_obj F (by simp))

/-- The single-object form of exact generation transfer. -/
theorem obj_classicalGenerator_of_retracts (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (G : C)
    (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator)
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    (ObjectProperty.singleton (F.obj G)).IsClassicalTriangulatedGenerator := by
  have h := map_classicalGenerator_of_retracts F (ObjectProperty.singleton G) hG hF
  change ((ObjectProperty.singleton G).map F).triangEnvelope = ⊤ at h
  change (ObjectProperty.singleton (F.obj G)).triangEnvelope = ⊤
  rwa [singleton_map_triangEnvelope] at h

/-- A natural splitting of `Id → U ⋙ F` proves the retract condition. -/
theorem obj_classicalGenerator_of_splitUnit (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (U : D ⥤ C)
    (η : 𝟭 D ⟶ U ⋙ F) (π : U ⋙ F ⟶ 𝟭 D) (hηπ : η ≫ π = 𝟙 (𝟭 D))
    (G : C) (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator) :
    (ObjectProperty.singleton (F.obj G)).IsClassicalTriangulatedGenerator := by
  apply obj_classicalGenerator_of_retracts F G hG
  intro Y
  refine ⟨U.obj Y, ⟨{ i := η.app Y, r := π.app Y, retract := ?_ }⟩⟩
  simpa only [NatTrans.comp_app, NatTrans.id_app, Functor.id_obj]
    using NatTrans.congr_app hηπ Y

end Triangulated

section FiniteSummands

variable {C : Type u₁} [Category.{v₁} C]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Replacing an object by an isomorphic object preserves its thick envelope. -/
theorem singleton_triangEnvelope_eq_of_iso {X Y : C} (e : X ≅ Y) :
    (ObjectProperty.singleton X).triangEnvelope =
      (ObjectProperty.singleton Y).triangEnvelope := by
  apply le_antisymm
  · refine ((ObjectProperty.singleton X).triangEnvelope_le_iff
      (Q := (ObjectProperty.singleton Y).triangEnvelope)).2 ?_
    rw [ObjectProperty.singleton_le_iff]
    exact (ObjectProperty.singleton Y).triangEnvelope.prop_of_iso e.symm
      ((ObjectProperty.singleton Y).le_triangEnvelope _ (by simp))
  · refine ((ObjectProperty.singleton Y).triangEnvelope_le_iff
      (Q := (ObjectProperty.singleton X).triangEnvelope)).2 ?_
    rw [ObjectProperty.singleton_le_iff]
    exact (ObjectProperty.singleton X).triangEnvelope.prop_of_iso e
      ((ObjectProperty.singleton X).le_triangEnvelope _ (by simp))

/-- Classical generation depends only on the isomorphism class of the object. -/
theorem classicalGenerator_iff_of_iso {X Y : C} (e : X ≅ Y) :
    (ObjectProperty.singleton X).IsClassicalTriangulatedGenerator ↔
      (ObjectProperty.singleton Y).IsClassicalTriangulatedGenerator := by
  unfold ObjectProperty.IsClassicalTriangulatedGenerator
  rw [singleton_triangEnvelope_eq_of_iso e]

/-- A finite nonempty direct sum generates the same thick subcategory as its
summands. -/
theorem biproduct_triangEnvelope_eq {I : Type*} [Finite I] [Nonempty I]
    (X : I → C) [HasBiproduct X] :
    (ObjectProperty.singleton (⨁ X)).triangEnvelope =
      (ObjectProperty.ofObj X).triangEnvelope := by
  apply le_antisymm
  · refine ((ObjectProperty.singleton (⨁ X)).triangEnvelope_le_iff
      (Q := (ObjectProperty.ofObj X).triangEnvelope)).2 ?_
    rw [ObjectProperty.singleton_le_iff]
    apply (ObjectProperty.ofObj X).triangEnvelope.prop_of_isLimit_fan (biproduct.isLimit X)
    intro i
    exact (ObjectProperty.ofObj X).le_triangEnvelope _ (ObjectProperty.ofObj_apply X i)
  · refine ((ObjectProperty.ofObj X).triangEnvelope_le_iff
      (Q := (ObjectProperty.singleton (⨁ X)).triangEnvelope)).2 ?_
    refine (ObjectProperty.ofObj_le_iff X
      (ObjectProperty.singleton (⨁ X)).triangEnvelope).2 ?_
    intro i
    exact ObjectProperty.IsStableUnderRetracts.of_biproduct
      (ObjectProperty.singleton (⨁ X)).triangEnvelope X
      ((ObjectProperty.singleton (⨁ X)).le_triangEnvelope _ (by simp)) i

/-- Isomorphic summand classes determine the thick envelope, independently
of their multiplicities. -/
theorem same_summands_triangEnvelope {I J : Type*} [Nonempty I] [Nonempty J]
    (X : I → C) (Y : J → C)
    (hXY : ∀ i, ∃ j, Nonempty (X i ≅ Y j))
    (hYX : ∀ j, ∃ i, Nonempty (Y j ≅ X i)) :
    (ObjectProperty.ofObj X).triangEnvelope = (ObjectProperty.ofObj Y).triangEnvelope := by
  apply le_antisymm
  · refine ((ObjectProperty.ofObj X).triangEnvelope_le_iff
      (Q := (ObjectProperty.ofObj Y).triangEnvelope)).2 ?_
    refine (ObjectProperty.ofObj_le_iff X (ObjectProperty.ofObj Y).triangEnvelope).2 ?_
    intro i
    obtain ⟨j, ⟨e⟩⟩ := hXY i
    exact (ObjectProperty.ofObj Y).triangEnvelope.prop_of_iso e.symm
      ((ObjectProperty.ofObj Y).le_triangEnvelope _ (ObjectProperty.ofObj_apply Y j))
  · refine ((ObjectProperty.ofObj Y).triangEnvelope_le_iff
      (Q := (ObjectProperty.ofObj X).triangEnvelope)).2 ?_
    refine (ObjectProperty.ofObj_le_iff Y (ObjectProperty.ofObj X).triangEnvelope).2 ?_
    intro j
    obtain ⟨i, ⟨e⟩⟩ := hYX j
    exact (ObjectProperty.ofObj X).triangEnvelope.prop_of_iso e.symm
      ((ObjectProperty.ofObj X).le_triangEnvelope _ (ObjectProperty.ofObj_apply X i))

/-- Finite direct sums with exactly the same isomorphism classes of
summands are classical generators simultaneously. -/
theorem same_summands_generates_iff {I J : Type*}
    [Finite I] [Finite J] [Nonempty I] [Nonempty J]
    (X : I → C) (Y : J → C) [HasBiproduct X] [HasBiproduct Y]
    (hXY : ∀ i, ∃ j, Nonempty (X i ≅ Y j))
    (hYX : ∀ j, ∃ i, Nonempty (Y j ≅ X i)) :
    (ObjectProperty.singleton (⨁ X)).IsClassicalTriangulatedGenerator ↔
      (ObjectProperty.singleton (⨁ Y)).IsClassicalTriangulatedGenerator := by
  unfold ObjectProperty.IsClassicalTriangulatedGenerator
  rw [biproduct_triangEnvelope_eq, biproduct_triangEnvelope_eq,
    same_summands_triangEnvelope X Y hXY hYX]

/-- A finite splitting before applying a functor that preserves those
biproducts determines the same generation criterion after applying it.
In particular, this transports ordinary sheaf splittings through the
degree-zero embedding into a derived category. -/
theorem same_summands_map_generates_iff
    {A : Type u₂} [Category.{v₂} A] [HasZeroMorphisms A]
    {I J : Type*} [Finite I] [Finite J] [Nonempty I] [Nonempty J]
    (F : A ⥤ C) [F.PreservesZeroMorphisms]
    (X : I → A) (Y : J → A) [HasBiproduct X] [HasBiproduct Y]
    [PreservesBiproduct X F] [PreservesBiproduct Y F]
    {M N : A} (eM : M ≅ ⨁ X) (eN : N ≅ ⨁ Y)
    (hXY : ∀ i, ∃ j, Nonempty (X i ≅ Y j))
    (hYX : ∀ j, ∃ i, Nonempty (Y j ≅ X i)) :
    (ObjectProperty.singleton (F.obj M)).IsClassicalTriangulatedGenerator ↔
      (ObjectProperty.singleton (F.obj N)).IsClassicalTriangulatedGenerator := by
  rw [classicalGenerator_iff_of_iso (F.mapIso eM ≪≫ F.mapBiproduct X),
    classicalGenerator_iff_of_iso (F.mapIso eN ≪≫ F.mapBiproduct Y)]
  apply same_summands_generates_iff (F.obj ∘ X) (F.obj ∘ Y)
  · intro i
    obtain ⟨j, ⟨e⟩⟩ := hXY i
    exact ⟨j, ⟨F.mapIso e⟩⟩
  · intro j
    obtain ⟨i, ⟨e⟩⟩ := hYX j
    exact ⟨i, ⟨F.mapIso e⟩⟩

/-- A classical generator has no nonzero left-orthogonal object. The
hypothesis tests every shift, as required for the full derived Hom complex. -/
theorem isZero_of_classicalGenerator_of_shiftHom_eq_zero (G X : C)
    (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator)
    (h : ∀ n : ℤ, ∀ f : X⟦n⟧ ⟶ G, f = 0) : IsZero X := by
  let Q := ((ObjectProperty.singleton X).shiftClosure ℤ).rightOrthogonal
  let := rightOrthogonal_stableUnderRetracts ((ObjectProperty.singleton X).shiftClosure ℤ)
  have hQG : Q G := by
    intro Z f hZ
    obtain ⟨Y, n, e, hY⟩ := hZ
    have hY' : X = Y := (ObjectProperty.singleton_iff X Y).1 hY
    subst Y
    rw [← cancel_epi e.inv, comp_zero]
    exact h n (e.inv ≫ f)
  have hclosure : (ObjectProperty.singleton G).triangEnvelope ≤ Q := by
    refine ((ObjectProperty.singleton G).triangEnvelope_le_iff (Q := Q)).2 ?_
    exact ObjectProperty.singleton_le_iff.mpr hQG
  have hQX : Q X := hclosure X (by rw [hG]; trivial)
  apply (IsZero.iff_id_eq_zero X).2
  exact hQX (𝟙 X) ((ObjectProperty.singleton X).le_shiftClosure _ (by simp))

/-- The form used by the necessity argument in Lemma 2.1. -/
theorem not_classicalGenerator_of_nonzero_leftOrthogonal (G X : C)
    (hX : ¬ IsZero X) (h : ∀ n : ℤ, ∀ f : X⟦n⟧ ⟶ G, f = 0) :
    ¬ (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator := by
  intro hG
  exact hX (isZero_of_classicalGenerator_of_shiftHom_eq_zero G X hG h)

end FiniteSummands

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CategoricalSource05

/-! ## Source module `ToricPower.DerivedNaturalTransformations`
Original SHA256: a02107286d8431232917bbc712efde1d32aab6c0007195851844e5293e5f4ab8.
The complete original source is retained in `third_party/categorical_sources`.
-/
section CategoricalSource06

/-!
# Natural splittings on bounded derived categories

A split natural transformation between exact functors of abelian categories
remains split after termwise application to complexes and localization at
quasi-isomorphisms. This file records that fact for Mathlib's derived category
and Tau Ceti's full subcategory of cohomologically bounded objects.

The final generator theorem has a genuine geometric input: a natural
retraction of the identity from the composite of two exact functors. It does
not assume that either functor is essentially surjective or fully faithful.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.NatTrans

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {F G H : A ⥤ B}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The termwise localized natural transformation preserves identities. -/
@[simp]
theorem mapDerivedCategory_id (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (𝟙 F : F ⟶ F).mapDerivedCategory = 𝟙 F.mapDerivedCategory := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  intro X
  simp only [mapDerivedCategory_app_Q_obj, mapHomologicalComplex_id,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  change F.mapDerivedCategoryFactors.hom.app X ≫ 𝟙 _ ≫
    F.mapDerivedCategoryFactors.inv.app X = 𝟙 _
  rw [Category.id_comp]
  exact F.mapDerivedCategoryFactors.hom_inv_id_app X

/-- The termwise localized natural transformation preserves composition. -/
@[simp]
theorem mapDerivedCategory_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    (τ ≫ σ).mapDerivedCategory = τ.mapDerivedCategory ≫ σ.mapDerivedCategory := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  intro X
  simp only [NatTrans.comp_app, mapDerivedCategory_app_Q_obj,
    mapHomologicalComplex_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]

/-- The canonical inclusion isomorphisms transport the actual derived
components to the underlying objects of the canonical bounded functors. -/
noncomputable def mapBoundedDerivedCategoryAmbient (τ : F ⟶ G) :
    F.mapBoundedDerivedCategory ⋙ DerivedCategory.Bounded.ι ⟶
      G.mapBoundedDerivedCategory ⋙ DerivedCategory.Bounded.ι :=
  F.mapBoundedDerivedCategoryCompιIso.hom ≫
    Functor.whiskerLeft DerivedCategory.Bounded.ι τ.mapDerivedCategory ≫
      G.mapBoundedDerivedCategoryCompιIso.inv

/-- Restriction of the actual derived natural transformation to bounded objects. -/
noncomputable def mapBoundedDerivedCategory (τ : F ⟶ G) :
    F.mapBoundedDerivedCategory ⟶ G.mapBoundedDerivedCategory where
  app X := ObjectProperty.homMk ((mapBoundedDerivedCategoryAmbient τ).app X)
  naturality {_ _} f := ObjectProperty.hom_ext _
    ((mapBoundedDerivedCategoryAmbient τ).naturality f)

/-- The bounded restriction has exactly the original derived components,
transported by the canonical inclusion isomorphisms. -/
@[simp]
theorem mapBoundedDerivedCategory_app_hom (τ : F ⟶ G)
    (X : DerivedCategory.Bounded A) :
    (τ.mapBoundedDerivedCategory.app X).hom =
      (mapBoundedDerivedCategoryAmbient τ).app X := rfl

@[simp]
theorem mapBoundedDerivedCategory_id (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (𝟙 F : F ⟶ F).mapBoundedDerivedCategory = 𝟙 F.mapBoundedDerivedCategory := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext _
  simp only [NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom,
    mapBoundedDerivedCategory_app_hom, mapBoundedDerivedCategoryAmbient,
    NatTrans.comp_app, Functor.whiskerLeft_app, mapDerivedCategory_id,
    Category.id_comp, Iso.hom_inv_id_app]

@[simp]
theorem mapBoundedDerivedCategory_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    (τ ≫ σ).mapBoundedDerivedCategory =
      τ.mapBoundedDerivedCategory ≫ σ.mapBoundedDerivedCategory := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext _
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    mapBoundedDerivedCategory_app_hom, mapBoundedDerivedCategoryAmbient,
    NatTrans.comp_app, Functor.whiskerLeft_app, mapDerivedCategory_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc]

end CategoryTheory.NatTrans

namespace ToricPower

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (U : B ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (η : 𝟭 B ⟶ U ⋙ F) (π : U ⋙ F ⟶ 𝟭 B)

/-- The natural inclusion obtained by deriving a split unit. -/
noncomputable def boundedDerivedSplitInclusion :
    𝟭 (DerivedCategory.Bounded B) ⟶
      U.mapBoundedDerivedCategory ⋙ F.mapBoundedDerivedCategory :=
  (Functor.mapBoundedDerivedCategoryIdIso (A := B)).inv ≫
    η.mapBoundedDerivedCategory ≫
    (Functor.mapBoundedDerivedCategoryCompIso U F).inv

/-- The natural projection obtained by deriving a split unit. -/
noncomputable def boundedDerivedSplitProjection :
    U.mapBoundedDerivedCategory ⋙ F.mapBoundedDerivedCategory ⟶
      𝟭 (DerivedCategory.Bounded B) :=
  (Functor.mapBoundedDerivedCategoryCompIso U F).hom ≫
    π.mapBoundedDerivedCategory ≫
    (Functor.mapBoundedDerivedCategoryIdIso (A := B)).hom

/-- Localization and bounded restriction preserve the splitting equation. -/
theorem boundedDerivedSplit_retract (hηπ : η ≫ π = 𝟙 (𝟭 B)) :
    boundedDerivedSplitInclusion F U η ≫ boundedDerivedSplitProjection F U π =
      𝟙 (𝟭 (DerivedCategory.Bounded B)) := by
  simp only [boundedDerivedSplitInclusion, boundedDerivedSplitProjection,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc η.mapBoundedDerivedCategory,
    ← NatTrans.mapBoundedDerivedCategory_comp, hηπ,
    NatTrans.mapBoundedDerivedCategory_id, Category.id_comp, Iso.inv_hom_id]

/-- An exact functor whose composite with an exact functor has a naturally
split unit sends every classical generator of the bounded derived category
to a classical generator of the bounded derived category. -/
theorem boundedDerived_generator_of_splitUnit (hηπ : η ≫ π = 𝟙 (𝟭 B))
    (G : DerivedCategory.Bounded A)
    (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator) :
    (ObjectProperty.singleton (F.mapBoundedDerivedCategory.obj G)).IsClassicalTriangulatedGenerator := by
  exact obj_classicalGenerator_of_splitUnit F.mapBoundedDerivedCategory
    U.mapBoundedDerivedCategory (boundedDerivedSplitInclusion F U η)
    (boundedDerivedSplitProjection F U π) (boundedDerivedSplit_retract F U η π hηπ) G hG

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CategoricalSource06

/-! ## Source module `ToricPower.BoundedSplitTransfer`
Original SHA256: 998491ba30b891756f9e793607e234371e345ce20b4bf4c3589ba8f1cb6e483a.
The complete original source is retained in `third_party/categorical_sources`.
-/
section CategoricalSource07

/-!
# Bounded generator transfer from an additive split unit

Only the pushforward functor must be exact. The auxiliary functor is applied
termwise to a genuinely bounded representative, and is never asserted to
descend to the derived category. Its natural split unit nevertheless gives
the required retract after applying the exact functor and localizing.

This removes a flatness requirement from the categorical step in the toric
argument. The remaining input is an actual natural splitting on coherent
sheaves, not a hypothesized statement about generation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (U : B ⥤ A) [U.Additive]
  (η : 𝟭 B ⟶ U ⋙ F) (π : U ⋙ F ⟶ 𝟭 B)
  (hηπ : η ≫ π = 𝟙 (𝟭 B))

include U η π hηπ

/-- A split unit gives a literal termwise retract of complexes. Exactness
of the auxiliary functor is unnecessary for this construction. -/
def termwiseSplitRetract (K : CochainComplex B ℤ) :
    Retract K ((F.mapHomologicalComplex (.up ℤ)).obj
      ((U.mapHomologicalComplex (.up ℤ)).obj K)) where
  i :=
    { f := fun n => η.app (K.X n)
      comm' := fun i j _ => by
        change η.app (K.X i) ≫ F.map (U.map (K.d i j)) = K.d i j ≫ η.app (K.X j)
        exact (η.naturality (K.d i j)).symm }
  r :=
    { f := fun n => π.app (K.X n)
      comm' := fun i j _ => by
        change π.app (K.X i) ≫ K.d i j = F.map (U.map (K.d i j)) ≫ π.app (K.X j)
        exact (π.naturality (K.d i j)).symm }
  retract := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact NatTrans.congr_app hηπ (K.X n)

/-- Every bounded target is a retract of the derived image of a bounded
source. Strictly bounded representatives ensure that termwise application
of the auxiliary functor remains bounded. -/
theorem boundedDerived_retracts_of_additiveSplitUnit
    (Y : DerivedCategory.Bounded B) :
    ∃ X : DerivedCategory.Bounded A,
      Nonempty (Retract Y (F.mapBoundedDerivedCategory.obj X)) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Y.property
  letI := ha
  letI := hb
  obtain ⟨K, hKa, hKb, ⟨eK⟩⟩ :=
    Y.obj.exists_iso_Q_obj_of_isGE_of_isLE a b
  letI := hKa
  letI := hKb
  let L : CochainComplex A ℤ := (U.mapHomologicalComplex (.up ℤ)).obj K
  have hLa : L.IsStrictlyGE a := by dsimp only [L]; infer_instance
  have hLb : L.IsStrictlyLE b := by dsimp only [L]; infer_instance
  letI := hLa
  letI := hLb
  let X : DerivedCategory.Bounded A :=
    ⟨DerivedCategory.Q.obj L,
      ⟨⟨a, (DerivedCategory.isGE_Q_obj_iff L a).2 inferInstance⟩,
        ⟨b, (DerivedCategory.isLE_Q_obj_iff L b).2 inferInstance⟩⟩⟩
  let eF : (F.mapBoundedDerivedCategory.obj X).obj ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L) :=
    F.mapBoundedDerivedCategoryCompιIso.app X ≪≫ F.mapDerivedCategoryFactors.app L
  let r : Retract Y.obj (F.mapBoundedDerivedCategory.obj X).obj :=
    (Retract.ofIso eK).trans
      (((termwiseSplitRetract F U η π hηπ K).map DerivedCategory.Q).trans
        (Retract.ofIso eF.symm))
  refine ⟨X, ⟨{
    i := ObjectProperty.homMk r.i
    r := ObjectProperty.homMk r.r
    retract := ?_ }⟩⟩
  exact ObjectProperty.hom_ext _ r.retract

/-- An exact functor with a naturally split additive lift sends every
classical generator of the bounded derived category to a generator. -/
theorem boundedDerived_generator_of_additiveSplitUnit
    (G : DerivedCategory.Bounded A)
    (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator) :
    (ObjectProperty.singleton (F.mapBoundedDerivedCategory.obj G)).IsClassicalTriangulatedGenerator := by
  exact obj_classicalGenerator_of_retracts F.mapBoundedDerivedCategory G hG
    (boundedDerived_retracts_of_additiveSplitUnit F U η π hηπ)

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CategoricalSource07

/-! ## Source module `ToricPower.VectorDerivedDetection`
Original SHA256: 7d68e53e45aecf328a60f23d404e960d35341edd0e919922413641069332ee30.
The complete original source is retained in `third_party/categorical_sources`.
-/
section CategoricalSource08

/-!
# Nonvanishing of derived Hom over a field

The final linear-algebra step in Proposition 3.2 is valid for arbitrary
unbounded complexes and arbitrary-dimensional vector spaces. We prove it
using actual homology objects and actual retracts in the category of
complexes, followed by Mathlib's localization at quasi-isomorphisms.

No boundedness assumption and no postulated decomposition of complexes are
used: a single nonzero homology object on each side suffices.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe w v u

section HomologyRetract

variable {C : Type u} [Category.{v} C] [Abelian C]
  {I : Type*} [DecidableEq I] {c : ComplexShape I}

/-- A homology object that is both projective and injective is an actual
direct summand of the complex, placed in its original degree. -/
def singleHomologyRetract (K : HomologicalComplex C c) (n : I)
    [Projective (K.homology n)] [Injective (K.homology n)] :
    Retract ((HomologicalComplex.single C c n).obj (K.homology n)) K := by
  let s : K.homology n ⟶ K.cycles n :=
    Projective.factorThru (𝟙 (K.homology n)) (K.homologyπ n)
  let t : K.X n ⟶ K.homology n :=
    Injective.factorThru (K.homologyπ n) (K.iCycles n)
  have hs : s ≫ K.homologyπ n = 𝟙 (K.homology n) := by simp [s]
  have ht : K.iCycles n ≫ t = K.homologyπ n := by simp [t]
  let inc := HomologicalComplex.mkHomFromSingle (s ≫ K.iCycles n)
    (fun j _ => by simp only [Category.assoc, HomologicalComplex.iCycles_d, comp_zero])
  let pr := HomologicalComplex.mkHomToSingle t (fun j _ => by
    rw [← K.toCycles_i j n, Category.assoc, ht, K.toCycles_comp_homologyπ])
  refine ⟨inc, pr, ?_⟩
  apply HomologicalComplex.from_single_hom_ext
  simp only [inc, pr, HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.mkHomToSingle_f, HomologicalComplex.id_f, Category.assoc,
    reassoc_of% ht, reassoc_of% hs, Category.id_comp, Iso.hom_inv_id]

variable [HasDerivedCategory.{w} C]

/-- The same splitting after localization is a retract of the genuine
derived degree-zero construction, shifted to the specified degree. -/
def derivedHomologyRetract (K : CochainComplex C ℤ) (n : ℤ)
    [Projective (K.homology n)] [Injective (K.homology n)] :
    Retract ((DerivedCategory.singleFunctor C n).obj (K.homology n))
      (DerivedCategory.Q.obj K) :=
  (singleHomologyRetract K n).map DerivedCategory.Q

/-- A nonzero object represented by a complex has nonzero homology in some
degree; an acyclic complex becomes zero in the actual localization. -/
theorem exists_nonzero_homology_of_nonzero_Q (K : CochainComplex C ℤ)
    (hK : ¬ IsZero (DerivedCategory.Q.obj K)) :
    ∃ n : ℤ, ¬ IsZero (K.homology n) := by
  by_contra! h
  let f : K ⟶ (0 : CochainComplex C ℤ) := 0
  have hf : QuasiIso f := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (h n).isIso
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map_isZero (isZero_zero _)) _
  letI := hf
  exact hK ((asIso (DerivedCategory.Q.map f)).isZero_iff.mpr
    (DerivedCategory.Q.map_isZero (isZero_zero _)))

end HomologyRetract

section VectorSpaces

variable {k : Type u} [Field k]

local instance vectorProjective (M : ModuleCat.{v} k) : Projective M := by
  exact ModuleCat.projective_of_free (Module.Basis.ofVectorSpace k M)

local instance vectorInjective (M : ModuleCat.{v} k) : Injective M where
  factors g f m := by
    obtain ⟨r, hr⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp m))
    refine ⟨ModuleCat.ofHom (g.hom.comp r), ?_⟩
    apply ModuleCat.hom_ext
    change (g.hom.comp r).comp f.hom = g.hom
    rw [LinearMap.comp_assoc, hr, LinearMap.comp_id]

/-- Two nonzero vector spaces admit a nonzero linear map, without dimension
or cardinality restrictions. -/
theorem exists_nonzero_vector_map (M N : ModuleCat.{v} k)
    (hM : ¬ IsZero M) (hN : ¬ IsZero N) : ∃ f : M ⟶ N, f ≠ 0 := by
  letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp
    (fun h => hM (ModuleCat.isZero_iff_subsingleton.mpr h))
  letI : Nontrivial N := not_subsingleton_iff_nontrivial.mp
    (fun h => hN (ModuleCat.isZero_iff_subsingleton.mpr h))
  obtain ⟨φ, hφ⟩ := exists_ne (0 : M →ₗ[k] N)
  refine ⟨ModuleCat.ofHom φ, ?_⟩
  intro hz
  exact hφ (ModuleCat.hom_ext_iff.mp hz)

variable [HasDerivedCategory.{w} (ModuleCat.{v} k)]

/-- The derived Hom of two nonzero complexes of vector spaces is nonzero
in some degree, including when either complex is unbounded. -/
theorem exists_nonzero_shifted_map_Q
    (K L : CochainComplex (ModuleCat.{v} k) ℤ)
    (hK : ¬ IsZero (DerivedCategory.Q.obj K))
    (hL : ¬ IsZero (DerivedCategory.Q.obj L)) :
    ∃ d : ℤ, ∃ f : (DerivedCategory.Q.obj K)⟦d⟧ ⟶ DerivedCategory.Q.obj L, f ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_nonzero_homology_of_nonzero_Q K hK
  obtain ⟨m, hm⟩ := exists_nonzero_homology_of_nonzero_Q L hL
  obtain ⟨φ, hφ⟩ := exists_nonzero_vector_map (K.homology n) (L.homology m) hn hm
  let rK := derivedHomologyRetract K n
  let rL := derivedHomologyRetract L m
  let e := ((DerivedCategory.singleFunctors (ModuleCat.{v} k)).shiftIso
    (n - m) m n (by omega)).app (K.homology n)
  refine ⟨n - m, rK.r⟦n - m⟧' ≫ e.hom ≫
    (DerivedCategory.singleFunctor (ModuleCat.{v} k) m).map φ ≫ rL.i, ?_⟩
  intro hf
  apply hφ
  apply (DerivedCategory.singleFunctor (ModuleCat.{v} k) m).map_injective
  rw [Functor.map_zero]
  rw [← cancel_mono rL.i, zero_comp, ← cancel_epi e.hom, comp_zero,
    ← cancel_epi (rK.r⟦n - m⟧'), comp_zero]
  exact hf

/-- The invariant formulation in the actual unbounded derived category. -/
theorem exists_nonzero_shifted_map_of_nonzero
    (E A : DerivedCategory (ModuleCat.{v} k)) (hE : ¬ IsZero E) (hA : ¬ IsZero A) :
    ∃ d : ℤ, ∃ f : E⟦d⟧ ⟶ A, f ≠ 0 := by
  let K := DerivedCategory.Q.objPreimage E
  let L := DerivedCategory.Q.objPreimage A
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eL : DerivedCategory.Q.obj L ≅ A := DerivedCategory.Q.objObjPreimageIso A
  have hK : ¬ IsZero (DerivedCategory.Q.obj K) :=
    fun h => hE (eK.isZero_iff.mp h)
  have hL : ¬ IsZero (DerivedCategory.Q.obj L) :=
    fun h => hA (eL.isZero_iff.mp h)
  obtain ⟨d, f, hf⟩ := exists_nonzero_shifted_map_Q K L hK hL
  refine ⟨d, eK.inv⟦d⟧' ≫ f ≫ eL.hom, ?_⟩
  intro hg
  apply hf
  rw [← cancel_mono eL.hom, zero_comp, ← cancel_epi (eK.inv⟦d⟧'), comp_zero]
  exact hg

end VectorSpaces

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CategoricalSource08
