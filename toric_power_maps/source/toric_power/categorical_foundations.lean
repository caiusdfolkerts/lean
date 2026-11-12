module

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

/-! ## Source module `TauCeti.Algebra.Homology.DerivedCategory.Bounded.Basic`
Original SHA256: 0be2c3b4907a8c369eb903442907c4430c979ce66fd93cef6cd6a4438af7f0c3.
The complete original source is retained in `third_party/categorical_sources`.
-/
section CategoricalSource01

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Single objects and short exact triangles in the bounded derived category

The single functors into the derived category lift to its bounded subcategory in every degree.
A short exact sequence then gives a distinguished triangle of bounded single objects.

## References

* Mathlib's `Mathlib/Algebra/Homology/DerivedCategory/Plus.lean`, whose lift of the single
  functors to the bounded-below derived category supplies the pattern used here.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategory.Bounded

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The functor sending an object to a complex concentrated in degree `n`. -/
noncomputable abbrev singleFunctor (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (n : ℤ) : A ⥤ DerivedCategory.Bounded A :=
  (DerivedCategory.TStructure.t (C := A)).bounded.lift (DerivedCategory.singleFunctor A n)
    (fun _ ↦ ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩)

/-- The single functors into the bounded derived category, with their shift compatibilities. -/
noncomputable def singleFunctors (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : SingleFunctors A (DerivedCategory.Bounded A) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors A) DerivedCategory.Bounded.ι
    (singleFunctor A) (fun _ ↦ Iso.refl _)

/-- The `n`th bounded single functor is `singleFunctor A n`. -/
@[simp] lemma singleFunctors_functor (n : ℤ) :
    (singleFunctors A).functor n = singleFunctor A n :=
  rfl

end DerivedCategory.Bounded

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {S : ShortComplex A}

/-- The triangle of bounded single objects associated with a short exact sequence. -/
@[implicit_reducible, simps! obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
noncomputable def _root_.CategoryTheory.ShortComplex.ShortExact.boundedSingleTriangle
    (hS : S.ShortExact) : Triangle (DerivedCategory.Bounded A) :=
  Triangle.mk ((DerivedCategory.Bounded.singleFunctor A 0).map S.f)
    ((DerivedCategory.Bounded.singleFunctor A 0).map S.g)
    ((DerivedCategory.TStructure.t (C := A)).bounded.fullyFaithfulι.preimage
      (hS.singleδ ≫ (DerivedCategory.Bounded.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₁)))

/-- Inclusion identifies the bounded single triangle with the derived single triangle. -/
@[simps!]
noncomputable def _root_.CategoryTheory.ShortComplex.ShortExact.boundedSingleTriangleιIso
    (hS : S.ShortExact) :
    DerivedCategory.Bounded.ι.mapTriangle.obj hS.boundedSingleTriangle ≅ hS.singleTriangle := by
  rw [Functor.mapTriangle_obj]
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [DerivedCategory.Bounded.singleFunctor, ObjectProperty.lift])
    (by simp [DerivedCategory.Bounded.singleFunctor, ObjectProperty.lift])
    (by simp [DerivedCategory.Bounded.singleFunctor, ObjectProperty.lift])

/-- The bounded single triangle of a short exact sequence is distinguished. -/
lemma _root_.CategoryTheory.ShortComplex.ShortExact.boundedSingleTriangle_distinguished
    (hS : S.ShortExact) :
    hS.boundedSingleTriangle ∈ distTriang (DerivedCategory.Bounded A) := by
  rw [← DerivedCategory.Bounded.ι.map_distinguished_iff, Functor.mapTriangle_obj]
  exact isomorphic_distinguished _ hS.singleTriangle_distinguished _
    hS.boundedSingleTriangleιIso

end TauCeti


-- Close scopes implicitly ended by the original source EOF.
end
end CategoricalSource01

/-! ## Source module `TauCeti.Algebra.Homology.DerivedCategory.Equivalence`
Original SHA256: ba0ed0ef49aa2864913d9b06252e82c6068ee1e14b53e4e56684c2ea802e0bdd.
The complete original source is retained in `third_party/categorical_sources`.
-/
section CategoricalSource02

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Derived equivalences induced by additive equivalences

An additive equivalence of abelian categories induces an equivalence of their derived categories.
Its functor and inverse are Mathlib's actual termwise derived actions. The unit and counit
are the derived images of the original comparisons, composed with Mathlib's identity and
composition comparisons for derived functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.NatIso

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- An isomorphism of exact functors induces an isomorphism of their derived actions. -/
noncomputable def mapDerivedCategory {F G : A ⥤ B}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] (α : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ _ _ _
    (isoWhiskerRight (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)) DerivedCategory.Q)

end CategoryTheory.NatIso

namespace CategoryTheory.Equivalence

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (e : A ≌ B) [e.functor.Additive]

/-- An additive equivalence of abelian categories acts termwise on the derived categories. -/
noncomputable def mapDerivedCategory : DerivedCategory A ≌ DerivedCategory B :=
  Equivalence.mk e.functor.mapDerivedCategory e.inverse.mapDerivedCategory
    ((Functor.mapDerivedCategoryIdIso A).symm ≪≫ NatIso.mapDerivedCategory e.unitIso ≪≫
      (Functor.mapDerivedCategoryCompIso e.functor e.inverse).symm)
    (Functor.mapDerivedCategoryCompIso e.inverse e.functor ≪≫
      NatIso.mapDerivedCategory e.counitIso ≪≫ Functor.mapDerivedCategoryIdIso B)

/-- The functor of the induced equivalence is Mathlib's termwise derived action. -/
@[simp]
lemma mapDerivedCategory_functor :
    e.mapDerivedCategory.functor = e.functor.mapDerivedCategory := (rfl)

/-- The inverse of the induced equivalence is the termwise derived action of the inverse. -/
@[simp]
lemma mapDerivedCategory_inverse :
    e.mapDerivedCategory.inverse = e.inverse.mapDerivedCategory := (rfl)

noncomputable instance : e.mapDerivedCategory.functor.CommShift ℤ :=
  inferInstanceAs (e.functor.mapDerivedCategory.CommShift ℤ)

instance : e.mapDerivedCategory.functor.IsTriangulated :=
  inferInstanceAs (e.functor.mapDerivedCategory.IsTriangulated)

end CategoryTheory.Equivalence


-- Close scopes implicitly ended by the original source EOF.
end
end CategoricalSource02

/-! ## Source module `TauCeti.CategoryTheory.ObjectProperty`
Original SHA256: e66947d82ce31732a5d46d900bb580e3bd101321a73dba99154cc14cdf2f7753.
The complete original source is retained in `third_party/categorical_sources`.
-/
section CategoricalSource03

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Object properties: transport along equivalences, and closure properties

This file contains general lemmas about object properties: transporting them along an
equivalence, comparing Mathlib's closure type classes with one another in the presence of a
zero object and of binary biproducts, smallness of full subcategories, and additivity of the
standard functors between full subcategories.

## Main declarations

* `CategoryTheory.ObjectProperty.inverseImage_functor_inverseImage_inverse`: pulling an
  isomorphism-invariant property backward along both functors of an equivalence recovers it.
* `CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_containsZero`: a property holding
  for a zero object and closed under binary products is closed under isomorphisms.
* `CategoryTheory.ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod`: for a replete
  property in a category with binary biproducts, closure under binary products only has to be
  checked on biproducts.
* `CategoryTheory.ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts`: a property closed
  under binary products holds for binary biproducts, with `X ⊞ Y` as the syntactic form of the
  conclusion.
* `CategoryTheory.ObjectProperty.essentiallySmall_of_ambient`: every property in an essentially
  small category is essentially small.
* `CategoryTheory.ObjectProperty.ιOfLE_additive`: the inclusion of a smaller property into a larger
  one is additive.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_additive` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_additive`: an additive equivalence
  restricts to an additive equivalence between corresponding full subcategories.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_comp_ι` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_comp_ι`: the restricted functors,
  followed by the inclusions, are the inclusions followed by the original functors.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_obj_obj`,
  `CategoryTheory.Equivalence.congrFullSubcategory_functor_map_hom` and their `inverse`
  counterparts: the restricted functors evaluated on objects and morphisms, for deriving the
  evaluation lemmas of any equivalence defined as a `congrFullSubcategory`.
-/

@[expose] public section

universe w u₁ v₁ u₂ v₂

namespace CategoryTheory

open Limits

namespace ObjectProperty

/-- Pulling an isomorphism-invariant object property backward along both functors of an
equivalence recovers the original property. -/
theorem inverseImage_functor_inverseImage_inverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.inverse).inverseImage e.functor = P := by
  ext X
  exact (P.prop_iff_of_iso (e.unitIso.app X)).symm

/-- **A property holding for a zero object and closed under binary products is closed under
isomorphisms.** An isomorphism `e : X ≅ Y` exhibits `Y` as a product of a zero object with `X`,
the two projections being the zero morphism and `e.inv`.

Mathlib's `CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts.closedUnderIsomorphisms` is
the same argument run on a terminal object, but it assumes closure under the empty limit, which
`CategoryTheory.ObjectProperty.ContainsZero` — the property for *one* zero object — does not
supply before repleteness is known. -/
theorem isClosedUnderIsomorphisms_of_containsZero {C : Type u₁} [Category.{v₁} C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨Z, hZ, hZP⟩ := P.exists_prop_of_containsZero
    let B : BinaryFan Z X := BinaryFan.mk (hZ.from_ Y) e.inv
    have hB : IsLimit B := BinaryFan.IsLimit.mk B (fun _ g => g ≫ e.hom)
      (fun _ _ => hZ.eq_of_tgt _ _)
      (fun _ _ => by simp [B])
      (fun _ _ _ _ hg => by simpa [B] using congrArg (fun k => k ≫ e.hom) hg)
    exact P.prop_of_isLimit_binaryFan hB hZP hX

/-- **For a replete property, closure under binary products only has to be checked on
biproducts**, since in a category with binary biproducts every binary product is one. -/
theorem isClosedUnderBinaryProducts_of_prop_biprod {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (h : ∀ X Y : C, P X → P Y → P (X ⊞ Y)) :
    P.IsClosedUnderBinaryProducts := by
  refine IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  refine P.prop_of_iso ?_ (h _ _ (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))
  exact (biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm

/-- **A property closed under binary products holds for binary biproducts.** In a category with
binary biproducts the biproduct is a binary product, so this is
`CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan` applied to
`CategoryTheory.Limits.BinaryBiproduct.isLimit`; naming it keeps the index of the conclusion
syntactically `X ⊞ Y`, which matters when the conclusion is the type index of a dependent
family. -/
theorem prop_biprod_of_isClosedUnderBinaryProducts {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] (P : ObjectProperty C) [P.IsClosedUnderBinaryProducts]
    {X Y : C} [HasBinaryBiproduct X Y] (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit X Y) hX hY

/-- Every object property in an essentially small category is essentially small. This supplies
the smallness instance for its full subcategory through Mathlib's object-property API. -/
instance essentiallySmall_of_ambient {C : Type u₁} [Category.{v₁} C]
    [CategoryTheory.EssentiallySmall.{w} C] (P : ObjectProperty C) :
    ObjectProperty.EssentiallySmall.{w} P :=
  ObjectProperty.EssentiallySmall.of_le.{w} (Q := (⊤ : ObjectProperty C)) le_top

/-- The inclusion of a smaller object property into a larger one is an additive functor: both
categories carry the addition of the ambient one. -/
instance ιOfLE_additive {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {P P' : ObjectProperty C} (h : P ≤ P') : (ObjectProperty.ιOfLE h).Additive where
  map_add := rfl

end ObjectProperty

namespace Equivalence

/-- The forward functor on corresponding full subcategories is the lift of the original functor. -/
theorem congrFullSubcategory_functor_eq_lift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).functor =
      Q.lift (P.ι ⋙ e.functor) (fun ⟨X, hX⟩ ↦ by rwa [← h] at hX) :=
  rfl

/-- The inverse functor on corresponding full subcategories is the lift of the original inverse. -/
theorem congrFullSubcategory_inverse_eq_lift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).inverse =
      P.lift (Q.ι ⋙ e.inverse) (fun ⟨Y, hY⟩ ↦ by
        rw [← h]
        exact Q.prop_of_iso (e.counitIso.app Y).symm hY) :=
  rfl

/-- The forward functor on corresponding full subcategories, followed by the inclusion, is the
inclusion followed by the original functor. -/
theorem congrFullSubcategory_functor_comp_ι
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).functor ⋙ Q.ι = P.ι ⋙ e.functor := by
  rw [congrFullSubcategory_functor_eq_lift]
  exact Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by
    simp only [Functor.comp_map, ObjectProperty.ι_obj_lift_map, eqToHom_refl, Category.id_comp,
      Category.comp_id]

/-- The inverse functor on corresponding full subcategories, followed by the inclusion, is the
inclusion followed by the original inverse. -/
theorem congrFullSubcategory_inverse_comp_ι
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).inverse ⋙ P.ι = Q.ι ⋙ e.inverse := by
  rw [congrFullSubcategory_inverse_eq_lift]
  exact Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by
    simp only [Functor.comp_map, ObjectProperty.ι_obj_lift_map, eqToHom_refl, Category.id_comp,
      Category.comp_id]

section Evaluation

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
  (e : C ≌ D) (h : Q.inverseImage e.functor = P)

/-- The forward functor on corresponding full subcategories acts on objects as the original
functor. Not a simp lemma: `congrFullSubcategory_functor` already unfolds the left-hand side. -/
theorem congrFullSubcategory_functor_obj_obj (X : P.FullSubcategory) :
    ((e.congrFullSubcategory h).functor.obj X).obj = e.functor.obj X.obj := by
  rw [congrFullSubcategory_functor_eq_lift, ObjectProperty.lift_obj_obj, Functor.comp_obj,
    ObjectProperty.ι_obj]

/-- The forward functor on corresponding full subcategories acts on morphisms as the original
functor, up to the identifications of `congrFullSubcategory_functor_obj_obj`. -/
theorem congrFullSubcategory_functor_map_hom {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((e.congrFullSubcategory h).functor.map f).hom =
      eqToHom (e.congrFullSubcategory_functor_obj_obj h X) ≫ e.functor.map f.hom ≫
        eqToHom (e.congrFullSubcategory_functor_obj_obj h Y).symm := by
  simpa only [Functor.comp_map, ObjectProperty.ι_map] using
    Functor.congr_hom (e.congrFullSubcategory_functor_comp_ι h) f

/-- The inverse functor on corresponding full subcategories acts on objects as the original
inverse. Not a simp lemma: `congrFullSubcategory_inverse` already unfolds the left-hand side. -/
theorem congrFullSubcategory_inverse_obj_obj (Y : Q.FullSubcategory) :
    ((e.congrFullSubcategory h).inverse.obj Y).obj = e.inverse.obj Y.obj := by
  rw [congrFullSubcategory_inverse_eq_lift, ObjectProperty.lift_obj_obj, Functor.comp_obj,
    ObjectProperty.ι_obj]

/-- The inverse functor on corresponding full subcategories acts on morphisms as the original
inverse, up to the identifications of `congrFullSubcategory_inverse_obj_obj`. -/
theorem congrFullSubcategory_inverse_map_hom {X Y : Q.FullSubcategory} (f : X ⟶ Y) :
    ((e.congrFullSubcategory h).inverse.map f).hom =
      eqToHom (e.congrFullSubcategory_inverse_obj_obj h X) ≫ e.inverse.map f.hom ≫
        eqToHom (e.congrFullSubcategory_inverse_obj_obj h Y).symm := by
  simpa only [Functor.comp_map, ObjectProperty.ι_map] using
    Functor.congr_hom (e.congrFullSubcategory_inverse_comp_ι h) f

end Evaluation

/-- The functor of an equivalence restricted to corresponding full subcategories is additive. -/
instance congrFullSubcategory_functor_additive
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) [e.functor.Additive] (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).functor.Additive := by
  rw [congrFullSubcategory_functor_eq_lift]
  infer_instance

/-- The inverse of an equivalence restricted to corresponding full subcategories is additive. -/
instance congrFullSubcategory_inverse_additive
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) [e.inverse.Additive] (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).inverse.Additive := by
  rw [congrFullSubcategory_inverse_eq_lift]
  infer_instance

end Equivalence

end CategoryTheory


-- Close scopes implicitly ended by the original source EOF.
end
end CategoricalSource03

/-! ## Source module `TauCeti.Algebra.Homology.DerivedCategory.Bounded.Functor`
Original SHA256: 33ae6506c8c7e0f9dc01a9c1180da4ea1239417925bb3fd5ed879dc13f7a30ab.
The complete original source is retained in `third_party/categorical_sources`.
-/
section CategoricalSource04

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Exact functors on bounded derived categories

An exact functor between abelian categories acts termwise on complexes and hence on bounded
derived categories. This restriction is triangulated and commutes with suspension. An additive
equivalence induces an equivalence of bounded derived categories with these same actual functors.
The single-object comparison characterizes their action on objects in any fixed degree.

The construction uses Mathlib's `Functor.mapDerivedCategory`, its factorization through termwise
mapping, and `Localization.equivalence`; no additional localization is constructed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Termwise exact functors preserve cohomological boundedness. -/
lemma bounded_mapDerivedCategory (X : DerivedCategory A)
    (hX : (DerivedCategory.TStructure.t (C := A)).bounded X) :
    (DerivedCategory.TStructure.t (C := B)).bounded (F.mapDerivedCategory.obj X) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hX
  obtain ⟨K, _, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE_of_isLE a b
  let L : CochainComplex B ℤ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have : L.IsGE a := by
    rw [CochainComplex.isGE_iff]
    exact fun i hi ↦ (K.exactAt_of_isGE a i hi).map F
  have : L.IsLE b := by
    rw [CochainComplex.isLE_iff]
    exact fun i hi ↦ (K.exactAt_of_isLE b i hi).map F
  exact (DerivedCategory.TStructure.t (C := B)).bounded.prop_of_iso
    (F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K).symm
    ⟨⟨a, by simpa only [Functor.comp_obj] using
      (DerivedCategory.isGE_Q_obj_iff L a).2 ‹L.IsGE a›⟩,
      ⟨b, by simpa only [Functor.comp_obj] using
        (DerivedCategory.isLE_Q_obj_iff L b).2 ‹L.IsLE b›⟩⟩

/-- The termwise action of an exact functor restricted to bounded derived categories. -/
noncomputable def mapBoundedDerivedCategory :
    DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded B :=
  (DerivedCategory.TStructure.t (C := B)).bounded.lift
    (DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory)
    (fun X ↦ F.bounded_mapDerivedCategory X.obj X.property)

/-- Inclusion identifies the bounded action with Mathlib's derived action. -/
noncomputable def mapBoundedDerivedCategoryCompιIso :
    F.mapBoundedDerivedCategory ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory :=
  (DerivedCategory.TStructure.t (C := B)).bounded.liftCompιIso _ _

noncomputable instance : F.mapBoundedDerivedCategory.CommShift ℤ := by
  exact Functor.CommShift.ofComp F.mapBoundedDerivedCategoryCompιIso ℤ

noncomputable instance : NatTrans.CommShift F.mapBoundedDerivedCategoryCompιIso.hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance : F.mapBoundedDerivedCategory.IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right F.mapBoundedDerivedCategoryCompιIso]
  infer_instance

/-- The bounded action commutes with the single-object embedding in every degree. -/
noncomputable def mapBoundedDerivedCategorySingleFunctor (n : ℤ) :
    TauCeti.DerivedCategory.Bounded.singleFunctor A n ⋙ F.mapBoundedDerivedCategory ≅
      F ⋙ TauCeti.DerivedCategory.Bounded.singleFunctor B n :=
  ((DerivedCategory.TStructure.t (C := B)).bounded.fullyFaithfulι.whiskeringRight _).preimageIso
    (F.mapDerivedCategorySingleFunctor n)

/-- The bounded derived action of the identity functor is the identity. -/
noncomputable def mapBoundedDerivedCategoryIdIso :
    (𝟭 A).mapBoundedDerivedCategory ≅ 𝟭 (DerivedCategory.Bounded A) :=
  ((DerivedCategory.TStructure.t (C := A)).bounded.fullyFaithfulι.whiskeringRight _).preimageIso
    ((𝟭 A).mapBoundedDerivedCategoryCompιIso ≪≫
      isoWhiskerLeft DerivedCategory.Bounded.ι (mapDerivedCategoryIdIso A) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The bounded derived action preserves composition of exact functors. -/
noncomputable def mapBoundedDerivedCategoryCompIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    F.mapBoundedDerivedCategory ⋙ G.mapBoundedDerivedCategory ≅
      (F ⋙ G).mapBoundedDerivedCategory :=
  ((DerivedCategory.TStructure.t (C := C)).bounded.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator .. ≪≫
      isoWhiskerLeft _ G.mapBoundedDerivedCategoryCompιIso ≪≫
      (Functor.associator ..).symm ≪≫
      isoWhiskerRight F.mapBoundedDerivedCategoryCompιIso _ ≪≫
      Functor.associator .. ≪≫
      isoWhiskerLeft DerivedCategory.Bounded.ι (mapDerivedCategoryCompIso F G) ≪≫
      (F ⋙ G).mapBoundedDerivedCategoryCompιIso.symm)

end CategoryTheory.Functor

namespace CategoryTheory.Equivalence

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (e : A ≌ B) [e.functor.Additive]

/-- Boundedness is the inverse image of boundedness under an additive derived equivalence. -/
lemma bounded_inverseImage_mapDerivedCategory :
    (DerivedCategory.TStructure.t (C := B)).bounded.inverseImage
        e.mapDerivedCategory.functor = (DerivedCategory.TStructure.t (C := A)).bounded := by
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, mapDerivedCategory_functor]
  constructor
  · intro hX
    have unit : X ≅ e.inverse.mapDerivedCategory.obj (e.functor.mapDerivedCategory.obj X) := by
      simpa only [mapDerivedCategory_functor, mapDerivedCategory_inverse,
        Functor.comp_obj, Functor.id_obj] using e.mapDerivedCategory.unitIso.app X
    exact (DerivedCategory.TStructure.t (C := A)).bounded.prop_of_iso unit.symm
      (e.inverse.bounded_mapDerivedCategory _ hX)
  · exact e.functor.bounded_mapDerivedCategory X

/-- An additive equivalence restricts to the cohomologically bounded objects. -/
noncomputable def mapBoundedDerivedCategory :
    DerivedCategory.Bounded A ≌ DerivedCategory.Bounded B :=
  e.mapDerivedCategory.congrFullSubcategory e.bounded_inverseImage_mapDerivedCategory

/-- The functor of the bounded equivalence is the actual termwise exact-functor action. -/
@[simp]
lemma mapBoundedDerivedCategory_functor :
    e.mapBoundedDerivedCategory.functor = e.functor.mapBoundedDerivedCategory := by
  simp only [mapBoundedDerivedCategory, congrFullSubcategory_functor_eq_lift,
    mapDerivedCategory_functor]
  rfl

/-- The inverse of the bounded equivalence is the termwise action of the original inverse. -/
@[simp]
lemma mapBoundedDerivedCategory_inverse :
    e.mapBoundedDerivedCategory.inverse = e.inverse.mapBoundedDerivedCategory := by
  simp only [mapBoundedDerivedCategory, congrFullSubcategory_inverse_eq_lift,
    mapDerivedCategory_inverse]
  rfl

/-- Inclusion identifies the bounded equivalence functor with its termwise derived action. -/
noncomputable def mapBoundedDerivedCategoryFunctorCompιIso :
    e.mapBoundedDerivedCategory.functor ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ e.functor.mapDerivedCategory :=
  isoWhiskerRight (eqToIso e.mapBoundedDerivedCategory_functor) _ ≪≫
    e.functor.mapBoundedDerivedCategoryCompιIso

noncomputable instance : e.mapBoundedDerivedCategory.functor.CommShift ℤ :=
  Functor.CommShift.ofComp (e.mapBoundedDerivedCategoryFunctorCompιIso) ℤ

noncomputable instance : NatTrans.CommShift (e.mapBoundedDerivedCategoryFunctorCompιIso).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance : e.mapBoundedDerivedCategory.functor.IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (e.mapBoundedDerivedCategoryFunctorCompιIso)]
  infer_instance

end CategoryTheory.Equivalence


-- Close scopes implicitly ended by the original source EOF.
end
end CategoricalSource04

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

/-- Restriction of the actual derived natural transformation to bounded objects. -/
noncomputable def mapBoundedDerivedCategory (τ : F ⟶ G) :
    F.mapBoundedDerivedCategory ⟶ G.mapBoundedDerivedCategory where
  app X := ObjectProperty.homMk (τ.mapDerivedCategory.app X.obj)
  naturality {_ _} f := ObjectProperty.hom_ext _ (τ.mapDerivedCategory.naturality f.hom)

/-- The bounded restriction has exactly the original derived components. -/
@[simp]
theorem mapBoundedDerivedCategory_app_hom (τ : F ⟶ G)
    (X : DerivedCategory.Bounded A) :
    (τ.mapBoundedDerivedCategory.app X).hom = τ.mapDerivedCategory.app X.obj := rfl

@[simp]
theorem mapBoundedDerivedCategory_id (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (𝟙 F : F ⟶ F).mapBoundedDerivedCategory = 𝟙 F.mapBoundedDerivedCategory := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext _
  exact NatTrans.congr_app (mapDerivedCategory_id F) X.obj

@[simp]
theorem mapBoundedDerivedCategory_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    (τ ≫ σ).mapBoundedDerivedCategory =
      τ.mapBoundedDerivedCategory ≫ σ.mapBoundedDerivedCategory := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext _
  exact NatTrans.congr_app (mapDerivedCategory_comp τ σ) X.obj

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
