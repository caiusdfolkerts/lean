module

public import ToricPower.BoundedHomologicalComparison
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Full faithfulness on bounded complexes from single-object comparisons

The hypothesis concerns the actual maps on morphisms between sheaves in
all single degrees. Two finite truncation inductions extend these
bijections to all bounded objects. No unbounded full faithfulness is
asserted or used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace ToricPower

universe w v₁ v₂ u₁ u₂

section Generic

variable {C : Type u₁} [Category.{w} C] [Preadditive C]
  {D : Type u₂} [Category.{w} D] [Preadditive D]
  (F : C ⥤ D) [F.Additive]

/-- The actual map on covariant Hom groups, naturally in the target. -/
def preadditiveCoyonedaComparison (X : C) :
    preadditiveCoyoneda.obj (op X) ⟶ F ⋙ preadditiveCoyoneda.obj (op (F.obj X)) where
  app Y := AddCommGrpCat.ofHom F.mapAddHom
  naturality {Y Z} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    exact F.map_comp g f

end Generic

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w} D]
  (F : DerivedCategory C ⥤ DerivedCategory D) [F.Additive] [F.CommShift ℤ]
  [F.IsTriangulated]
  (singles : ∀ (X Y : C) (a b : ℤ), Function.Bijective
    (F.map : ((DerivedCategory.singleFunctor C a).obj X ⟶
      (DerivedCategory.singleFunctor C b).obj Y) → _))

include singles in
/-- Fixing a single source, the comparison holds for every bounded target. -/
theorem derivedHom_map_bijective_single_bounded (X : C) (a : ℤ)
    (Y : DerivedCategory C) (hY : (DerivedCategory.TStructure.t (C := C)).bounded Y) :
    Function.Bijective (F.map : ((DerivedCategory.singleFunctor C a).obj X ⟶ Y) → _) := by
  let H := preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor C a).obj X))
  let G := F ⋙ preadditiveCoyoneda.obj (op (F.obj ((DerivedCategory.singleFunctor C a).obj X)))
  let α := preadditiveCoyonedaComparison F ((DerivedCategory.singleFunctor C a).obj X)
  have h : IsIso (α.app Y) :=
    homologicalComparison_isIso_of_bounded H G α (fun Z b =>
      (ConcreteCategory.isIso_iff_bijective _).mpr (singles X Z a b)) Y hY
  exact (ConcreteCategory.isIso_iff_bijective (α.app Y)).mp h

include singles in
/-- The actual derived morphism map is bijective for every pair of
bounded complexes. -/
theorem derivedHom_map_bijective_bounded
    (X Y : DerivedCategory C)
    (hX : (DerivedCategory.TStructure.t (C := C)).bounded X)
    (hY : (DerivedCategory.TStructure.t (C := C)).bounded Y) :
    Function.Bijective (F.map : (X ⟶ Y) → _) := by
  let H := preadditiveYoneda.obj Y
  let G := F.op ⋙ preadditiveYoneda.obj (F.obj Y)
  let α := preadditiveYonedaMap F Y
  have h : IsIso (α.app (op X)) :=
    homologicalComparison_isIso_of_bounded_op H G α (fun Z a =>
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (derivedHom_map_bijective_single_bounded F singles Z a Y hY)) X hX
  exact (ConcreteCategory.isIso_iff_bijective (α.app (op X))).mp h

/-- The actual restriction to the bounded source is fully faithful.
The target remains the ordinary unbounded derived category. -/
def boundedDerivedFullyFaithfulOfSingles :
    (DerivedCategory.Bounded.ι (C := C) ⋙ F).FullyFaithful :=
  Classical.choice ((Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
    (fun X Y => (derivedHom_map_bijective_bounded F singles X.obj Y.obj X.property Y.property).comp
      ((Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Bounded.ι (C := C))).map_bijective X Y)))

end ToricPower

end
