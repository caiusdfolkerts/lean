module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The actual K-injective homotopy subcategory embeds in the derived category

The source is the right orthogonal to acyclic complexes in the genuine
homotopy category. Localization is fully faithful there, by the actual
calculus of fractions. The induced functor is triangulated.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace ToricPower

universe u v w
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

abbrev KInjectiveHomotopy :=
  ((HomotopyCategory.subcategoryAcyclic A).rightOrthogonal).FullSubcategory

abbrev kInjectiveHomotopyInclusion : KInjectiveHomotopy A ⥤ HomotopyCategory A (.up ℤ) :=
  ((HomotopyCategory.subcategoryAcyclic A).rightOrthogonal).ι

abbrev kInjectiveLocalization : KInjectiveHomotopy A ⥤ DerivedCategory A :=
  kInjectiveHomotopyInclusion A ⋙ DerivedCategory.Qh

theorem kInjectiveLocalization_map_bijective (X Y : KInjectiveHomotopy A) :
    Function.Bijective ((kInjectiveLocalization A).map : (X ⟶ Y) → _) := by
  have maps := Y.property.map_bijective_of_isTriangulated DerivedCategory.Qh X.obj
  constructor
  · intro f g same
    apply ObjectProperty.hom_ext
    exact maps.1 same
  · intro f
    obtain ⟨g, hg⟩ := maps.2 f
    exact ⟨ObjectProperty.homMk g, hg⟩

instance kInjectiveLocalization_full : (kInjectiveLocalization A).Full where
  map_surjective {X Y} := (kInjectiveLocalization_map_bijective A X Y).2

instance kInjectiveLocalization_faithful : (kInjectiveLocalization A).Faithful where
  map_injective {X Y} := (kInjectiveLocalization_map_bijective A X Y).1

end ToricPower
end
