module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The actual termwise adjunction on complexes

An adjunction between functors preserving zero morphisms induces an
adjunction on actual homological complexes. The unit and counit are the
literal termwise unit and counit, and the triangle equations are checked
in every degree. This construction does not assume that either functor
preserves quasi-isomorphisms or that a derived adjunction already exists.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v' w

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
  {B : Type u'} [Category.{v'} B] [HasZeroMorphisms B]
  {F : A ⥤ B} {G : B ⥤ A}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  (adj : F ⊣ G) {I : Type w} (c : ComplexShape I)

/-- The original unit is a chain map by its actual naturality. -/
def complexAdjunctionUnit :
    𝟭 (HomologicalComplex A c) ⟶ F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c where
  app K :=
    { f := fun n => adj.unit.app (K.X n)
      comm' := fun i j _ => (adj.unit.naturality (K.d i j)).symm }
  naturality {_ _} f := by
    ext n
    exact adj.unit.naturality (f.f n)

/-- The original counit is a chain map by its actual naturality. -/
def complexAdjunctionCounit :
    G.mapHomologicalComplex c ⋙ F.mapHomologicalComplex c ⟶
      𝟭 (HomologicalComplex B c) where
  app K :=
    { f := fun n => adj.counit.app (K.X n)
      comm' := fun i j _ => (adj.counit.naturality (K.d i j)).symm }
  naturality {_ _} f := by
    ext n
    exact adj.counit.naturality (f.f n)

/-- The genuine adjunction on complexes, with the original triangle
identities checked degree by degree. -/
def complexAdjunction : F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit := complexAdjunctionUnit adj c
  counit := complexAdjunctionCounit adj c
  left_triangle_components K := by
    ext n
    exact adj.left_triangle_components (K.X n)
  right_triangle_components K := by
    ext n
    exact adj.right_triangle_components (K.X n)

@[simp]
theorem complexAdjunction_homEquiv_f
    (K : HomologicalComplex A c) (L : HomologicalComplex B c)
    (f : (F.mapHomologicalComplex c).obj K ⟶ L) (n : I) :
    ((complexAdjunction adj c).homEquiv K L f).f n =
      adj.homEquiv (K.X n) (L.X n) (f.f n) := rfl

@[simp]
theorem complexAdjunction_homEquiv_symm_f
    (K : HomologicalComplex A c) (L : HomologicalComplex B c)
    (f : K ⟶ (G.mapHomologicalComplex c).obj L) (n : I) :
    (((complexAdjunction adj c).homEquiv K L).symm f).f n =
      (adj.homEquiv (K.X n) (L.X n)).symm (f.f n) := rfl

end ToricPower

end
