module

public import ToricPower.ModuleDirectSumComplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Literal unrestricted direct sums of module diagrams

The universal property is verified at every diagram object. The actual
summand inclusions and incidence maps are retained, rather than merely
identifying dimensions or cohomology groups.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped Classical

namespace ToricPower.ModuleDiagramSum

variable (R : Type) [CommRing R] {I C : Type} [SmallCategory C]
  (F : Discrete I ⥤ C ⥤ ModuleCat.{0} R)

/-- The full dependent finitely supported module at every object. -/
def diagram : C ⥤ ModuleCat.{0} R := F.flip ⋙ ModuleDirectSum.sumFunctor R

def inclusion (i : I) : F.obj ⟨i⟩ ⟶ diagram R F where
  app c := ModuleCat.ofHom (DFinsupp.lsingle (R := R)
    (M := fun j : I => ↑((F.obj ⟨j⟩).obj c)) i)
  naturality {c d} f :=
    (ModuleDirectSum.sumFunctor_map_inclusion R (F.flip.map f) i).symm

/-- The canonical cocone, with its genuine summand inclusions. -/
def cocone : Cocone F where
  pt := diagram R F
  ι := Discrete.natTrans (fun i => inclusion R F i.as)

/-- The coproduct property holds for arbitrary diagrams and index sets. -/
def isColimit : IsColimit (cocone R F) :=
  evaluationJointlyReflectsColimits _ (fun c =>
    ModuleDirectSum.sumCoconeIsColimit R (F ⋙ (evaluation C (ModuleCat.{0} R)).obj c))

def colimitIso : diagram R F ≅ colimit F :=
  (isColimit R F).coconePointUniqueUpToIso (colimit.isColimit F)

@[reassoc]
theorem inclusion_colimitIso (i : I) :
    inclusion R F i ≫ (colimitIso R F).hom = colimit.ι F ⟨i⟩ :=
  (isColimit R F).fac (colimit.cocone F) ⟨i⟩

end ToricPower.ModuleDiagramSum

end
