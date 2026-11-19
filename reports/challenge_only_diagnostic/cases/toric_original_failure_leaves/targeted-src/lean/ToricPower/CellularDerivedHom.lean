module

public import ToricPower.CellularHomDiagram
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# The actual bounded-below derived Hom diagram

The ordinary Hom-diagram functor is derived in the actual category of
module diagrams. All incidence coherence survives the construction of
complexes and their localization. The domain is explicitly bounded below;
no unbounded extension or full-faithfulness claim is made here.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u v w w'

section DerivedHom

variable (R : Type u) [CommRing R]
  {C : Type u} [Category.{u} C]
  {A : Type v} [Category.{u} A] [Abelian A] [Linear R A]
  [EnoughInjectives A] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} (C ⥤ ModuleCat.{u} R)]
  (P : Cᵒᵖ ⥤ A)

/-- The canonical bounded-below right-derived Hom diagram. This is a
functor into the derived category of actual module diagrams. -/
def labelRHomPlus :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus (C ⥤ ModuleCat.{u} R) :=
  (homDiagram R P).rightDerivedFunctorPlus

instance : (labelRHomPlus R P).CommShift ℤ := by
  unfold labelRHomPlus
  infer_instance

instance : (labelRHomPlus R P).IsTriangulated := by
  unfold labelRHomPlus
  infer_instance

/-- The actual comparison from termwise Hom diagrams to their derived
Hom object. It is supplied by Mathlib's localization universal property. -/
def labelRHomPlusUnit :
    (homDiagram R P).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ labelRHomPlus R P :=
  (homDiagram R P).rightDerivedFunctorPlusUnit

/-- On a bounded-below complex of actual injective objects, the derived
diagram is the literal complex `c ↦ Hom(P(c), Kⁿ)` with its ordinary
postcomposition differential. -/
def labelRHomPlusOnInjectiveComplex
    (K : CochainComplex.Plus (InjectiveObject A)) :
    (labelRHomPlus R P).obj
        (DerivedCategory.Plus.Q.obj ((InjectiveObject.ι A).mapCochainComplexPlus.obj K)) ≅
      DerivedCategory.Plus.Q.obj
        ((homDiagram R P).mapCochainComplexPlus.obj
          ((InjectiveObject.ι A).mapCochainComplexPlus.obj K)) :=
  (asIso ((homDiagram R P).rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι A).mapCochainComplexPlus.obj K))).symm

/-- A literal label transformation induces the contravariant map between
the actual derived Hom-diagram functors. -/
def labelRHomPlusPrecompose {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) :
    labelRHomPlus R Q ⟶ labelRHomPlus R P :=
  (homDiagramPrecompose R α).rightDerivedFunctorPlus

end DerivedHom

end ToricPower.Cellular

end
