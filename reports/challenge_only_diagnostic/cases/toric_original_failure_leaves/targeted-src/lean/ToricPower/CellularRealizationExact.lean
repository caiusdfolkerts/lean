module

public import ToricPower.CellularRealizationColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Exactness of actual cellular realization in its coefficients

Vector copowers over a field preserve short exact sequences because
those sequences split. The finite cellular degree is a finite coproduct,
which is also a finite product. These original constructions therefore
preserve finite limits as well as colimits, for arbitrary diagrams and
arbitrary coefficient dimensions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k]
  {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Abelian B] [Linear k B]
  [HasColimitsOfSize.{u,u} B]

/-- Exactness is objectwise, using the actual unrestricted copowers. -/
instance covariantCopowerFunctor_preservesFiniteLimits (Q : C ⥤ B) :
    PreservesFiniteLimits (covariantCopowerFunctor k Q) := by
  apply preservesFiniteLimits_of_evaluation
  intro c
  change PreservesFiniteLimits
    (((evaluation C (ModuleCat.{u} k)).obj c) ⋙ vectorCopowerFunctor k (Q.obj c))
  infer_instance

end ToricPower.Cellular

namespace ToricPower.IntegralArrangement

universe v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type v} [Category.{0} B] [Abelian B] [Linear k B]
  [HasColimitsOfSize.{0,0} B] [HasFiniteBiproducts B]

instance cellularDegreeDiagram_preservesFiniteLimits (q : ℕ) :
    PreservesFiniteLimits (cellularDegreeDiagram A (B := B) q) := by
  apply preservesFiniteLimits_of_evaluation
  intro c
  change PreservesFiniteLimits
    ((evaluation (IncidenceObject A) B).obj ⟨q,c.as⟩)
  infer_instance

/-- The actual finite cellular cochain construction is exact, not only
its scalar coordinates or its homology. -/
instance arrangementCellularCochainFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (arrangementCellularCochainFunctor A k (B := B)) where
  preservesFiniteLimits J _ _ := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro q
    exact preservesLimitsOfShape_of_natIso (cellularDegreeCoproductIso A k q).symm

/-- Exactness holds for the whole actual cellular functor and therefore
for every actual degree evaluation used in finite signed totalization. -/
instance arrangementCellularRealization_preservesFiniteLimits
    (Q : IncidenceObject A ⥤ B) :
    PreservesFiniteLimits (arrangementCellularRealization A k Q) := by
  unfold arrangementCellularRealization
  infer_instance

end ToricPower.IntegralArrangement

end
