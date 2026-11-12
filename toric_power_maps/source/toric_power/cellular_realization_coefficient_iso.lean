module

public import ToricPower.CovariantCopowerLabelNaturality
public import ToricPower.ArrangementCellularCoefficientFunctor

/-!
# A natural coefficient comparison for the whole cellular realization

The canonical finite cellular comparison and the unrestricted copower
comparison combine into an isomorphism of actual functors. It retains
every input-diagram map, as well as every original cell incidence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

universe u v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type u} [Category.{0} B] [Preadditive B] [Linear k B]
  {D : Type v} [Category.{0} D] [Preadditive D] [Linear k D]
  [HasCoproducts.{0} B] [HasFiniteBiproducts B]
  [HasCoproducts.{0} D] [HasFiniteBiproducts D]
  (F : B ⥤ D) [F.Additive] [F.Linear k] [PreservesColimitsOfSize.{0,0} F]
  (Q : IncidenceObject A ⥤ B) (Q' : IncidenceObject A ⥤ D)
  (e : Q ⋙ F ≅ Q')

/-- The complete cellular realization commutes with the actual
coefficient functor and specified label isomorphism. -/
def cellularRealizationCoefficientIso :
    arrangementCellularRealization A k Q ⋙ F.mapHomologicalComplex (.up ℕ) ≅
      arrangementCellularRealization A k Q' :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Cellular.covariantCopowerFunctor k Q)
      (cellularCoefficientFunctorIso A k F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Cellular.covariantCopowerFunctorComparisonIso k F Q)
      (arrangementCellularCochainFunctor A k) ≪≫
    Functor.isoWhiskerRight (Cellular.covariantCopowerLabelFunctorIso k e)
      (arrangementCellularCochainFunctor A k)

end ToricPower.IntegralArrangement

end
