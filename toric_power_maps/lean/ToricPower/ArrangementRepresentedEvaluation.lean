module

public import ToricPower.ArrangementCellularInclusions
public import ToricPower.CovariantRepresentableSource

/-!
# Literal cellular generators of represented tensor evaluation

The full coefficient transformation is passed through the original
cellular functor. Its generator formula retains the actual cell
inclusion, original free incidence generator and original inverse-label
map. This is the coordinate comparison used for a canonical top quotient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower.IntegralArrangement

universe u

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type u} [Category.{0} B] [Preadditive B] [Linear k B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear k B]
  [HasCoproducts.{0} B] [HasFiniteBiproducts B]
  (Q R : IncidenceObject A ⥤ B) (c : IncidenceObject A)
  [PreservesColimitsOfSize.{0,0} ((tensoringRight B).obj (R.obj c))]

local notation "P" => Cellular.covariantCopowerDiagram k Q (Cellular.representable k c)
local notation "T" => Cellular.covariantTensorDiagram Q R
local notation "F" => Functor.obj (tensoringRight B) (R.obj c)

/-- The full actual cellular evaluation map, including its differential. -/
def cellularRepresentedTensorEvaluation :
    ((F).mapHomologicalComplex (.up ℕ)).obj
        ((arrangementCellularRealization A k Q).obj (Cellular.representable k c)) ⟶
      arrangementCellularCochainComplex A k T :=
  (cellularCoefficientComplexIso A k F P).hom ≫
    (arrangementCellularCochainFunctor A k).map
      (Cellular.representedTensorEvaluationDiagram k Q R c)

/-- Each original cell/incidence generator is evaluated by its literal
inverse-label map, before the final top quotient is applied. -/
@[reassoc]
theorem cellularRepresentedTensorEvaluation_generator
    (q : ℕ) (d : NormalizedCell A q) (f : c ⟶ (⟨q,d⟩ : IncidenceObject A)) :
    (Cellular.vectorCopowerInclusion k (Q.obj ⟨q,d⟩)
        ((Cellular.representable k c).obj ⟨q,d⟩) (ModuleCat.freeMk f) ≫
      arrangementCellularCochainInclusion A k P q d) ▷ R.obj c ≫
        (cellularRepresentedTensorEvaluation A k Q R c).f q =
      Q.obj ⟨q,d⟩ ◁ R.map f ≫
        arrangementCellularCochainInclusion A k T q d := by
  change ((Cellular.vectorCopowerInclusion k (Q.obj ⟨q,d⟩)
      ((Cellular.representable k c).obj ⟨q,d⟩) (ModuleCat.freeMk f) ≫
        arrangementCellularCochainInclusion A k P q d) ▷ R.obj c) ≫
      (cellularCoefficientTermIso A k F P q).hom ≫
        ((arrangementCellularCochainFunctor A k).map
          (Cellular.representedTensorEvaluationDiagram k Q R c)).f q = _
  rw [comp_whiskerRight, Category.assoc]
  have comparison := cellularCoefficientTermIso_inclusion A k F P q d
  change arrangementCellularCochainInclusion A k P q d ▷ R.obj c ≫
      (cellularCoefficientTermIso A k F P q).hom =
        arrangementCellularCochainInclusion A k (P ⋙ F) q d at comparison
  rw [← Category.assoc (arrangementCellularCochainInclusion A k P q d ▷ R.obj c),
    comparison, cellularCochainMap_inclusion, ← Category.assoc]
  exact congrArg (fun g => g ≫ arrangementCellularCochainInclusion A k T q d)
    (Cellular.representedTensorEvaluation_generator k Q R c ⟨q,d⟩ f)

end ToricPower.IntegralArrangement

end
