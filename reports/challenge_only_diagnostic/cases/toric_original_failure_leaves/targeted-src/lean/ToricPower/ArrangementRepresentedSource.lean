module

public import ToricPower.ArrangementRepresentedEvaluation
public import ToricPower.CellularCoefficientTransformation

/-!
# Source naturality of the actual represented cellular evaluation

The original free incidence precomposition and the original inverse
Cartier label map give the same map of whole cellular complexes. This
establishes the source square before any top quotient is taken.
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
  (Q R : IncidenceObject A ⥤ B)
  [∀ c, PreservesColimitsOfSize.{0,0} ((tensoringRight B).obj (R.obj c))]

/-- Literal precomposition in the representable agrees with the
literal inverse-label action after the whole cellular construction. -/
@[reassoc]
theorem cellularRepresentedTensorEvaluation_source
    {c d : IncidenceObject A} (f : c ⟶ d) :
    (((tensoringRight B).obj (R.obj c)).mapHomologicalComplex (.up ℕ)).map
        ((arrangementCellularRealization A k Q).map
          (Cellular.representablePrecompose k f)) ≫
      cellularRepresentedTensorEvaluation A k Q R c =
    (((tensoringRight B).map (R.map f)).mapHomologicalComplex (.up ℕ)).app
        ((arrangementCellularRealization A k Q).obj (Cellular.representable k d)) ≫
      cellularRepresentedTensorEvaluation A k Q R d := by
  let α := Cellular.covariantCopowerMap k Q (Cellular.representablePrecompose k f)
  let P := Cellular.covariantCopowerDiagram k Q (Cellular.representable k d)
  let Pc := Cellular.covariantCopowerDiagram k Q (Cellular.representable k c)
  let Fc := (tensoringRight B).obj (R.obj c)
  let Fd := (tensoringRight B).obj (R.obj d)
  let γ := (tensoringRight B).map (R.map f)
  have coefficients :
      Functor.whiskerRight α Fc ≫ Cellular.representedTensorEvaluationDiagram k Q R c =
        Functor.whiskerLeft P γ ≫ Cellular.representedTensorEvaluationDiagram k Q R d := by
    apply NatTrans.ext
    funext e
    exact Cellular.representedTensorEvaluation_source k Q R f e
  change (Fc.mapHomologicalComplex (.up ℕ)).map
      ((arrangementCellularCochainFunctor A k).map α) ≫
        (cellularCoefficientComplexIso A k Fc Pc).hom ≫
          (arrangementCellularCochainFunctor A k).map
            (Cellular.representedTensorEvaluationDiagram k Q R c) =
    (γ.mapHomologicalComplex (.up ℕ)).app (arrangementCellularCochainComplex A k P) ≫
      (cellularCoefficientComplexIso A k Fd P).hom ≫
        (arrangementCellularCochainFunctor A k).map
          (Cellular.representedTensorEvaluationDiagram k Q R d)
  have source := cellularCoefficientComplexIso_natural A k Fc α
  have coefficient := cellularCoefficientComplexIso_transformation A k Fc Fd γ P
  calc
    _ = (cellularCoefficientComplexIso A k Fc P).hom ≫
        (arrangementCellularCochainFunctor A k).map (Functor.whiskerRight α Fc) ≫
        (arrangementCellularCochainFunctor A k).map
          (Cellular.representedTensorEvaluationDiagram k Q R c) := by
      simpa only [Category.assoc] using congrArg
        (fun g => g ≫ (arrangementCellularCochainFunctor A k).map
          (Cellular.representedTensorEvaluationDiagram k Q R c)) source
    _ = (cellularCoefficientComplexIso A k Fc P).hom ≫
        (arrangementCellularCochainFunctor A k).map (Functor.whiskerLeft P γ) ≫
        (arrangementCellularCochainFunctor A k).map
          (Cellular.representedTensorEvaluationDiagram k Q R d) := by
      rw [← Functor.map_comp, coefficients, Functor.map_comp]
    _ = _ := by
      simpa only [Category.assoc] using (congrArg
        (fun g => g ≫ (arrangementCellularCochainFunctor A k).map
          (Cellular.representedTensorEvaluationDiagram k Q R d)) coefficient).symm

end ToricPower.IntegralArrangement

end
