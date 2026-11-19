module

public import ToricPower.CellularRealizationCoefficientIso
public import ToricPower.ArrangementCellularInclusions

/-! # Original cellular generators under the actual coefficient comparison -/

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
  (e : Q ⋙ F ≅ Q') (M : IncidenceObject A ⥤ ModuleCat k)

/-- The original objectwise comparison, with its three actual factors
exposed for map-level calculations. -/
def cellularRealizationCoefficientObjectIso :
    (F.mapHomologicalComplex (.up ℕ)).obj
      ((arrangementCellularRealization A k Q).obj M) ≅
        (arrangementCellularRealization A k Q').obj M :=
  cellularCoefficientComplexIso A k F (Cellular.covariantCopowerDiagram k Q M) ≪≫
    (arrangementCellularCochainFunctor A k).mapIso
      (Cellular.covariantCopowerCoefficientIso k M F Q) ≪≫
    (arrangementCellularCochainFunctor A k).mapIso
      ((Cellular.covariantCopowerLabelFunctor k M).mapIso e)

/-- Every original vector and cell inclusion is preserved by the
specified coefficient comparison. -/
@[reassoc]
theorem cellularRealizationCoefficientObjectIso_generator (q : ℕ)
    (d : NormalizedCell A q) (x : M.obj ⟨q,d⟩) :
    F.map (Cellular.vectorCopowerInclusion k (Q.obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
        arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k Q M) q d) ≫
      (cellularRealizationCoefficientObjectIso A k F Q Q' e M).hom.f q =
    e.hom.app ⟨q,d⟩ ≫
      Cellular.vectorCopowerInclusion k (Q'.obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
        arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k Q' M) q d := by
  change F.map (_ ≫ _) ≫ (cellularCoefficientTermIso A k F
      (Cellular.covariantCopowerDiagram k Q M) q).hom ≫
    ((arrangementCellularCochainFunctor A k).map
      (Cellular.covariantCopowerCoefficientIso k M F Q).hom).f q ≫
    ((arrangementCellularCochainFunctor A k).map
      ((Cellular.covariantCopowerLabelFunctor k M).mapIso e).hom).f q = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    cellularCoefficientTermIso_inclusion_assoc,
    cellularCochainMap_inclusion_assoc, cellularCochainMap_inclusion]
  change F.map (Cellular.vectorCopowerInclusion k (Q.obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x) ≫
    (Cellular.vectorCopowerComparisonIso k F (Q.obj ⟨q,d⟩) (M.obj ⟨q,d⟩)).hom ≫
      Cellular.vectorCopowerMapObject k (e.hom.app ⟨q,d⟩) (M.obj ⟨q,d⟩) ≫ _ = _
  rw [Cellular.vectorCopowerComparisonIso_inclusion_assoc,
    Cellular.vectorCopowerInclusion_mapObject_assoc]
  rfl

end ToricPower.IntegralArrangement

end
