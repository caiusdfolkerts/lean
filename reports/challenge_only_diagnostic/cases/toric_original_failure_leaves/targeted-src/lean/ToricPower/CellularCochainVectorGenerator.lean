module

public import ToricPower.ArrangementCellularInclusions
public import ToricPower.CellularCovariantLabels
public import ToricPower.CellularFoundations

/-! # Actual cellular vector generators under coefficient maps

These formulas retain the original cell inclusion and the original
copower vector. They apply to arbitrary, unrestricted vector diagrams.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

universe v
variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type v} [Category.{0} B] [Preadditive B] [Linear k B]
  [HasCoproducts.{0} B] [HasFiniteBiproducts B]
  (Q : IncidenceObject A ⥤ B)

/-- An actual coefficient transformation changes precisely the original
copower vector in each cell. -/
@[reassoc]
theorem cellularVectorGenerator_map
    {M M' : IncidenceObject A ⥤ ModuleCat k} (f : M ⟶ M')
    (q : ℕ) (c : NormalizedCell A q) (x : M.obj ⟨q,c⟩) :
    (Cellular.vectorCopowerInclusion k (Q.obj ⟨q,c⟩) (M.obj ⟨q,c⟩) x ≫
      arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k Q M) q c) ≫
      ((arrangementCellularRealization A k Q).map f).f q =
    Cellular.vectorCopowerInclusion k (Q.obj ⟨q,c⟩) (M'.obj ⟨q,c⟩) (f.app ⟨q,c⟩ x) ≫
      arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k Q M') q c := by
  change (_ ≫ _) ≫ ((arrangementCellularCochainFunctor A k).map
    (Cellular.covariantCopowerMap k Q f)).f q = _
  rw [Category.assoc, cellularCochainMap_inclusion]
  change _ ≫ (Cellular.vectorCopowerFunctor k (Q.obj ⟨q,c⟩)).map (f.app ⟨q,c⟩) ≫ _ = _
  rw [Cellular.vectorCopowerInclusion_map_assoc]

/-- The identity vector in the genuine representable goes to exactly
the specified coefficient vector. -/
@[reassoc]
theorem cellularVectorGenerator_fromValue
    (M : IncidenceObject A ⥤ ModuleCat k)
    (q : ℕ) (c : NormalizedCell A q) (x : M.obj ⟨q,c⟩) :
    (Cellular.vectorCopowerInclusion k (Q.obj ⟨q,c⟩)
      ((Cellular.representable k (⟨q,c⟩ : IncidenceObject A)).obj ⟨q,c⟩)
      (ModuleCat.freeMk (𝟙 (⟨q,c⟩ : IncidenceObject A))) ≫
      arrangementCellularCochainInclusion A k
        (Cellular.covariantCopowerDiagram k Q (Cellular.representable k ⟨q,c⟩)) q c) ≫
      ((arrangementCellularRealization A k Q).map (Cellular.fromValue k M ⟨q,c⟩ x)).f q =
    Cellular.vectorCopowerInclusion k (Q.obj ⟨q,c⟩) (M.obj ⟨q,c⟩) x ≫
      arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k Q M) q c := by
  rw [cellularVectorGenerator_map, Cellular.fromValue_app_freeMk, M.map_id,
    ModuleCat.id_apply]

end ToricPower.IntegralArrangement

end
