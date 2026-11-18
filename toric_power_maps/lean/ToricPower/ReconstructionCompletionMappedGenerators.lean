module

public import ToricPower.CellularRealizationCoefficientGenerators
public import ToricPower.ReconstructionCompletionGeometricCellular

/-! # Detection by every original mapped cellular generator -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

universe u v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type u} [Category.{0} B] [Abelian B] [Linear k B]
  {D : Type v} [Category.{0} D] [Abelian D] [Linear k D]
  [HasCoproducts.{0} B] [HasFiniteBiproducts B]
  [HasCoproducts.{0} D] [HasFiniteBiproducts D]
  (F : B ⥤ D) [F.Additive] [F.Linear k] [PreservesColimitsOfSize.{0,0} F]
  (Q : IncidenceObject A ⥤ B) (M : IncidenceObject A ⥤ ModuleCat k)

local instance (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance : HasFiniteBiproducts Dᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts

private theorem mappedCellularTerm_hom_ext (P : IncidenceObject A ⥤ D)
    (q : ℕ) {Z : D} {f g : (arrangementCellularCochainComplex A k P).X q ⟶ Z}
    (same : ∀ d : NormalizedCell A q,
      arrangementCellularCochainInclusion A k P q d ≫ f =
        arrangementCellularCochainInclusion A k P q d ≫ g) : f = g := by
  apply Quiver.Hom.op_inj
  apply biproduct.hom_ext
  intro d
  exact congrArg Quiver.Hom.op (same d)

/-- Every original Hom vector and cell is retained after an actual
cocontinuous coefficient functor. These generators jointly detect maps. -/
theorem reconstruction_mapped_cellular_hom_ext (q : ℕ) {Z : D}
    {f g : F.obj (((arrangementCellularRealization A k Q).obj M).X q) ⟶ Z}
    (same : ∀ (d : NormalizedCell A q) (x : M.obj ⟨q,d⟩),
      F.map (Cellular.vectorCopowerInclusion k (Q.obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
        arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k Q M) q d) ≫ f =
      F.map (Cellular.vectorCopowerInclusion k (Q.obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
        arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k Q M) q d) ≫ g) :
    f = g := by
  let e := cellularRealizationCoefficientObjectIso A k F Q (Q ⋙ F) (Iso.refl _) M
  apply (cancel_epi (e.inv.f q)).mp
  apply mappedCellularTerm_hom_ext A k (Cellular.covariantCopowerDiagram k (Q ⋙ F) M) q
  intro d
  apply Cellular.vectorCopower_hom_ext k ((Q ⋙ F).obj ⟨q,d⟩) (M.obj ⟨q,d⟩)
  intro x
  have formula := cellularRealizationCoefficientObjectIso_generator A k F Q (Q ⋙ F)
    (Iso.refl _) M q d x
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] at formula
  have factor : (Cellular.vectorCopowerInclusion k ((Q ⋙ F).obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
      arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k (Q ⋙ F) M) q d) ≫
      e.inv.f q =
      F.map (Cellular.vectorCopowerInclusion k (Q.obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
        arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k Q M) q d) :=
    (Iso.comp_inv_eq (HomologicalComplex.Hom.isoApp e q)).mpr formula.symm
  have left := congrArg (fun a => a ≫ f) factor
  have right := congrArg (fun a => a ≫ g) factor
  simpa only [Category.assoc] using left.trans ((same d x).trans right.symm)

end ToricPower.IntegralArrangement

end
