module

public import ToricPower.ArrangementRepresentedAllWeightCoordinates
public import ToricPower.ArrangementRepresentableCellMaps
public import ToricPower.ArrangementCellularInclusions

/-!
# Original coefficient generators of the full character inclusions

The character decomposition is defined through genuine colimits.
These formulas identify its original inclusions with the literal
incidence copowers and Laurent monomials, before taking cohomology.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (k : Type) [Field k] (m : Fin n → ℤ)

/-- The actual inclusion into the exhaustive coefficient decomposition. -/
def representedLaurentCoefficientWeightInclusion :
    representedWeightDiagram A S c m k ⟶ representedLaurentDiagram A S c k :=
  colimit.ι (representedWeightFamily A S c k) ⟨m⟩ ≫
    (representedLaurentDiagramCoproductIso A S c k).inv

/-- Evaluation of the categorical coproduct comparison retains its
original weight inclusion. -/
@[reassoc]
theorem representedWeightFamily_colimit_inclusion (d : IncidenceObject A) :
    (colimit.ι (representedWeightFamily A S c k) ⟨m⟩).app d ≫
        (colimitIsoFlipCompColim (representedWeightFamily A S c k)).hom.app d =
      colimit.ι ((representedWeightFamily A S c k).flip.obj d) ⟨m⟩ := by
  simp only [colimitIsoFlipCompColim, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Category.assoc, colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc,
    HasColimit.ι_isoOfNatIso_hom, compEvaluation, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Category.comp_id]
  erw [Category.id_comp]

/-- The actual coefficient inclusion sends the weight generator to
its full Laurent index, with coefficient unchanged. -/
theorem representedLaurentCoefficientWeightInclusion_single
    (d : IncidenceObject A) (f : RepresentedWeightIndex A S c m d) (a : k) :
    (representedLaurentCoefficientWeightInclusion A S c k m).app d
        (Finsupp.single f a) =
      Finsupp.single ((representedLaurentFiberEquiv A S c d).symm ⟨m,f⟩) a := by
  apply (representedLaurentFiberLinearEquiv A S c k d).injective
  rw [representedLaurentFiberLinearEquiv_single]
  have inclusion := ConcreteCategory.congr_hom
    (ModuleDirectSum.sumColimitIso_inclusion k
      ((representedWeightFamily A S c k).flip.obj d) m)
    (Finsupp.single f a)
  have evaluated := ConcreteCategory.congr_hom
    (representedWeightFamily_colimit_inclusion A S c k m d) (Finsupp.single f a)
  simp only [ModuleCat.comp_apply] at inclusion evaluated
  change (representedLaurentDiagramWeightSumIso A S c k).hom.app d
      ((representedLaurentCoefficientWeightInclusion A S c k m).app d
        (Finsupp.single f a)) = _
  unfold representedLaurentCoefficientWeightInclusion representedLaurentDiagramCoproductIso
  simp only [NatTrans.comp_app, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, ModuleCat.comp_apply,
    Iso.inv_hom_id_app_apply]
  erw [evaluated]
  change (ModuleDirectSum.sumColimitIso k
      ((representedWeightFamily A S c k).flip.obj d)).inv
      (colimit.ι ((representedWeightFamily A S c k).flip.obj d) ⟨m⟩
        (Finsupp.single f a)) = DFinsupp.single m (Finsupp.single f a)
  rw [← inclusion]
  have inverse := ConcreteCategory.congr_hom
    (ModuleDirectSum.sumColimitIso k
      ((representedWeightFamily A S c k).flip.obj d)).hom_inv_id
    ((ModuleCat.ofHom (@DFinsupp.lsingle (Fin n → ℤ) k
      (fun i => (((representedWeightFamily A S c k).flip.obj d).obj ⟨i⟩))
      inferInstance inferInstance inferInstance
      (fun a b => Classical.propDecidable (a = b)) m)) (Finsupp.single f a))
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at inverse
  refine inverse.trans ?_
  dsimp only [ModuleCat.ofHom, DFinsupp.lsingle]
  simp only [ConcreteCategory.hom_ofHom]
  change @DFinsupp.single (Fin n → ℤ)
    (fun i => (((representedWeightFamily A S c k).flip.obj d).obj ⟨i⟩))
    _ (fun a b => Classical.propDecidable (a = b)) m (Finsupp.single f a) = _
  apply DFinsupp.ext
  intro t
  by_cases h : m = t
  · subst t
    simp only [DFinsupp.single_eq_same]
  · simp only [DFinsupp.single_eq_of_ne (Ne.symm h)]
    exact @DFinsupp.single_eq_of_ne (Fin n → ℤ)
      (fun i => (((representedWeightFamily A S c k).flip.obj d).obj ⟨i⟩))
      _ (fun a b => Classical.propDecidable (a = b)) m t (Finsupp.single f a) (Ne.symm h)

/-- The complete original chain inclusion is the cellular functor
applied to the original coefficient inclusion. -/
theorem representedLaurentWeightInclusion_eq :
    representedLaurentWeightInclusion A S c k m =
      (arrangementCellularCochainFunctor A k).map
        (representedLaurentCoefficientWeightInclusion A S c k m) ≫
      (representedLaurentCellularComplexIso A S c k).inv := by
  simp only [representedLaurentWeightInclusion, representableCellularWeightSumIso,
    representedLaurentCochainWeightSumIso, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, ModuleDirectSum.complexColimitIso_inclusion_assoc,
    HasColimit.ι_isoOfNatIso_inv_assoc]
  change (representedWeightFamilyComplexIso A S c k).inv.app ⟨m⟩ ≫
    colimit.ι (representedWeightFamily A S c k ⋙ arrangementCellularCochainFunctor A k)
      ⟨m⟩ ≫ _ = _
  simp only [representedWeightFamilyComplexIso, Discrete.natIso_inv_app,
    Iso.refl_inv, Category.id_comp, ι_preservesColimitIso_inv_assoc]
  erw [Category.id_comp]
  simp only [CategoryTheory.Functor.mapIso_inv]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  rfl

/-- The full original character inclusion is the actual incidence
copower inclusion of its literal Laurent monomial. -/
theorem representedLaurentWeightInclusion_generator (q : ℕ)
    (p : RepresentableCostalkIndex A c S m q) (a : k) :
    (representedLaurentWeightInclusion A S c k m).f q
        ((representedWeightCellularCoordinates A S c m k q).symm (Finsupp.single p a)) =
      arrangementCellularCochainInclusion A k
        (Cellular.covariantCopowerDiagram k (reflectedLaurentDiagram A S k)
          (Cellular.representable k c)) q p.val.1
        (Cellular.vectorCopowerInclusion k
          ((reflectedLaurentDiagram A S k).obj ⟨q,p.val.1⟩)
          ((Cellular.representable k c).obj ⟨q,p.val.1⟩)
          (ModuleCat.freeMk p.val.2)
          (Finsupp.single ⟨m+p.val.2.val,p.property⟩ a)) := by
  rw [representedLaurentWeightInclusion_eq, representedWeightCellularCoordinates_symm_single]
  change ((arrangementCellularCochainFunctor A k).map
      (representedLaurentCoefficientWeightInclusion A S c k m) ≫
        (arrangementCellularCochainFunctor A k).map
          (representedLaurentDiagramIso A S c k).inv).f q _ = _
  rw [← CategoryTheory.Functor.map_comp]
  have actual := ConcreteCategory.congr_hom
    (cellularCochainMap_inclusion A k
      (representedLaurentCoefficientWeightInclusion A S c k m ≫
        (representedLaurentDiagramIso A S c k).inv) q p.val.1)
    (Finsupp.single ⟨p.val.2,p.property⟩ a)
  simp only [ModuleCat.comp_apply] at actual
  erw [actual]
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  erw [representedLaurentCoefficientWeightInclusion_single]
  change arrangementCellularCochainInclusion A k
    (Cellular.covariantCopowerDiagram k (reflectedLaurentDiagram A S k)
      (Cellular.representable k c)) q p.val.1
    ((representableLaurentCellCoordinates A S k c q p.val.1).symm
      (Finsupp.single ⟨p.val.2,⟨m+p.val.2.val,p.property⟩⟩ a)) = _
  rw [representableLaurentCellCoordinates_symm_single]

end ToricPower.IntegralArrangement

end
