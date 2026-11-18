module

public import ToricPower.CellularCovariantLabels
public import ToricPower.ArrangementCellularInclusions
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Linearity and unrestricted colimits of actual cellular realization

Every degree is the genuine finite sum of vector copowers of the actual
labels. The proofs below retain that construction and establish the
linearity and colimit preservation needed for linear representable
density. No finite-dimensional condition is imposed on the diagrams.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k]
  {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasColimitsOfSize.{u,u} B]

instance vectorCopower_linear (P : B) : (vectorCopowerFunctor k P).Linear k where
  map_smul f r := by
    apply vectorCopower_hom_ext k P _
    intro x
    simp only [vectorCopowerInclusion_map, Linear.comp_smul]
    change vectorCopowerInclusion k P _ (r • f x) =
      r • vectorCopowerInclusion k P _ (f x)
    exact map_smul _ r (f x)

instance covariantCopowerFunctor_additive (Q : C ⥤ B) :
    (covariantCopowerFunctor k Q).Additive where
  map_add := by
    intro F G α β
    apply NatTrans.ext
    funext c
    exact (vectorCopowerFunctor k (Q.obj c)).map_add

instance covariantCopowerFunctor_linear (Q : C ⥤ B) :
    (covariantCopowerFunctor k Q).Linear k where
  map_smul α r := by
    apply NatTrans.ext
    funext c
    exact (vectorCopowerFunctor k (Q.obj c)).map_smul r (α.app c)

/-- Colimits of diagrams and their actual vector copowers are computed
at each original object. -/
instance covariantCopowerFunctor_preservesColimits (Q : C ⥤ B) :
    PreservesColimitsOfSize.{u,u} (covariantCopowerFunctor k Q) := by
  apply preservesColimits_of_evaluation
  intro c
  change PreservesColimitsOfSize.{u,u}
    (((evaluation C (ModuleCat.{u} k)).obj c) ⋙ vectorCopowerFunctor k (Q.obj c))
  infer_instance

end ToricPower.Cellular

namespace ToricPower.IntegralArrangement

universe v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type v} [Category.{0} B] [Preadditive B] [Linear k B]
  [HasColimitsOfSize.{0,0} B] [HasFiniteBiproducts B]

local instance cellularColimitCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance cellularColimitOppositeBiproducts : HasFiniteBiproducts Bᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance arrangementCellularCochainFunctor_additive :
    (arrangementCellularCochainFunctor A k (B := B)).Additive where
  map_add := by
    intro F G α β
    apply HomologicalComplex.Hom.ext
    funext q
    apply Quiver.Hom.op_inj
    change biproduct.map (fun c : NormalizedCell A q =>
        (α.app ⟨q,c⟩ + β.app ⟨q,c⟩).op) =
      biproduct.map (fun c : NormalizedCell A q => (α.app ⟨q,c⟩).op) +
        biproduct.map (fun c : NormalizedCell A q => (β.app ⟨q,c⟩).op)
    apply biproduct.hom_ext
    intro c
    simp only [Preadditive.add_comp, biproduct.map_π, op_add,
      Preadditive.comp_add]

instance arrangementCellularCochainFunctor_linear :
    (arrangementCellularCochainFunctor A k (B := B)).Linear k where
  map_smul α r := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply Quiver.Hom.op_inj
    change biproduct.map (fun c : NormalizedCell A q => (r • α.app ⟨q,c⟩).op) =
      r • biproduct.map (fun c : NormalizedCell A q => (α.app ⟨q,c⟩).op)
    apply biproduct.hom_ext
    intro c
    simp only [Linear.smul_comp, biproduct.map_π, Linear.op_smul,
      Linear.comp_smul]

/-- Evaluation on the actual cells of a specified degree, with no
quotient or replacement of the cell set. -/
def cellularDegreeDiagram (q : ℕ) :
    (IncidenceObject A ⥤ B) ⥤ (Discrete (NormalizedCell A q) ⥤ B) where
  obj F := Discrete.functor (fun c => F.obj ⟨q,c⟩)
  map α := Discrete.natTrans (fun c => α.app ⟨q,c.as⟩)
  map_id _ := by ext c; rfl
  map_comp _ _ := by ext c; rfl

instance cellularDegreeDiagram_preservesColimits (q : ℕ) :
    PreservesColimitsOfSize.{0,0} (cellularDegreeDiagram A (B := B) q) := by
  apply preservesColimits_of_evaluation
  intro c
  change PreservesColimitsOfSize.{0,0}
    ((evaluation (IncidenceObject A) B).obj ⟨q,c.as⟩)
  infer_instance

/-- The actual cochain term is naturally the original coproduct of
its actual cell coefficients. -/
def cellularDegreeCoproductIso (q : ℕ) :
    arrangementCellularCochainFunctor A k ⋙ HomologicalComplex.eval B (.up ℕ) q ≅
      cellularDegreeDiagram A q ⋙ colim :=
  NatIso.ofComponents (fun F =>
    arrangementCellularCochainTermIso A k F q ≪≫
      biproduct.isoCoproduct (fun c : NormalizedCell A q => F.obj ⟨q,c⟩)) (by
    intro F G α
    simp only [Iso.trans_hom, Category.assoc]
    change ((arrangementCellularCochainFunctor A k).map α).f q ≫
        (arrangementCellularCochainTermIso A k G q).hom ≫
          (biproduct.isoCoproduct (fun c : NormalizedCell A q => G.obj ⟨q,c⟩)).hom =
      (arrangementCellularCochainTermIso A k F q).hom ≫
        (biproduct.isoCoproduct (fun c : NormalizedCell A q => F.obj ⟨q,c⟩)).hom ≫
          colimMap (Discrete.natTrans
            (F := Discrete.functor (fun c : NormalizedCell A q => F.obj ⟨q,c⟩))
            (G := Discrete.functor (fun c : NormalizedCell A q => G.obj ⟨q,c⟩))
            (fun c : Discrete (NormalizedCell A q) => α.app ⟨q,c.as⟩))
    apply (cancel_epi (arrangementCellularCochainTermIso A k F q).inv).mp
    apply biproduct.hom_ext'
    intro c
    have inclusion : biproduct.ι (fun d : NormalizedCell A q => F.obj ⟨q,d⟩) c ≫
        (arrangementCellularCochainTermIso A k F q).inv =
        arrangementCellularCochainInclusion A k F q c := by
      rw [← arrangementCellularCochainInclusion_termIso A k F q c]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (biproduct.ι _ c), inclusion,
      cellularCochainMap_inclusion_assoc,
      arrangementCellularCochainInclusion_termIso_assoc,
      biproduct.isoCoproduct_hom, biproduct.isoCoproduct_hom,
      biproduct.ι_desc, biproduct.ι_desc_assoc]
    change α.app ⟨q,c⟩ ≫ Sigma.ι (fun d : NormalizedCell A q => G.obj ⟨q,d⟩) c =
      Sigma.ι (fun d : NormalizedCell A q => F.obj ⟨q,d⟩) c ≫
        colimMap (Discrete.natTrans
          (F := Discrete.functor (fun c : NormalizedCell A q => F.obj ⟨q,c⟩))
          (G := Discrete.functor (fun c : NormalizedCell A q => G.obj ⟨q,c⟩))
          (fun d : Discrete (NormalizedCell A q) => α.app ⟨q,d.as⟩))
    exact (ι_colimMap (Discrete.natTrans
      (F := Discrete.functor (fun c : NormalizedCell A q => F.obj ⟨q,c⟩))
      (G := Discrete.functor (fun c : NormalizedCell A q => G.obj ⟨q,c⟩))
      (fun d : Discrete (NormalizedCell A q) => α.app ⟨q,d.as⟩)) ⟨c⟩).symm)

instance arrangementCellularCochainFunctor_preservesColimits :
    PreservesColimitsOfSize.{0,0} (arrangementCellularCochainFunctor A k (B := B)) where
  preservesColimitsOfShape := by
    intro J inst
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro q
    exact preservesColimitsOfShape_of_natIso (cellularDegreeCoproductIso A k q).symm

variable (Q : IncidenceObject A ⥤ B)

instance arrangementCellularRealization_additive :
    (arrangementCellularRealization A k Q).Additive := by
  unfold arrangementCellularRealization
  infer_instance

instance arrangementCellularRealization_linear :
    (arrangementCellularRealization A k Q).Linear k := by
  unfold arrangementCellularRealization
  infer_instance

/-- The complete actual cellular functor preserves all small colimits,
including unrestricted vector copowers and coproducts. -/
instance arrangementCellularRealization_preservesColimits :
    PreservesColimitsOfSize.{0,0} (arrangementCellularRealization A k Q) := by
  unfold arrangementCellularRealization
  infer_instance

end ToricPower.IntegralArrangement

end
