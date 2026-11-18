module

public import ToricPower.ArrangementCochainCoordinates
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Cellular cochains commute with actual coefficient colimits

In each cellular degree there are finitely many periodic cells. The
actual cochain term is their coproduct, and its maps are the corresponding
coefficient maps. This identifies evaluation of the cellular construction
with restriction of the coefficient diagram followed by a coproduct.
Consequently the full complex, including its original incidence
differentials, preserves every colimit that exists in the coefficient
category. In particular, unrestricted character sums may be taken before
or after constructing the actual cellular complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

universe v u w w'

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (k : Type) [CommRing k]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear k B]
  [HasFiniteBiproducts B]

local instance cochainColimitCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _

local instance cochainColimitOppositeBiproducts : HasFiniteBiproducts Bᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual map of cochain terms acts on each cell by the given
coefficient natural transformation. -/
@[reassoc]
theorem arrangementCellularCochainMap_inclusion
    {F G : IncidenceObject A ⥤ B} (α : F ⟶ G) (q : ℕ)
    (i : NormalizedCell A q) :
    arrangementCellularCochainInclusion A k F q i ≫
        ((arrangementCellularCochainFunctor A k).map α).f q =
      α.app ⟨q, i⟩ ≫ arrangementCellularCochainInclusion A k G q i := by
  change (biproduct.π (fun j : NormalizedCell A q => F.op.obj (op ⟨q, j⟩)) i).unop ≫
      (biproduct.map (fun j : NormalizedCell A q => (α.app ⟨q, j⟩).op)).unop =
    α.app ⟨q, i⟩ ≫
      (biproduct.π (fun j : NormalizedCell A q => G.op.obj (op ⟨q, j⟩)) i).unop
  exact congrArg Quiver.Hom.unop
    (biproduct.map_π (fun j : NormalizedCell A q => (α.app ⟨q, j⟩).op) i)

/-- The actual cell inclusions jointly detect morphisms out of a term. -/
theorem arrangementCellularCochainTerm_hom_ext
    (F : IncidenceObject A ⥤ B) (q : ℕ) {Y : B}
    {f g : (arrangementCellularCochainComplex A k F).X q ⟶ Y}
    (components : ∀ i : NormalizedCell A q,
      arrangementCellularCochainInclusion A k F q i ≫ f =
        arrangementCellularCochainInclusion A k F q i ≫ g) : f = g := by
  apply Quiver.Hom.op_inj
  apply biproduct.hom_ext
  intro i
  exact congrArg Quiver.Hom.op (components i)

/-- Restrict a coefficient diagram to the finite discrete set of cells
in one degree. -/
def cellularDegreeEvaluation (q : ℕ) :
    (IncidenceObject A ⥤ B) ⥤ (Discrete (NormalizedCell A q) ⥤ B) where
  obj F := Discrete.functor (fun i : NormalizedCell A q => F.obj ⟨q, i⟩)
  map α := Discrete.natTrans (fun i => α.app ⟨q, i.as⟩)
  map_id F := by ext i; rfl
  map_comp α β := by ext i; rfl

def cellularCochainTermCoproductIso (F : IncidenceObject A ⥤ B) (q : ℕ) :
    (arrangementCellularCochainComplex A k F).X q ≅
      colimit ((cellularDegreeEvaluation A (B := B) q).obj F) :=
  arrangementCellularCochainTermIso A k F q ≪≫
    biproduct.isoCoproduct (fun i : NormalizedCell A q => F.obj ⟨q, i⟩)

@[reassoc]
theorem cellularCochainTermCoproductIso_inclusion
    (F : IncidenceObject A ⥤ B) (q : ℕ) (i : NormalizedCell A q) :
    arrangementCellularCochainInclusion A k F q i ≫
        (cellularCochainTermCoproductIso A k F q).hom =
      colimit.ι ((cellularDegreeEvaluation A (B := B) q).obj F) ⟨i⟩ := by
  change arrangementCellularCochainInclusion A k F q i ≫
      (arrangementCellularCochainTermIso A k F q).hom ≫
        (biproduct.isoCoproduct _).hom = _
  rw [← Category.assoc, arrangementCellularCochainInclusion_termIso,
    biproduct.isoCoproduct_hom, biproduct.ι_desc]
  rfl

/-- Evaluation of the actual cellular cochain functor is naturally the
finite coproduct of the actual coefficient evaluations. -/
def cellularCochainEvaluationIso (q : ℕ) :
    arrangementCellularCochainFunctor A k (B := B) ⋙
        HomologicalComplex.eval B (ComplexShape.up ℕ) q ≅
      cellularDegreeEvaluation A (B := B) q ⋙ colim :=
  NatIso.ofComponents (fun F => cellularCochainTermCoproductIso A k F q) (by
    intro F G α
    apply arrangementCellularCochainTerm_hom_ext A k F q
    intro i
    change arrangementCellularCochainInclusion A k F q i ≫
        ((arrangementCellularCochainFunctor A k).map α).f q ≫
          (cellularCochainTermCoproductIso A k G q).hom =
      arrangementCellularCochainInclusion A k F q i ≫
        (cellularCochainTermCoproductIso A k F q).hom ≫
          colim.map ((cellularDegreeEvaluation A q).map α)
    rw [← Category.assoc, arrangementCellularCochainMap_inclusion,
      Category.assoc, cellularCochainTermCoproductIso_inclusion,
      ← Category.assoc, cellularCochainTermCoproductIso_inclusion,
      colimit.ι_map]
    rfl)

/-- Every genuine coefficient colimit is preserved by the complete
cellular cochain complex, not just by its individual graded modules. -/
instance arrangementCellularCochainPreservesColimitsOfShape
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J B] :
    PreservesColimitsOfShape J (arrangementCellularCochainFunctor A k (B := B)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro q
  haveI : PreservesColimitsOfShape J (cellularDegreeEvaluation A (B := B) q) := by
    apply preservesColimitsOfShape_of_evaluation _ J
    intro i
    change PreservesColimitsOfShape J
      ((evaluation (IncidenceObject A) B).obj ⟨q, i.as⟩)
    infer_instance
  exact preservesColimitsOfShape_of_natIso (cellularCochainEvaluationIso A k q).symm

end ToricPower.IntegralArrangement
