module

public import ToricPower.ArrangementCellularComplex

/-!
# The actual coordinates of covariant cellular cochains

The cochain construction is obtained from the genuine cellular chain
complex in the opposite coefficient category. This file identifies its
terms with the ordinary finite cellwise biproduct and displays every
differential using the original incidence columns and the literal
covariant coefficient maps. The opposite-category construction therefore
does not hide an independent choice of matrix or signs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B]
  {I : Type} (F : I → B) [HasBiproduct F]
  [HasBiproduct (fun i => op (F i))]

/-- The canonical finite-biproduct comparison, proved from its two
universal properties rather than an equality of chosen objects. -/
def unopBiproductIso :
    unop (⨁ fun i => op (F i)) ≅ ⨁ F :=
  (opCoproductIsoProduct' (biproduct.isColimit F)
    (biproduct.isLimit (fun i => op (F i)))).unop

@[reassoc]
theorem unopBiproductIso_inclusion (i : I) :
    (biproduct.π (fun i => op (F i)) i).unop ≫ (unopBiproductIso F).hom =
      biproduct.ι F i := by
  exact congrArg Quiver.Hom.unop
    (opCoproductIsoProduct'_hom_comp_proj (biproduct.isColimit F)
      (biproduct.isLimit (fun i => op (F i))) i)

@[reassoc]
theorem unopBiproductIso_projection (i : I) :
    (unopBiproductIso F).hom ≫ biproduct.π F i =
      (biproduct.ι (fun i => op (F i)) i).unop := by
  apply Quiver.Hom.op_inj
  apply biproduct.hom_ext
  intro j
  rw [op_comp, Category.assoc]
  change (biproduct.π F i).op ≫
      (opCoproductIsoProduct' (biproduct.isColimit F)
        (biproduct.isLimit (fun i => op (F i)))).hom ≫
          biproduct.π (fun i => op (F i)) j =
    biproduct.ι (fun i => op (F i)) i ≫ biproduct.π (fun i => op (F i)) j
  have component := opCoproductIsoProduct'_hom_comp_proj (biproduct.isColimit F)
    (biproduct.isLimit (fun i => op (F i))) j
  change (opCoproductIsoProduct' (biproduct.isColimit F)
      (biproduct.isLimit (fun i => op (F i)))).hom ≫
      biproduct.π (fun i => op (F i)) j = (biproduct.ι F j).op at component
  rw [component, ← op_comp]
  by_cases equal : i = j
  · subst j
    simp only [biproduct.ι_π_self, op_id]
  · simp only [biproduct.ι_π_ne _ equal,
      biproduct.ι_π_ne _ (Ne.symm equal), op_zero]

namespace IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (k : Type) [CommRing k] [Linear k B] [HasFiniteBiproducts B]
  (F : IncidenceObject A ⥤ B)

local instance cochainCoordinateCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _

local instance cochainCoordinateOppositeBiproducts : HasFiniteBiproducts Bᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual cochain term is the ordinary finite sum of the genuine
covariant coefficient objects. -/
def arrangementCellularCochainTermIso (q : ℕ) :
    (arrangementCellularCochainComplex A k F).X q ≅
      ⨁ fun i : NormalizedCell A q => F.obj ⟨q, i⟩ :=
  unopBiproductIso (fun i : NormalizedCell A q => F.obj ⟨q, i⟩)

/-- The literal projection from a cochain term to one cell coefficient. -/
def arrangementCellularCochainProjection (q : ℕ) (i : NormalizedCell A q) :
    (arrangementCellularCochainComplex A k F).X q ⟶ F.obj ⟨q, i⟩ :=
  (biproduct.ι (fun i : NormalizedCell A q => F.op.obj (op ⟨q, i⟩)) i).unop

/-- The literal inclusion of one cell coefficient in its cochain term. -/
def arrangementCellularCochainInclusion (q : ℕ) (i : NormalizedCell A q) :
    F.obj ⟨q, i⟩ ⟶ (arrangementCellularCochainComplex A k F).X q :=
  (biproduct.π (fun i : NormalizedCell A q => F.op.obj (op ⟨q, i⟩)) i).unop

@[reassoc]
theorem arrangementCellularCochainTermIso_projection (q : ℕ)
    (i : NormalizedCell A q) :
    (arrangementCellularCochainTermIso A k F q).hom ≫
        biproduct.π (fun i : NormalizedCell A q => F.obj ⟨q, i⟩) i =
      arrangementCellularCochainProjection A k F q i :=
  unopBiproductIso_projection _ i

@[reassoc]
theorem arrangementCellularCochainInclusion_termIso (q : ℕ)
    (i : NormalizedCell A q) :
    arrangementCellularCochainInclusion A k F q i ≫
        (arrangementCellularCochainTermIso A k F q).hom =
      biproduct.ι (fun i : NormalizedCell A q => F.obj ⟨q, i⟩) i :=
  unopBiproductIso_inclusion _ i

/-- A covariant coefficient map is the original arrow, with zero used
only when the chosen displacement is not an incidence. -/
theorem cellularCoefficientHom_op_unop {e d : ℕ}
    (j : NormalizedCell A e) (i : NormalizedCell A d) (a : Fin n → ℤ)
    (incidence : IncidenceTranslation A ⟨d, i⟩ ⟨e, j⟩ a) :
    (cellularCoefficientHom A F.op j i a).unop =
      F.map (⟨a, incidence⟩ : (⟨d, i⟩ : IncidenceObject A) ⟶ ⟨e, j⟩) := by
  rw [cellularCoefficientHom, dif_pos incidence]
  rfl

/-- Every row of the cochain differential is the transpose of the
original actual cellular column, with no altered incidence signs. -/
theorem arrangementCellularCochain_d_projection (q : ℕ)
    (j : NormalizedCell A (q + 1)) :
    (arrangementCellularCochainComplex A k F).d q (q + 1) ≫
        arrangementCellularCochainProjection A k F (q + 1) j =
      (arrangementCellularColumn A k F.op q j).unop := by
  have column :
      biproduct.ι (fun i : NormalizedCell A (q + 1) => F.op.obj (op ⟨q + 1, i⟩)) j ≫
        (arrangementCellularChainComplex A k F.op).d (q + 1) q =
      arrangementCellularColumn A k F.op q j := by
    rw [arrangementCellularChainComplex_d]
    exact arrangementCellularBoundary_column A k F.op q j
  exact congrArg Quiver.Hom.unop column

/-- The same differential in literal covariant coefficient coordinates. -/
theorem arrangementCellularCochain_d_column (q : ℕ)
    (j : NormalizedCell A (q + 1)) :
    (arrangementCellularCochainComplex A k F).d q (q + 1) ≫
        arrangementCellularCochainProjection A k F (q + 1) j =
      Finsupp.linearCombination k
        (fun p : NormalizedCell A q × (Fin n → ℤ) =>
          arrangementCellularCochainProjection A k F q p.1 ≫
            (cellularCoefficientHom A F.op j p.1 p.2).unop)
        (diagonalGlobalColumn k A q j) := by
  rw [arrangementCellularCochain_d_projection]
  let reverse :
      (F.op.obj (op ⟨q + 1, j⟩) ⟶ arrangementCellularTerm A F.op q) →ₗ[k]
      ((arrangementCellularCochainComplex A k F).X q ⟶ F.obj ⟨q + 1, j⟩) :=
    { toFun := Quiver.Hom.unop
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Finsupp.apply_linearCombination k reverse _ _

end IntegralArrangement
end ToricPower
