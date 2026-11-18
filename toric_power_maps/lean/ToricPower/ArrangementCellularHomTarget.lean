module

public import ToricPower.ArrangementCellularCoefficientFunctor
public import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Actual Hom coefficients of a finite cellular cochain complex

The comparison uses the original finite biproducts, translated incidence
arrows and signed cellular columns. No dualization of an infinite vector
space, reflexivity assumption, or replacement differential is involved.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

universe u v w z

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear k B] [HasFiniteBiproducts B]
  {D : Type w} [Category.{z} D] [Preadditive D] [Linear k D] [HasFiniteBiproducts D]
  (F : B ⥤ D) [F.Additive] [F.Linear k]
  (P : (IncidenceObject A)ᵒᵖ ⥤ B)

local instance chainCoefficientCells (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _

def cellularChainCoefficientTermIso (q : ℕ) :
    F.obj (arrangementCellularTerm A P q) ≅ arrangementCellularTerm A (P ⋙ F) q :=
  F.mapBiproduct (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩))

@[reassoc]
theorem cellularChainCoefficientTermIso_inclusion (q : ℕ) (c : NormalizedCell A q) :
    F.map (biproduct.ι (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩)) c) ≫
      (cellularChainCoefficientTermIso A F P q).hom =
        biproduct.ι (fun c : NormalizedCell A q => (P ⋙ F).obj (op ⟨q,c⟩)) c := by
  apply (cancel_mono (cellularChainCoefficientTermIso A F P q).inv).mp
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  simp only [
    cellularChainCoefficientTermIso,Functor.mapBiproduct_inv,biproduct.ι_desc]

theorem map_cellularContravariantCoefficient {e d : ℕ}
    (j : NormalizedCell A e) (i : NormalizedCell A d) (a : Fin n → ℤ) :
    F.map (cellularCoefficientHom A P j i a) =
      cellularCoefficientHom A (P ⋙ F) j i a := by
  by_cases incidence : IncidenceTranslation A ⟨d,i⟩ ⟨e,j⟩ a
  · simp only [cellularCoefficientHom,dif_pos incidence]
    rfl
  · simp only [cellularCoefficientHom,dif_neg incidence,Functor.map_zero]

@[reassoc]
theorem cellularChainCoefficientTermIso_column (q : ℕ) (j : NormalizedCell A (q+1)) :
    F.map (arrangementCellularColumn A k P q j) ≫
      (cellularChainCoefficientTermIso A F P q).hom =
        arrangementCellularColumn A k (P ⋙ F) q j := by
  change (Linear.rightComp k (F.obj (P.obj (op ⟨q+1,j⟩)))
      (cellularChainCoefficientTermIso A F P q).hom)
      ((F.mapLinearMap k) (Finsupp.linearCombination k _ (diagonalGlobalColumn k A q j))) = _
  rw [Finsupp.apply_linearCombination,Finsupp.apply_linearCombination]
  apply congrArg (fun f => Finsupp.linearCombination k f (diagonalGlobalColumn k A q j))
  funext p
  change F.map (cellularCoefficientHom A P j p.1 p.2 ≫
    biproduct.ι (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩)) p.1) ≫ _ = _
  rw [Functor.map_comp,Category.assoc,cellularChainCoefficientTermIso_inclusion,
    map_cellularContravariantCoefficient]

theorem cellularChainCoefficientTermIso_d (q : ℕ) :
    (cellularChainCoefficientTermIso A F P (q+1)).hom ≫
        (arrangementCellularChainComplex A k (P ⋙ F)).d (q+1) q =
      F.map ((arrangementCellularChainComplex A k P).d (q+1) q) ≫
        (cellularChainCoefficientTermIso A F P q).hom := by
  apply (cancel_epi (cellularChainCoefficientTermIso A F P (q+1)).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply biproduct.hom_ext'
  intro j
  simp only [← Category.assoc,
    cellularChainCoefficientTermIso,Functor.mapBiproduct_inv,biproduct.ι_desc]
  rw [arrangementCellularChainComplex_d,arrangementCellularBoundary_column,
    ← Functor.map_comp,arrangementCellularChainComplex_d,
    arrangementCellularBoundary_column]
  exact (cellularChainCoefficientTermIso_column A k F P q j).symm

def cellularChainCoefficientComplexIso :
    ((F.mapHomologicalComplex (.down ℕ)).obj (arrangementCellularChainComplex A k P)) ≅
      arrangementCellularChainComplex A k (P ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (cellularChainCoefficientTermIso A F P)
    (fun q r relation => by
      obtain rfl : q = r+1 := relation.symm
      exact cellularChainCoefficientTermIso_d A k F P r)

section Target

variable (Q : IncidenceObject A ⥤ B) (M : B)

local instance targetHomOppositeBiproducts : HasFiniteBiproducts Bᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The literal contravariant Hom of the actual cellular cochains is
the original cellular chain complex of its full coefficient Hom diagram. -/
def cellularHomTargetComplexIso :
    ((((linearYoneda k B).obj M).mapHomologicalComplex (.down ℕ)).obj
      (arrangementCellularCochainComplex A k Q).op) ≅
        arrangementCellularChainComplex A k (Q.op ⋙ (linearYoneda k B).obj M) :=
  cellularChainCoefficientComplexIso A k ((linearYoneda k B).obj M) Q.op

end Target

end ToricPower.IntegralArrangement

end
