module

public import ToricPower.ArrangementCochainCoordinates
public import ToricPower.InternalDualBiproduct
public import ToricPower.InternalDualLinear

/-!
# Internal duality of the original cellular coefficient complex

The same genuine cellular incidence columns define both complexes.
The canonical dual-biproduct comparison carries each actual boundary
to the actual coboundary with the dual coefficient maps. Scalars and
translation indices are retained literally.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Classical BigOperators

namespace ToricPower.IntegralArrangement

universe u v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  {B : Type u} [Category.{v} B] [MonoidalCategory B] [MonoidalClosed B]
  [Preadditive B] [MonoidalPreadditive B] [Linear k B] [MonoidalLinear k B]
  [HasFiniteBiproducts B] (P : (IncidenceObject A)ᵒᵖ ⥤ B)

local instance internalDualCellularCellsFintype (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _

local notation "Q" => P.rightOp ⋙ internalDual B
local notation "K" => internalDualComplex B (arrangementCellularChainComplex A k P)
local notation "L" => arrangementCellularCochainComplex A k Q

/-- Every literal coefficient map becomes its original internal dual. -/
theorem internalDual_cellularCoefficientHom {e d : ℕ}
    (j : NormalizedCell A e) (i : NormalizedCell A d) (a : Fin n → ℤ) :
    (internalDual B).map (cellularCoefficientHom A P j i a).op =
      (cellularCoefficientHom A (Q).op j i a).unop := by
  by_cases incidence : IncidenceTranslation A ⟨d,i⟩ ⟨e,j⟩ a
  · simp only [cellularCoefficientHom, dif_pos incidence]
    rfl
  · simp only [cellularCoefficientHom, dif_neg incidence, op_zero, unop_zero,
      Functor.map_zero]

/-- The actual internal-dual term has the original covariant cellular
cochain term, through the canonical biproduct comparisons. -/
def internalDualCellularTermIso (q : ℕ) : (K).X q ≅ (L).X q :=
  internalDualBiproductIso
      (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩)) ≪≫
    (arrangementCellularCochainTermIso A k Q q).symm

@[reassoc]
theorem internalDualCellularTermIso_projection (q : ℕ)
    (i : NormalizedCell A q) :
    (internalDualCellularTermIso A k P q).hom ≫
        arrangementCellularCochainProjection A k Q q i =
      (internalDual B).map
        (biproduct.ι (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩)) i).op := by
  rw [← arrangementCellularCochainTermIso_projection]
  simp only [internalDualCellularTermIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact internalDualBiproductIso_hom_π
    (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩)) i

/-- Dualizing a whole original column retains every coefficient and
reverses precisely its original factor maps. -/
theorem internalDualCellularColumn (q : ℕ) (j : NormalizedCell A (q+1)) :
    (internalDual B).map (arrangementCellularColumn A k P q j).op =
      Finsupp.linearCombination k
        (fun p : NormalizedCell A q × (Fin n → ℤ) =>
          (internalDual B).map
              (biproduct.ι (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩)) p.1).op ≫
            (cellularCoefficientHom A (Q).op j p.1 p.2).unop)
        (diagonalGlobalColumn k A q j) := by
  let reverse :
      (P.obj (op ⟨q+1,j⟩) ⟶ arrangementCellularTerm A P q) →ₗ[k]
        ((internalDual B).obj (op (arrangementCellularTerm A P q)) ⟶
          (Q).obj ⟨q+1,j⟩) :=
    { toFun := fun f => (internalDual B).map f.op
      map_add' := fun f g => by simp only [op_add, Functor.map_add]
      map_smul' := fun r f => by
        simp only [Linear.op_smul, Functor.map_smul, RingHom.id_apply] }
  change reverse (Finsupp.linearCombination k _ (diagonalGlobalColumn k A q j)) = _
  rw [Finsupp.apply_linearCombination]
  apply congrArg (fun g : (NormalizedCell A q × (Fin n → ℤ)) →
    ((internalDual B).obj (op (arrangementCellularTerm A P q)) ⟶
      (Q).obj ⟨q+1,j⟩) =>
        Finsupp.linearCombination k g (diagonalGlobalColumn k A q j))
  funext p
  change (internalDual B).map
      (cellularCoefficientHom A P j p.1 p.2 ≫
        biproduct.ι (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩)) p.1).op = _
  rw [op_comp, Functor.map_comp, internalDual_cellularCoefficientHom]

/-- The complete actual differential square, before passing to homology. -/
theorem internalDualCellularTermIso_d (q : ℕ) :
    (internalDualCellularTermIso A k P q).hom ≫ (L).d q (q+1) =
      (K).d q (q+1) ≫ (internalDualCellularTermIso A k P (q+1)).hom := by
  apply (cancel_mono (arrangementCellularCochainTermIso A k Q (q+1)).hom).mp
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, arrangementCellularCochainTermIso_projection]
  rw [internalDualCellularTermIso_projection,
    arrangementCellularCochain_d_column]
  have right : (K).d q (q+1) ≫
      (internalDual B).map
        (biproduct.ι (fun c : NormalizedCell A (q+1) => P.obj (op ⟨q+1,c⟩)) j).op =
      (internalDual B).map (arrangementCellularColumn A k P q j).op := by
    change (internalDual B).map
        ((arrangementCellularChainComplex A k P).d (q+1) q).op ≫ _ = _
    rw [← Functor.map_comp, ← op_comp, arrangementCellularChainComplex_d,
      arrangementCellularBoundary_column]
  rw [right, internalDualCellularColumn]
  let precompose := Linear.leftComp k ((Q).obj ⟨q+1,j⟩)
    (internalDualCellularTermIso A k P q).hom
  change precompose (Finsupp.linearCombination k _ (diagonalGlobalColumn k A q j)) = _
  rw [Finsupp.apply_linearCombination]
  apply congrArg (fun g : (NormalizedCell A q × (Fin n → ℤ)) →
    ((K).X q ⟶ (Q).obj ⟨q+1,j⟩) =>
      Finsupp.linearCombination k g (diagonalGlobalColumn k A q j))
  funext p
  change (internalDualCellularTermIso A k P q).hom ≫
      (arrangementCellularCochainProjection A k Q q p.1 ≫
        (cellularCoefficientHom A (Q).op j p.1 p.2).unop) = _
  rw [← Category.assoc, internalDualCellularTermIso_projection]

/-- The full internal dual is the actual cellular cochain complex of
the dual coefficient functor. This includes all original incidence maps. -/
def internalDualCellularComplexIso : K ≅ L :=
  HomologicalComplex.Hom.isoOfComponents (internalDualCellularTermIso A k P)
    (fun q r relation => by
      obtain rfl : r = q+1 := relation.symm
      exact internalDualCellularTermIso_d A k P q)

end ToricPower.IntegralArrangement

end
