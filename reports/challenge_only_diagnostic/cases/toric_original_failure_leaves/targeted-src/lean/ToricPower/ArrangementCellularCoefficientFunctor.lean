module

public import ToricPower.ArrangementCochainCoordinates
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Changing the coefficient category of actual cellular cochains

A linear additive functor carries the original finite cellular complex
to the original cellular complex of its coefficient image. The comparison
uses the canonical finite-biproduct map and preserves every translated
incidence coefficient. Exactness of the coefficient functor is not needed
for this equality of complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

universe u v w z

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear k B]
  {D : Type w} [Category.{z} D] [Preadditive D] [Linear k D]
  [HasFiniteBiproducts B] [HasFiniteBiproducts D]
  (F : B ⥤ D) [F.Additive] [F.Linear k]
  (P : IncidenceObject A ⥤ B)

local instance (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance : HasFiniteBiproducts Bᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts Dᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts

local notation "K" => arrangementCellularCochainComplex A k P
local notation "L" => arrangementCellularCochainComplex A k (P ⋙ F)

/-- The literal supported coefficient arrow commutes with a linear
coefficient functor, including translations outside the incidence set. -/
theorem map_cellularCovariantCoefficient {e d : ℕ}
    (j : NormalizedCell A e) (i : NormalizedCell A d) (a : Fin n → ℤ) :
    F.map ((cellularCoefficientHom A P.op j i a).unop) =
      (cellularCoefficientHom A (P ⋙ F).op j i a).unop := by
  by_cases incidence : IncidenceTranslation A ⟨d,i⟩ ⟨e,j⟩ a
  · simp only [cellularCoefficientHom, dif_pos incidence]
    rfl
  · simp only [cellularCoefficientHom, dif_neg incidence, unop_zero, Functor.map_zero]

/-- The canonical comparison on actual finite cellular terms. -/
def cellularCoefficientTermIso (q : ℕ) : F.obj ((K).X q) ≅ (L).X q :=
  F.mapIso (arrangementCellularCochainTermIso A k P q) ≪≫
    F.mapBiproduct (fun c : NormalizedCell A q => P.obj ⟨q,c⟩) ≪≫
      (arrangementCellularCochainTermIso A k (P ⋙ F) q).symm

@[reassoc]
theorem cellularCoefficientTermIso_projection (q : ℕ) (i : NormalizedCell A q) :
    (cellularCoefficientTermIso A k F P q).hom ≫
        arrangementCellularCochainProjection A k (P ⋙ F) q i =
      F.map (arrangementCellularCochainProjection A k P q i) := by
  rw [← arrangementCellularCochainTermIso_projection A k (P ⋙ F) q i]
  simp only [cellularCoefficientTermIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Functor.mapBiproduct_hom]
  change F.map (arrangementCellularCochainTermIso A k P q).hom ≫
      biproduct.lift (fun j => F.map
        (biproduct.π (fun c : NormalizedCell A q => P.obj ⟨q,c⟩) j)) ≫
        biproduct.π (fun c : NormalizedCell A q => F.obj (P.obj ⟨q,c⟩)) i = _
  rw [biproduct.lift_π, ← Functor.map_comp, arrangementCellularCochainTermIso_projection]

/-- The full coboundary square is proved in the original column
coordinates, with the actual coefficient ring action retained. -/
theorem cellularCoefficientTermIso_d (q : ℕ) :
    (cellularCoefficientTermIso A k F P q).hom ≫ (L).d q (q+1) =
      F.map ((K).d q (q+1)) ≫ (cellularCoefficientTermIso A k F P (q+1)).hom := by
  apply (cancel_mono (arrangementCellularCochainTermIso A k (P ⋙ F) (q+1)).hom).mp
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, arrangementCellularCochainTermIso_projection]
  rw [cellularCoefficientTermIso_projection, ← Functor.map_comp,
    arrangementCellularCochain_d_column, arrangementCellularCochain_d_column]
  change (Linear.leftComp k ((P ⋙ F).obj ⟨q+1,j⟩)
      (cellularCoefficientTermIso A k F P q).hom)
        (Finsupp.linearCombination k _ (diagonalGlobalColumn k A q j)) =
    (F.mapLinearMap k) (Finsupp.linearCombination k _ (diagonalGlobalColumn k A q j))
  rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination]
  apply congrArg (fun g : (NormalizedCell A q × (Fin n → ℤ)) →
    (F.obj ((K).X q) ⟶ (P ⋙ F).obj ⟨q+1,j⟩) =>
      Finsupp.linearCombination k g (diagonalGlobalColumn k A q j))
  funext p
  change (cellularCoefficientTermIso A k F P q).hom ≫
      (arrangementCellularCochainProjection A k (P ⋙ F) q p.1 ≫
        (cellularCoefficientHom A (P ⋙ F).op j p.1 p.2).unop) =
    F.map (arrangementCellularCochainProjection A k P q p.1 ≫
      (cellularCoefficientHom A P.op j p.1 p.2).unop)
  rw [Functor.map_comp, ← Category.assoc, cellularCoefficientTermIso_projection,
    map_cellularCovariantCoefficient]

/-- An isomorphism of the actual full complexes, not only their terms
or their cohomology groups. -/
def cellularCoefficientComplexIso :
    ((F.mapHomologicalComplex (.up ℕ)).obj K) ≅ L :=
  HomologicalComplex.Hom.isoOfComponents (cellularCoefficientTermIso A k F P)
    (fun q r relation => by
      obtain rfl : r = q+1 := relation.symm
      exact cellularCoefficientTermIso_d A k F P q)

/-- The genuine cochain map has the literal coefficient projections. -/
@[reassoc]
theorem cellularCochainMap_projection {P P' : IncidenceObject A ⥤ B}
    (α : P ⟶ P') (q : ℕ) (j : NormalizedCell A q) :
    ((arrangementCellularCochainFunctor A k).map α).f q ≫
        arrangementCellularCochainProjection A k P' q j =
      arrangementCellularCochainProjection A k P q j ≫ α.app ⟨q,j⟩ := by
  change (biproduct.map
      (fun c : NormalizedCell A q => (α.app ⟨q,c⟩).op)).unop ≫
        (biproduct.ι (fun c : NormalizedCell A q => P'.op.obj (op ⟨q,c⟩)) j).unop =
    (biproduct.ι (fun c : NormalizedCell A q => P.op.obj (op ⟨q,c⟩)) j).unop ≫
      α.app ⟨q,j⟩
  exact congrArg Quiver.Hom.unop
    (biproduct.ι_map (fun c : NormalizedCell A q => (α.app ⟨q,c⟩).op) j)

/-- The complex comparison is natural in the complete coefficient
diagram, before any homology or derived localization. -/
theorem cellularCoefficientComplexIso_natural {P P' : IncidenceObject A ⥤ B}
    (α : P ⟶ P') :
    (F.mapHomologicalComplex (.up ℕ)).map
        ((arrangementCellularCochainFunctor A k).map α) ≫
      (cellularCoefficientComplexIso A k F P').hom =
    (cellularCoefficientComplexIso A k F P).hom ≫
      (arrangementCellularCochainFunctor A k).map (Functor.whiskerRight α F) := by
  apply HomologicalComplex.Hom.ext
  funext q
  change F.map (((arrangementCellularCochainFunctor A k).map α).f q) ≫
      (cellularCoefficientTermIso A k F P' q).hom =
    (cellularCoefficientTermIso A k F P q).hom ≫
      ((arrangementCellularCochainFunctor A k).map (Functor.whiskerRight α F)).f q
  apply (cancel_mono (arrangementCellularCochainTermIso A k (P' ⋙ F) q).hom).mp
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, arrangementCellularCochainTermIso_projection]
  rw [cellularCoefficientTermIso_projection, ← Functor.map_comp,
    cellularCochainMap_projection, cellularCochainMap_projection,
    Functor.map_comp, ← Category.assoc, cellularCoefficientTermIso_projection]
  rfl

/-- The comparison on whole functors includes all diagram maps. -/
def cellularCoefficientFunctorIso :
    arrangementCellularCochainFunctor A k (B := B) ⋙ F.mapHomologicalComplex (.up ℕ) ≅
      (Functor.whiskeringRight (IncidenceObject A) B D).obj F ⋙
        arrangementCellularCochainFunctor A k :=
  NatIso.ofComponents (cellularCoefficientComplexIso A k F)
    (fun α => cellularCoefficientComplexIso_natural A k F α)

end ToricPower.IntegralArrangement

end
