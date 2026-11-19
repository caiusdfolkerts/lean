module

public import ToricPower.ArrangementCellularConstantAugmentation
public import ToricPower.ArrangementCellularHomTarget
public import ToricPower.ArrangementChainFreeCoordinates

/-! # Naturality of the original cellular augmentation

These formulas retain the specified maps on every actual vertex.  They
allow the same chain augmentation to be evaluated on an affine chart
and written in full Laurent coordinates, without changing its map.
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
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear k B] [HasFiniteBiproducts B]
  [HasZeroObject B]

local instance constantNaturalityCells (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _

theorem cellularConstantAugmentation_precompose
    (P Q : (IncidenceObject A)ᵒᵖ ⥤ B) (g : P ⟶ Q) (T : B)
    (α : Q ⟶ (Functor.const (IncidenceObject A)ᵒᵖ).obj T) :
    (arrangementCellularChainFunctor A k).map g ≫
        cellularConstantAugmentation A k Q T α =
      cellularConstantAugmentation A k P T (g ≫ α) := by
  apply (ChainComplex.toSingle₀Equiv _ T).injective
  apply Subtype.ext
  change (arrangementCellularChainMap A k g).f 0 ≫
      (cellularConstantAugmentation A k Q T α).f 0 =
    (cellularConstantAugmentation A k P T (g ≫ α)).f 0
  rw [cellularConstantAugmentation_f_zero,cellularConstantAugmentation_f_zero]
  apply biproduct.hom_ext'
  intro c
  change biproduct.ι _ c ≫ arrangementCellularTermMap A g 0 ≫ _ = _
  erw [← Category.assoc,arrangementCellularTermMap_ι,Category.assoc,
    cellularConstantAugmentationZero_inclusion,
    cellularConstantAugmentationZero_inclusion]
  rfl

theorem cellularConstantAugmentation_postcompose
    (P : (IncidenceObject A)ᵒᵖ ⥤ B) (T U : B) (f : T ⟶ U)
    (α : P ⟶ (Functor.const (IncidenceObject A)ᵒᵖ).obj T) :
    cellularConstantAugmentation A k P T α ≫ (ChainComplex.single₀ B).map f =
      cellularConstantAugmentation A k P U
        (α ≫ (Functor.const (IncidenceObject A)ᵒᵖ).map f) := by
  apply (ChainComplex.toSingle₀Equiv _ U).injective
  apply Subtype.ext
  change (cellularConstantAugmentation A k P T α).f 0 ≫
    ((ChainComplex.single₀ B).map f).f 0 =
    (cellularConstantAugmentation A k P U _).f 0
  rw [ChainComplex.single₀_map_f_zero,cellularConstantAugmentation_f_zero,
    cellularConstantAugmentation_f_zero]
  apply biproduct.hom_ext'
  intro c
  erw [← Category.assoc,cellularConstantAugmentationZero_inclusion,
    cellularConstantAugmentationZero_inclusion]
  rfl

variable {D : Type w} [Category.{z} D] [Preadditive D] [Linear k D]
  [HasFiniteBiproducts D] [HasZeroObject D]
  (F : B ⥤ D) [F.Additive] [F.Linear k]

def cellularConstantCoefficientMap
    (P : (IncidenceObject A)ᵒᵖ ⥤ B) (T : B)
    (α : P ⟶ (Functor.const (IncidenceObject A)ᵒᵖ).obj T) :
    P ⋙ F ⟶ (Functor.const (IncidenceObject A)ᵒᵖ).obj (F.obj T) where
  app c := F.map (α.app c)
  naturality {c d} f := by
    change F.map (P.map f) ≫ F.map (α.app d) = F.map (α.app c) ≫ 𝟙 _
    rw [← CategoryTheory.Functor.map_comp,α.naturality]
    erw [Category.comp_id,Category.comp_id]

theorem cellularConstantAugmentation_map
    (P : (IncidenceObject A)ᵒᵖ ⥤ B) (T : B)
    (α : P ⟶ (Functor.const (IncidenceObject A)ᵒᵖ).obj T) :
    (F.mapHomologicalComplex (.down ℕ)).map
        (cellularConstantAugmentation A k P T α) ≫
        (HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).hom.app T =
      (cellularChainCoefficientComplexIso A k F P).hom ≫
        cellularConstantAugmentation A k (P ⋙ F) (F.obj T)
          (cellularConstantCoefficientMap A F P T α) := by
  apply (ChainComplex.toSingle₀Equiv _ (F.obj T)).injective
  apply Subtype.ext
  change F.map ((cellularConstantAugmentation A k P T α).f 0) ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).hom.app T).f 0 =
    (cellularChainCoefficientTermIso A F P 0).hom ≫
      (cellularConstantAugmentation A k (P ⋙ F) (F.obj T) _).f 0
  simp only [cellularConstantAugmentation_f_zero,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    CategoryTheory.Functor.map_id,Category.comp_id]
  apply (cancel_epi (cellularChainCoefficientTermIso A F P 0).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply biproduct.hom_ext'
  intro c
  simp only [← Category.assoc,cellularChainCoefficientTermIso,
    Functor.mapBiproduct_inv,biproduct.ι_desc]
  erw [← CategoryTheory.Functor.map_comp,cellularConstantAugmentationZero_inclusion,
    Category.comp_id,Category.comp_id,cellularConstantAugmentationZero_inclusion]
  rfl

section Free

variable (P : (IncidenceObject A)ᵒᵖ ⥤ ModuleCat.{0} k)
  (I : IncidenceObject A → Type)
  (coordinates : ∀ c, P.obj (op c) ≃ₗ[k] (I c →₀ k))
  (T : ModuleCat.{0} k)
  (α : P ⟶ (Functor.const (IncidenceObject A)ᵒᵖ).obj T)

theorem cellularConstantAugmentation_free_generator
    (c : NormalizedCell A 0) (a : I ⟨0,c⟩) (r : k) :
    (cellularConstantAugmentation A k P T α).f 0
      ((cellularChainFreeCoordinates A k P I coordinates 0).symm
        (Finsupp.single ⟨c,a⟩ r)) =
      α.app (op ⟨0,c⟩) ((coordinates ⟨0,c⟩).symm (Finsupp.single a r)) := by
  rw [cellularChainFreeCoordinates_symm_single,cellularConstantAugmentation_f_zero]
  erw [← ModuleCat.comp_apply,cellularConstantAugmentationZero_inclusion]
  rfl

end Free

end ToricPower.IntegralArrangement

end
