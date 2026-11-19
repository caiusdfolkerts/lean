module

public import ToricPower.ArrangementCellularHomTarget

/-! # Full coefficient functoriality of the actual cellular chains

The canonical comparison with an additive linear functor commutes with
every transformation of the original contravariant coefficient diagram.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  {B D : Type*} [Category.{0} B] [Category.{0} D]
  [Preadditive B] [Preadditive D] [Linear k B] [Linear k D]
  [HasFiniteBiproducts B] [HasFiniteBiproducts D]
  (F : B ⥤ D) [F.Additive] [F.Linear k]

local instance chainNaturalCellFinite (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _

@[reassoc]
theorem cellularChainCoefficientComplexIso_natural
    {P P' : (IncidenceObject A)ᵒᵖ ⥤ B} (α : P ⟶ P') :
    (F.mapHomologicalComplex (.down ℕ)).map
      ((arrangementCellularChainFunctor A k).map α) ≫
        (cellularChainCoefficientComplexIso A k F P').hom =
      (cellularChainCoefficientComplexIso A k F P).hom ≫
        (arrangementCellularChainFunctor A k).map (Functor.whiskerRight α F) := by
  apply HomologicalComplex.Hom.ext
  funext q
  change F.map (biproduct.map (fun c : NormalizedCell A q => α.app (op ⟨q,c⟩))) ≫
      (cellularChainCoefficientTermIso A F P' q).hom =
    (cellularChainCoefficientTermIso A F P q).hom ≫
      biproduct.map (fun c : NormalizedCell A q => F.map (α.app (op ⟨q,c⟩)))
  apply (cancel_epi (cellularChainCoefficientTermIso A F P q).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply biproduct.hom_ext'
  intro c
  simp only [← Category.assoc,cellularChainCoefficientTermIso,
    Functor.mapBiproduct_inv,biproduct.ι_desc]
  rw [← F.map_comp,biproduct.ι_map,F.map_comp,Category.assoc,biproduct.ι_map]
  exact congrArg (fun t => F.map (α.app (op ⟨q,c⟩)) ≫ t)
    (cellularChainCoefficientTermIso_inclusion A F P' q c)

def cellularChainCoefficientFunctorIso :
    arrangementCellularChainFunctor A k (B := B) ⋙ F.mapHomologicalComplex (.down ℕ) ≅
      (Functor.whiskeringRight (IncidenceObject A)ᵒᵖ B D).obj F ⋙
        arrangementCellularChainFunctor A k :=
  NatIso.ofComponents (cellularChainCoefficientComplexIso A k F)
    (fun α => cellularChainCoefficientComplexIso_natural A k F α)

end ToricPower.IntegralArrangement

end

