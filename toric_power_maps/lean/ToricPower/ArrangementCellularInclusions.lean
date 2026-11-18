module

public import ToricPower.ArrangementCellularCoefficientFunctor

/-!
# Genuine cell inclusions under cellular coefficient comparisons

These identities concern the actual inclusions of the original finite
cochain terms. They complement the projection formulas and identify
individual generators of maps assembled from cellular coefficient
diagrams, before taking homology.
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

local instance (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance : HasFiniteBiproducts Bᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts Dᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts

@[reassoc]
theorem cellularCochainInclusion_projection_self (P : IncidenceObject A ⥤ B)
    (q : ℕ) (i : NormalizedCell A q) :
    arrangementCellularCochainInclusion A k P q i ≫
        arrangementCellularCochainProjection A k P q i = 𝟙 _ :=
  congrArg Quiver.Hom.unop
    (biproduct.ι_π_self (fun c : NormalizedCell A q => P.op.obj (op ⟨q,c⟩)) i)

@[reassoc]
theorem cellularCochainInclusion_projection_ne (P : IncidenceObject A ⥤ B)
    (q : ℕ) (i j : NormalizedCell A q) (different : i ≠ j) :
    arrangementCellularCochainInclusion A k P q i ≫
        arrangementCellularCochainProjection A k P q j = 0 :=
  congrArg Quiver.Hom.unop
    (biproduct.ι_π_ne (fun c : NormalizedCell A q => P.op.obj (op ⟨q,c⟩))
      (Ne.symm different))

/-- A genuine coefficient-diagram map acts on the original cochain
inclusion by its original component. -/
@[reassoc]
theorem cellularCochainMap_inclusion {P P' : IncidenceObject A ⥤ B}
    (α : P ⟶ P') (q : ℕ) (i : NormalizedCell A q) :
    arrangementCellularCochainInclusion A k P q i ≫
        ((arrangementCellularCochainFunctor A k).map α).f q =
      α.app ⟨q,i⟩ ≫ arrangementCellularCochainInclusion A k P' q i := by
  exact congrArg Quiver.Hom.unop
    (biproduct.map_π (fun c : NormalizedCell A q => (α.app ⟨q,c⟩).op) i)

/-- The canonical change of coefficient category preserves every
literal inclusion, not only the dimensions of the finite terms. -/
@[reassoc]
theorem cellularCoefficientTermIso_inclusion
    (F : B ⥤ D) [F.Additive] [F.Linear k] (P : IncidenceObject A ⥤ B)
    (q : ℕ) (i : NormalizedCell A q) :
    F.map (arrangementCellularCochainInclusion A k P q i) ≫
        (cellularCoefficientTermIso A k F P q).hom =
      arrangementCellularCochainInclusion A k (P ⋙ F) q i := by
  apply (cancel_mono (arrangementCellularCochainTermIso A k (P ⋙ F) q).hom).mp
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, arrangementCellularCochainTermIso_projection]
  rw [cellularCoefficientTermIso_projection, ← Functor.map_comp]
  by_cases equal : i = j
  · subst j
    rw [cellularCochainInclusion_projection_self,
      cellularCochainInclusion_projection_self]
    exact F.map_id _
  · rw [cellularCochainInclusion_projection_ne A k P q i j equal,
      cellularCochainInclusion_projection_ne A k (P ⋙ F) q i j equal,
      Functor.map_zero]

end ToricPower.IntegralArrangement

end
