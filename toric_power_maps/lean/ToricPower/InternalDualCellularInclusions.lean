module

public import ToricPower.ArrangementInternalDualComplex
public import ToricPower.ArrangementCellularInclusions

/-!
# Original characteristic-cell inclusions under internal duality

These formulas identify the specified complex comparison on every
actual cell. They retain the original biproduct maps and make no
homological or exactness assertion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

universe u v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear k B]
  [HasFiniteBiproducts B]

local instance internalCellularInclusionCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _

/-- The canonical cochain-term comparison carries each literal cell
inclusion to the same biproduct inclusion. -/
@[reassoc]
theorem cellularCochainTermIso_inclusion (Q : IncidenceObject A ⥤ B)
    (q : ℕ) (i : NormalizedCell A q) :
    arrangementCellularCochainInclusion A k Q q i ≫
      (arrangementCellularCochainTermIso A k Q q).hom =
        biproduct.ι (fun c : NormalizedCell A q => Q.obj ⟨q,c⟩) i := by
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc, arrangementCellularCochainTermIso_projection]
  by_cases equal : i = j
  · subst j
    rw [cellularCochainInclusion_projection_self, biproduct.ι_π_self]
  · rw [cellularCochainInclusion_projection_ne A k Q q i j equal,
      biproduct.ι_π_ne _ equal]

variable [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [MonoidalLinear k B]
  (P : (IncidenceObject A)ᵒᵖ ⥤ B)

/-- The actual inverse complex comparison sends a genuine covariant
cell inclusion to the internal dual of the original projection. -/
@[reassoc]
theorem internalDualCellularTermIso_inclusion (q : ℕ)
    (i : NormalizedCell A q) :
    arrangementCellularCochainInclusion A k (P.rightOp ⋙ internalDual B) q i ≫
      (internalDualCellularTermIso A k P q).inv =
        (internalDual B).map
          (biproduct.π (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩)) i).op := by
  change arrangementCellularCochainInclusion A k (P.rightOp ⋙ internalDual B) q i ≫
      (arrangementCellularCochainTermIso A k (P.rightOp ⋙ internalDual B) q).hom ≫
        (internalDualBiproductIso
          (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩))).inv = _
  rw [← Category.assoc, cellularCochainTermIso_inclusion]
  exact internalDualBiproductIso_ι_inv
    (fun c : NormalizedCell A q => P.obj (op ⟨q,c⟩)) i

end ToricPower.IntegralArrangement

end
