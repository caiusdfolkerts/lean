module

public import ToricPower.LinearVectorCopower
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Copowers of literal free coefficient modules

The chosen vector-space basis used to construct a copower is eliminated
by its universal property. For a free coefficient module, its genuine
free generators give the canonical coproduct of copies of the label.
The coordinate formulas are used for the actual cellular representables.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe v u

variable (k : Type u) [Field k]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasCoproducts.{u} B] (P : B) (I : Type u)

/-- The actual free generators identify the copower with the literal
coproduct indexed by those generators. -/
def vectorCopowerFreeIso :
    vectorCopower k P ((ModuleCat.free k).obj I) ≅ ∐ (fun _ : I => P) where
  hom := (vectorCopowerHomEquiv k P ((ModuleCat.free k).obj I) _).symm
    (ModuleCat.freeDesc (↾fun i : I => Sigma.ι (fun _ : I => P) i))
  inv := Sigma.desc (fun i : I =>
    vectorCopowerInclusion k P ((ModuleCat.free k).obj I) (ModuleCat.freeMk i))
  hom_inv_id := by
    apply (vectorCopowerHomEquiv k P ((ModuleCat.free k).obj I) _).injective
    apply ModuleCat.free_hom_ext
    intro i
    change vectorCopowerInclusion k P ((ModuleCat.free k).obj I) (ModuleCat.freeMk i) ≫
      ((vectorCopowerHomEquiv k P ((ModuleCat.free k).obj I) _).symm
        (ModuleCat.freeDesc (↾fun i : I => Sigma.ι (fun _ : I => P) i)) ≫
        Sigma.desc (fun i : I => vectorCopowerInclusion k P
          ((ModuleCat.free k).obj I) (ModuleCat.freeMk i))) =
      vectorCopowerInclusion k P ((ModuleCat.free k).obj I) (ModuleCat.freeMk i) ≫ 𝟙 _
    rw [← Category.assoc, vectorCopowerInclusion_desc,
      ModuleCat.freeDesc_apply, Category.comp_id]
    change Sigma.ι (fun _ : I => P) i ≫
      Sigma.desc (fun i : I => vectorCopowerInclusion k P
        ((ModuleCat.free k).obj I) (ModuleCat.freeMk i)) = _
    exact Sigma.ι_comp_desc _ _
  inv_hom_id := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_comp_desc, vectorCopowerInclusion_desc,
      ModuleCat.freeDesc_apply, Category.comp_id]
    rfl

@[reassoc]
theorem vectorCopowerFreeIso_generator (i : I) :
    vectorCopowerInclusion k P ((ModuleCat.free k).obj I) (ModuleCat.freeMk i) ≫
        (vectorCopowerFreeIso k P I).hom = Sigma.ι (fun _ : I => P) i := by
  exact (vectorCopowerInclusion_desc k P ((ModuleCat.free k).obj I) _
    (ModuleCat.freeDesc (↾fun i : I => Sigma.ι (fun _ : I => P) i))
    (ModuleCat.freeMk i)).trans (ModuleCat.freeDesc_apply _ i)

@[reassoc]
theorem vectorCopowerFreeIso_inv_inclusion (i : I) :
    Sigma.ι (fun _ : I => P) i ≫ (vectorCopowerFreeIso k P I).inv =
      vectorCopowerInclusion k P ((ModuleCat.free k).obj I) (ModuleCat.freeMk i) :=
  Sigma.ι_comp_desc _ _

variable [Finite I] [HasFiniteBiproducts B]

/-- For a finite actual hom-set, the same canonical comparison lands
in the ordinary finite biproduct. -/
def vectorCopowerFreeBiproductIso :
    vectorCopower k P ((ModuleCat.free k).obj I) ≅ ⨁ (fun _ : I => P) :=
  vectorCopowerFreeIso k P I ≪≫ (biproduct.isoCoproduct (fun _ : I => P)).symm

@[reassoc]
theorem vectorCopowerFreeBiproductIso_generator (i : I) :
    vectorCopowerInclusion k P ((ModuleCat.free k).obj I) (ModuleCat.freeMk i) ≫
        (vectorCopowerFreeBiproductIso k P I).hom =
      biproduct.ι (fun _ : I => P) i := by
  rw [vectorCopowerFreeBiproductIso, Iso.trans_hom,
    vectorCopowerFreeIso_generator_assoc, Iso.symm_hom, biproduct.isoCoproduct_inv,
    Sigma.ι_comp_desc]

end ToricPower.Cellular
