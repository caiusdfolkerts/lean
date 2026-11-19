module

public import ToricPower.SchemeExternalFrameEquiv
public import ToricPower.AffineTildeBaseSections
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The canonical affine exterior-section isomorphism

The product coordinate ring is supplied as a genuine algebra isomorphism
with the tensor product of the two coordinate rings. The induced section
isomorphism is proved to be the canonical exterior product, first for
structure sheaves and then for any two specified rank-one frames.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace ToricPower

universe u
variable (k : Type u) [Field k]

/-- The actual affine global-function isomorphism, with the specified
base-field scalar action on the structure-sheaf section module. -/
def affineUnitBaseSectionsLinearEquiv (R : CommRingCat.{u}) [Algebra k R] :
    R ≃ₗ[k] (FiniteCover.schemeBaseSections k (Spec R) ⊤).obj (𝟙_ (Spec R).Modules) where
  toEquiv := (affineGlobalSectionsEquiv R).toEquiv
  map_add' := (affineGlobalSectionsEquiv R).map_add
  map_smul' a r := by
    change affineGlobalSectionsEquiv R (a • r) =
      (Spec R).presheaf.map (𝟙 (⊤ : (Spec R).Opens)).op
        (Scheme.Modules.baseRingToGlobalSections k (Spec R) a) * affineGlobalSectionsEquiv R r
    rw [Algebra.smul_def, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply,
      TauCeti.AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections_Spec_apply, map_mul]
    rfl

@[simp]
theorem affineUnitBaseSectionsLinearEquiv_apply (R : CommRingCat.{u}) [Algebra k R] (r : R) :
    affineUnitBaseSectionsLinearEquiv k R r = affineGlobalSectionsEquiv R r := rfl

variable (A B P : CommRingCat.{u}) [Algebra k A] [Algebra k B] [Algebra k P]
  (coordinate : A ⊗[k] B ≃ₐ[k] P)

abbrev affineExternalFirstAlgebraMap : A →ₐ[k] P :=
  coordinate.toAlgHom.comp Algebra.TensorProduct.includeLeft
abbrev affineExternalSecondAlgebraMap : B →ₐ[k] P :=
  coordinate.toAlgHom.comp Algebra.TensorProduct.includeRight
abbrev affineExternalFirstMap : Spec P ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom (affineExternalFirstAlgebraMap k A B P coordinate).toRingHom)
abbrev affineExternalSecondMap : Spec P ⟶ Spec B :=
  Spec.map (CommRingCat.ofHom (affineExternalSecondAlgebraMap k A B P coordinate).toRingHom)

local notation "f" => affineExternalFirstMap k A B P coordinate
local notation "g" => affineExternalSecondMap k A B P coordinate

/-- The affine unit calculation, using the actual two coordinate maps. -/
def affineExternalUnitSectionsLinearEquiv :
    (FiniteCover.schemeBaseSections k (Spec A) ⊤).obj (𝟙_ (Spec A).Modules) ⊗[k]
      (FiniteCover.schemeBaseSections k (Spec B) ⊤).obj (𝟙_ (Spec B).Modules) ≃ₗ[k]
        (FiniteCover.schemeBaseSections k (Spec P) ⊤).obj
          (schemeExteriorSheaf f g (𝟙_ (Spec A).Modules) (𝟙_ (Spec B).Modules)) :=
  (TensorProduct.congr (affineUnitBaseSectionsLinearEquiv k A).symm
    (affineUnitBaseSectionsLinearEquiv k B).symm).trans
      (coordinate.toLinearEquiv.trans
        ((affineUnitBaseSectionsLinearEquiv k P).trans
          (((FiniteCover.schemeBaseSections k (Spec P) ⊤).mapIso
            (schemeExternalUnitFrame f g)).toLinearEquiv)))

theorem affineExternalUnitSectionsLinearEquiv_tmul
    (r : (FiniteCover.schemeBaseSections k (Spec A) ⊤).obj (𝟙_ (Spec A).Modules))
    (s : (FiniteCover.schemeBaseSections k (Spec B) ⊤).obj (𝟙_ (Spec B).Modules)) :
    affineExternalUnitSectionsLinearEquiv k A B P coordinate (r ⊗ₜ[k] s) =
      schemeExternalSection k f g (𝟙_ (Spec A).Modules) (𝟙_ (Spec B).Modules) r s := by
  obtain ⟨a, rfl⟩ := (affineUnitBaseSectionsLinearEquiv k A).surjective r
  obtain ⟨b, rfl⟩ := (affineUnitBaseSectionsLinearEquiv k B).surjective s
  simp only [affineExternalUnitSectionsLinearEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.symm_apply_apply, AlgEquiv.toLinearEquiv_apply]
  rw [schemeExternalSection_unit]
  change (schemeExternalUnitFrame f g).hom.app ⊤
      (affineGlobalSectionsEquiv P (coordinate (a ⊗ₜ[k] b))) =
    (schemeExternalUnitFrame f g).hom.app ⊤
      ((f).appTop (affineGlobalSectionsEquiv A a) * (g).appTop (affineGlobalSectionsEquiv B b))
  rw [affineGlobalSectionsEquiv_specMap, affineGlobalSectionsEquiv_specMap, ← map_mul]
  apply congrArg ((schemeExternalUnitFrame f g).hom.app ⊤)
  apply congrArg (affineGlobalSectionsEquiv P)
  change coordinate (a ⊗ₜ[k] b) = coordinate (a ⊗ₜ[k] 1) * coordinate (1 ⊗ₜ[k] b)
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The canonical exterior product is an isomorphism for any two
actual specified rank-one frames on the two affine factors. -/
def affineExternalSectionsLinearEquiv {L : (Spec A).Modules} {M : (Spec B).Modules}
    (left : 𝟙_ (Spec A).Modules ≅ L) (right : 𝟙_ (Spec B).Modules ≅ M) :
    (FiniteCover.schemeBaseSections k (Spec A) ⊤).obj L ⊗[k]
      (FiniteCover.schemeBaseSections k (Spec B) ⊤).obj M ≃ₗ[k]
        (FiniteCover.schemeBaseSections k (Spec P) ⊤).obj (schemeExteriorSheaf f g L M) :=
  schemeExternalSectionsLinearEquivOfFrames k f g left right
    (affineExternalUnitSectionsLinearEquiv k A B P coordinate)

theorem affineExternalSectionsLinearEquiv_eq {L : (Spec A).Modules} {M : (Spec B).Modules}
    (left : 𝟙_ (Spec A).Modules ≅ L) (right : 𝟙_ (Spec B).Modules ≅ M) :
    (affineExternalSectionsLinearEquiv k A B P coordinate left right).toLinearMap =
      schemeExternalSectionsLinearMap k f g L M :=
  schemeExternalSectionsLinearEquivOfFrames_eq k f g left right _
    (affineExternalUnitSectionsLinearEquiv_tmul k A B P coordinate)

end ToricPower

end
