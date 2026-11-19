module

public import ToricPower.LinearVectorCopower
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Vector copowers of modules are their genuine tensor products

The comparison sends each original vector inclusion to the corresponding
pure tensor. Its inverse is constructed from those same inclusions.
Neither module is assumed finite dimensional.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] (P M : ModuleCat.{u} k)

/-- The bilinear insertion into the original categorical copower. -/
def moduleCopowerBilinear : P →ₗ[k] M →ₗ[k] ↑(vectorCopower k P M) where
  toFun p :=
    { toFun := fun m => vectorCopowerInclusion k P M m p
      map_add' := fun m n => by
        rw [map_add]
        rfl
      map_smul' := fun a m => by
        rw [map_smul]
        rfl }
  map_add' p q := by
    apply LinearMap.ext
    intro m
    exact (vectorCopowerInclusion k P M m).hom.map_add p q
  map_smul' a p := by
    apply LinearMap.ext
    intro m
    exact (vectorCopowerInclusion k P M m).hom.map_smul a p

/-- The canonical tensor-to-copower map. -/
def moduleCopowerTensorInverse : ModuleCat.of k (P ⊗[k] M) ⟶ vectorCopower k P M :=
  ModuleCat.ofHom (TensorProduct.lift (moduleCopowerBilinear k P M))

/-- The canonical copower-to-tensor map. -/
def moduleCopowerTensorMap : vectorCopower k P M ⟶ ModuleCat.of k (P ⊗[k] M) :=
  (vectorCopowerHomEquiv k P M (ModuleCat.of k (P ⊗[k] M))).symm
    (ModuleCat.ofHom
      { toFun := fun m => ModuleCat.ofHom ((TensorProduct.mk k P M).flip m)
        map_add' := fun m n => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro p
          exact TensorProduct.tmul_add p m n
        map_smul' := fun a m => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro p
          exact TensorProduct.tmul_smul a p m })

@[simp]
theorem moduleCopowerTensorMap_inclusion (m : M) (p : P) :
    moduleCopowerTensorMap k P M (vectorCopowerInclusion k P M m p) = p ⊗ₜ[k] m := by
  exact ConcreteCategory.congr_hom
    (vectorCopowerInclusion_desc k P M (ModuleCat.of k (P ⊗[k] M)) _ m) p

@[simp]
theorem moduleCopowerTensorInverse_tmul (p : P) (m : M) :
    moduleCopowerTensorInverse k P M (p ⊗ₜ[k] m) = vectorCopowerInclusion k P M m p :=
  TensorProduct.lift.tmul _ _

/-- The isomorphism has the specified pure-tensor formula. -/
def moduleVectorCopowerTensorIso : vectorCopower k P M ≅ ModuleCat.of k (P ⊗[k] M) where
  hom := moduleCopowerTensorMap k P M
  inv := moduleCopowerTensorInverse k P M
  hom_inv_id := by
    apply vectorCopower_hom_ext k P M
    intro m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change moduleCopowerTensorInverse k P M
      (moduleCopowerTensorMap k P M (vectorCopowerInclusion k P M m p)) =
        vectorCopowerInclusion k P M m p
    rw [moduleCopowerTensorMap_inclusion, moduleCopowerTensorInverse_tmul]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro p
    apply LinearMap.ext
    intro m
    change moduleCopowerTensorMap k P M
      (moduleCopowerTensorInverse k P M (p ⊗ₜ[k] m)) = p ⊗ₜ[k] m
    rw [moduleCopowerTensorInverse_tmul, moduleCopowerTensorMap_inclusion]

end ToricPower.Cellular

end
