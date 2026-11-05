module
public import graph_foundation.part012
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.ExteriorSumTensor -/
section

/-! # Splitting the exterior variables into two finite families

The coordinate equivalence below uses Mathlib's graded tensor product. On
underlying modules it is the usual tensor product, but its multiplication
retains the exterior signs. The contraction formulas explicitly retain
the parity on the first factor when a variable of the second factor is
removed.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace FourPapers.ExteriorSumTensor
open Classical CommAlg
open scoped TensorProduct
universe u
variable {K V W : Type u} [CommRing K] [Fintype V] [Fintype W]

def exteriorCongr {M N : Type u} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (e : M ≃ₗ[K] N) :
    ExteriorAlgebra K M ≃ₗ[K] ExteriorAlgebra K N where
  toFun := ExteriorAlgebra.map e.toLinearMap
  invFun := ExteriorAlgebra.map e.symm.toLinearMap
  left_inv := ExteriorAlgebra.leftInverse_map_iff.mpr e.left_inv
  right_inv := ExteriorAlgebra.leftInverse_map_iff.mpr e.right_inv
  map_add' := map_add _
  map_smul' := map_smul _

def vectorEquiv : (V ⊕ W → K) ≃ₗ[K] ((V → K) × (W → K)) :=
  LinearEquiv.sumArrowLequivProdArrow V W K K

def leftVector : (V → K) →ₗ[K] (V ⊕ W → K) :=
  (vectorEquiv (K := K) (V := V) (W := W)).symm.toLinearMap.comp
    (LinearMap.inl K (V → K) (W → K))

def rightVector : (W → K) →ₗ[K] (V ⊕ W → K) :=
  (vectorEquiv (K := K) (V := V) (W := W)).symm.toLinearMap.comp
    (LinearMap.inr K (V → K) (W → K))

def join :
    (Simplicial.Ambient V K ⊗[K] Simplicial.Ambient W K) ≃ₗ[K]
      Simplicial.Ambient (V ⊕ W) K :=
  ((GradedTensorProduct.of K (fun i : ℕ => ⋀[K]^i (V → K))
      (fun i : ℕ => ⋀[K]^i (W → K))).trans
    (ExteriorAlgebra.prodEquivTensor K (V → K) (W → K)).symm.toLinearEquiv).trans
      (exteriorCongr (vectorEquiv (K := K) (V := V) (W := W)).symm)

theorem join_tmul (a : Simplicial.Ambient V K) (b : Simplicial.Ambient W K) :
    join (a ⊗ₜ[K] b) = ExteriorAlgebra.map leftVector a *
      ExteriorAlgebra.map rightVector b := by
  change ExteriorAlgebra.map (vectorEquiv (K := K) (V := V) (W := W)).symm.toLinearMap
    ((ExteriorAlgebra.prodEquivTensor K (V → K) (W → K)).symm
      (a ᵍ⊗ₜ[K] b)) = _
  rw [ExteriorAlgebra.prodEquivTensor_symm_tmul, map_mul]
  congr 1
  · exact DFunLike.congr_fun (ExteriorAlgebra.map_comp_map
      (LinearMap.inl K (V → K) (W → K)) vectorEquiv.symm.toLinearMap) a
  · exact DFunLike.congr_fun (ExteriorAlgebra.map_comp_map
      (LinearMap.inr K (V → K) (W → K)) vectorEquiv.symm.toLinearMap) b

theorem involute_map {M N : Type u} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (z : ExteriorAlgebra K M) :
    CliffordAlgebra.involute (ExteriorAlgebra.map f z) =
      ExteriorAlgebra.map f (CliffordAlgebra.involute z) := by
  have he : (CliffordAlgebra.involute : ExteriorAlgebra K N →ₐ[K] _).comp
      (ExteriorAlgebra.map f) = (ExteriorAlgebra.map f).comp CliffordAlgebra.involute := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro m
    change CliffordAlgebra.involute (ExteriorAlgebra.map f (ExteriorAlgebra.ι K m)) =
      ExteriorAlgebra.map f (CliffordAlgebra.involute (ExteriorAlgebra.ι K m))
    simp only [ExteriorAlgebra.map_apply_ι, CliffordAlgebra.involute_ι, map_neg]
  exact DFunLike.congr_fun he z

theorem left_left_coordinate (v : V) :
    ((Pi.basisFun K (V ⊕ W)).coord (Sum.inl v)).comp
      (leftVector (K := K) (V := V) (W := W)) = (Pi.basisFun K V).coord v := by
  apply LinearMap.ext
  intro x
  rfl

theorem left_right_coordinate (v : V) :
    ((Pi.basisFun K (V ⊕ W)).coord (Sum.inl v)).comp
      (rightVector (K := K) (V := V) (W := W)) = 0 := by
  apply LinearMap.ext
  intro x
  rfl

theorem right_left_coordinate (w : W) :
    ((Pi.basisFun K (V ⊕ W)).coord (Sum.inr w)).comp
      (leftVector (K := K) (V := V) (W := W)) = 0 := by
  apply LinearMap.ext
  intro x
  rfl

theorem right_right_coordinate (w : W) :
    ((Pi.basisFun K (V ⊕ W)).coord (Sum.inr w)).comp
      (rightVector (K := K) (V := V) (W := W)) = (Pi.basisFun K W).coord w := by
  apply LinearMap.ext
  intro x
  rfl

theorem contraction_left (v : V) (a : Simplicial.Ambient V K)
    (b : Simplicial.Ambient W K) :
    Simplicial.contraction (Sum.inl v) (join (a ⊗ₜ[K] b)) =
      join (Simplicial.contraction v a ⊗ₜ[K] b) := by
  rw [join_tmul, Simplicial.contraction, CliffordAlgebra.contractLeft_mul,
    ExteriorAlgebra.contractLeft_map, ExteriorAlgebra.contractLeft_map,
    left_left_coordinate, left_right_coordinate, map_zero, LinearMap.zero_apply,
    map_zero, mul_zero, add_zero, join_tmul]

theorem contraction_right (w : W) (a : Simplicial.Ambient V K)
    (b : Simplicial.Ambient W K) :
    Simplicial.contraction (Sum.inr w) (join (a ⊗ₜ[K] b)) =
      join (CliffordAlgebra.involute a ⊗ₜ[K] Simplicial.contraction w b) := by
  rw [join_tmul, Simplicial.contraction, CliffordAlgebra.contractLeft_mul,
    ExteriorAlgebra.contractLeft_map, ExteriorAlgebra.contractLeft_map,
    right_left_coordinate, right_right_coordinate, map_zero, LinearMap.zero_apply,
    map_zero, zero_mul, zero_add, involute_map, join_tmul]

end FourPapers.ExteriorSumTensor

end
end
end

end
