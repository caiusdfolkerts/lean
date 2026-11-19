module
public import graph_foundation.part013
public import shared_results.part018_koszul_summand_projection

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.KoszulCoefficientProjection -/
section

/-! # Coefficient-degree projections on literal Koszul algebras -/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.KoszulCoefficientProjection
open Classical CommAlg
open scoped TensorProduct
universe u
variable {K A B V W : Type u} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W]

def tensor (P : A →ₗ[K] A) :
    (A ⊗[K] Simplicial.Ambient V K) →ₗ[K] (A ⊗[K] Simplicial.Ambient V K) :=
  P.rTensor (Simplicial.Ambient V K)

@[simp] theorem tensor_tmul (P : A →ₗ[K] A) (a : A) (z : Simplicial.Ambient V K) :
    tensor P (a ⊗ₜ[K] z)=P a ⊗ₜ[K] z := rfl

include V in
theorem tensor_idempotent (P : A →ₗ[K] A) (hP : ∀ a, P (P a)=P a) :
    ∀ x, tensor (V := V) P (tensor P x)=tensor P x := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a z => simp only [tensor_tmul,hP]

theorem differential_commute (f : V → A) (P : A →ₗ[K] A)
    (hP : ∀ v a, P (f v*a)=f v*P a) :
    ∀ x, TensorExteriorKoszul.differential (K := K) (M := A) f (tensor P x)=
      tensor P (TensorExteriorKoszul.differential (K := K) (M := A) f x) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a z =>
      simp only [tensor_tmul,TensorExteriorKoszul.differential_tmul,smul_eq_mul,map_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hP]

theorem map_commute {E₁ E₂ : Type*} [AddCommGroup E₁] [Module K E₁]
    [AddCommGroup E₂] [Module K E₂]
    (F : A →ₗ[K] B) (L : E₁ →ₗ[K] E₂)
    (P : A →ₗ[K] A) (Q : B →ₗ[K] B) (hPQ : ∀ a, F (P a)=Q (F a)) :
    ∀ x, TensorProduct.map F L ((P.rTensor E₁) x)=
      (Q.rTensor E₂) (TensorProduct.map F L x) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a z =>
      change F (P a) ⊗ₜ[K] L z=Q (F a) ⊗ₜ[K] L z
      rw [hPQ]

theorem map_range {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (F : M →ₗ[K] N)
    (P : M →ₗ[K] M) (Q : N →ₗ[K] N) (hPQ : ∀ a, F (P a)=Q (F a)) :
    ∀ x∈LinearMap.range P, F x∈LinearMap.range Q := by
  rintro x ⟨a,rfl⟩
  exact ⟨F a,(hPQ a).symm⟩

theorem equiv_range_iff {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (e : M ≃ₗ[K] N)
    (P : M →ₗ[K] M) (Q : N →ₗ[K] N) (hPQ : ∀ a, e (P a)=Q (e a))
    (x : M) : e x∈LinearMap.range Q ↔ x∈LinearMap.range P := by
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨e.symm b,e.injective ?_⟩
    rw [hPQ,e.apply_symm_apply,hb]
  · exact map_range e.toLinearMap P Q hPQ x

theorem right_commute (F : A →ₐ[K] B) (P : A →ₗ[K] A) (Q : B →ₗ[K] B)
    (hPQ : ∀ a, F (P a)=Q (F a)) :
    ∀ x, KoszulSummandProjection.right (V := V) (W := W) F
      (tensor (V := V ⊕ W) P x)=
      tensor (V := W) Q (KoszulSummandProjection.right F x) := by
  intro x
  exact map_commute F.toLinearMap
    (KoszulSummandProjection.rightExterior (K := K) (V := V) (W := W)).toLinearMap
    P Q hPQ x

end FourPapers.KoszulCoefficientProjection

end
end
end


end
