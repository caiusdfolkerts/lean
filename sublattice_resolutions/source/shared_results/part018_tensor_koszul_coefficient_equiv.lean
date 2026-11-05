module
public import graph_foundation.part013
public import shared_results.part018_koszul_coefficient_projection

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.TensorKoszulCoefficientEquiv -/
section

/-! # Coefficient algebra equivalences of actual Koszul algebras -/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.TensorKoszulCoefficientEquiv
open Classical CommAlg
open scoped TensorProduct
universe u
variable {K A B V : Type u} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Fintype V] [LinearOrder V]
  (e : A ≃ₐ[K] B)

def algebra : (A ⊗[K] Simplicial.Ambient V K) ≃ₐ[K]
    (B ⊗[K] Simplicial.Ambient V K) :=
  Algebra.TensorProduct.congr e AlgEquiv.refl

@[simp] theorem algebra_tmul (a : A) (z : Simplicial.Ambient V K) :
    algebra e (a ⊗ₜ[K] z)=e a ⊗ₜ[K] z := rfl

variable (x : V → A) (y : V → B) (hxy : ∀ v,e (x v)=y v)

include hxy in
theorem differential (z : A ⊗[K] Simplicial.Ambient V K) :
    algebra e (TensorExteriorKoszul.differential (K := K) (M := A) x z)=
      TensorExteriorKoszul.differential (K := K) (M := B) y (algebra e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z t hz ht => simp only [map_add,hz,ht]
  | tmul a z =>
      rw [TensorExteriorKoszul.differential_tmul,map_sum,algebra_tmul,
        TensorExteriorKoszul.differential_tmul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [algebra_tmul]
      change e (x v*a) ⊗ₜ[K] Simplicial.contraction v z=
        (y v*e a) ⊗ₜ[K] Simplicial.contraction v z
      rw [map_mul,hxy]

def homologyEquiv :
    (TensorExteriorKoszul.parityDifferential (K := K) x).Homology ≃ₐ[K]
      (TensorExteriorKoszul.parityDifferential (K := K) y).Homology :=
  ParityDifferential.homologyEquiv _ _ (algebra e) (differential e x y hxy)

theorem projection_commute (P : A →ₗ[K] A) (Q : B →ₗ[K] B)
    (hPQ : ∀ a,e (P a)=Q (e a)) (z : A ⊗[K] Simplicial.Ambient V K) :
    algebra e (KoszulCoefficientProjection.tensor P z)=
      KoszulCoefficientProjection.tensor Q (algebra e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z t hz ht => simp only [map_add,hz,ht]
  | tmul a z => change e (P a) ⊗ₜ[K] z=Q (e a) ⊗ₜ[K] z; rw [hPQ]

theorem homologyEquiv_selectedClasses (P : A →ₗ[K] A) (Q : B →ₗ[K] B)
    (hPQ : ∀ a,e (P a)=Q (e a)) :
    homologyEquiv e x y hxy ''
      (TensorExteriorKoszul.parityDifferential (K := K) x).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor P))=
      (TensorExteriorKoszul.parityDifferential (K := K) y).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor Q)) :=
  ParityDifferential.homologyEquiv_classesFrom _ _ (algebra e) (differential e x y hxy)
    _ _ (KoszulCoefficientProjection.equiv_range_iff (algebra e).toLinearEquiv
      (KoszulCoefficientProjection.tensor P) (KoszulCoefficientProjection.tensor Q)
      (projection_commute e P Q hPQ))

end FourPapers.TensorKoszulCoefficientEquiv

end
end
end


end
