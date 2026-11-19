module
public import mixed_results.tensor_koszul_algebra_rename
public import shared_results.part018_koszul_coefficient_projection

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.TensorKoszulSelectedRename -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.TensorKoszulAlgebraRename
open Classical CommAlg
open scoped TensorProduct
universe u
variable {K A V W : Type u} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W] (e : V ≃ W)

 theorem coefficientProjection_commute (P : A →ₗ[K] A)
    (z : A ⊗[K] Simplicial.Ambient V K) :
    algebra e (KoszulCoefficientProjection.tensor P z)=
      KoszulCoefficientProjection.tensor P (algebra e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a z => rfl

theorem homologyEquiv_selectedClasses (x : V → A) (y : W → A)
    (hxy : ∀ v, y (e v)=x v) (P : A →ₗ[K] A) :
    homologyEquiv e x y hxy ''
      (TensorExteriorKoszul.parityDifferential (K := K) x).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := V) P))=
      (TensorExteriorKoszul.parityDifferential (K := K) y).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := W) P)) := by
  have hRange := KoszulCoefficientProjection.equiv_range_iff (K := K)
    (M := A ⊗[K] Simplicial.Ambient V K) (N := A ⊗[K] Simplicial.Ambient W K)
    (algebra (K := K) (A := A) e).toLinearEquiv
    (KoszulCoefficientProjection.tensor (V := V) P)
    (KoszulCoefficientProjection.tensor (V := W) P)
    (coefficientProjection_commute e P)
  have h := ParityDifferential.homologyEquiv_classesFrom (K := K)
    (A := A ⊗[K] Simplicial.Ambient V K) (B := A ⊗[K] Simplicial.Ambient W K)
    (TensorExteriorKoszul.parityDifferential (K := K) x)
    (TensorExteriorKoszul.parityDifferential (K := K) y)
    (algebra (K := K) (A := A) e) (differential e x y hxy)
    (LinearMap.range (KoszulCoefficientProjection.tensor (V := V) P))
    (LinearMap.range (KoszulCoefficientProjection.tensor (V := W) P)) hRange
  exact h


end FourPapers.TensorKoszulAlgebraRename

end
end
end

end
