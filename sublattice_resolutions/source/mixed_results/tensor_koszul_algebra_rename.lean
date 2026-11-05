module
public import shared_results.part011
public import graph_foundation.part012

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.TensorKoszulAlgebraRename -/
section

/-! # Permuting Koszul generators preserves the actual homology algebra -/

section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace FourPapers.TensorKoszulAlgebraRename
open Classical CommAlg
open scoped TensorProduct
universe u
variable {K A V W : Type u} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W] (e : V ≃ W)

def exterior : Simplicial.Ambient V K ≃ₐ[K] Simplicial.Ambient W K where
  toFun := ExteriorAlgebra.map (TensorExteriorKoszul.vectorRename (K := K) e).toLinearMap
  invFun := ExteriorAlgebra.map (TensorExteriorKoszul.vectorRename (K := K) e).symm.toLinearMap
  left_inv := ExteriorAlgebra.leftInverse_map_iff.mpr
    (TensorExteriorKoszul.vectorRename e).left_inv
  right_inv := ExteriorAlgebra.leftInverse_map_iff.mpr
    (TensorExteriorKoszul.vectorRename e).right_inv
  map_add' := map_add _
  map_mul' := map_mul _
  commutes' := AlgHom.commutes _

def algebra : (A ⊗[K] Simplicial.Ambient V K) ≃ₐ[K]
    (A ⊗[K] Simplicial.Ambient W K) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := A)) (exterior e)

@[simp] theorem algebra_tmul (a : A) (z : Simplicial.Ambient V K) :
    algebra e (a ⊗ₜ[K] z)=a ⊗ₜ[K] TensorExteriorKoszul.exteriorRename e z := rfl

variable (x : V → A) (y : W → A) (hxy : ∀ v, y (e v)=x v)

include hxy in
theorem differential (z : A ⊗[K] Simplicial.Ambient V K) :
    algebra e (TensorExteriorKoszul.differential (K := K) (M := A) x z)=
      TensorExteriorKoszul.differential (K := K) (M := A) y (algebra e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z t hz ht => simp only [map_add,hz,ht]
  | tmul a z =>
      rw [TensorExteriorKoszul.differential_tmul,map_sum,algebra_tmul,
        TensorExteriorKoszul.differential_tmul]
      apply Fintype.sum_equiv e
      intro v
      rw [algebra_tmul,hxy,TensorExteriorKoszul.exteriorRename_contraction]

def homologyEquiv :
    (TensorExteriorKoszul.parityDifferential (K := K) x).Homology ≃ₐ[K]
      (TensorExteriorKoszul.parityDifferential (K := K) y).Homology :=
  ParityDifferential.homologyEquiv _ _ (algebra e) (differential e x y hxy)

end FourPapers.TensorKoszulAlgebraRename

end
end
end


end
