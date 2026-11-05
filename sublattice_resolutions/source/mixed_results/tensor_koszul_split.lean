module
public import mixed_results.exterior_sum_tensor
public import mixed_results.tensor_exterior_perturbation

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.TensorKoszulSplit -/
section

/-! # The literal two-family Koszul differential in tensor coordinates

The second differential includes the parity of the first exterior factor.
Consequently the displayed sum is exactly the Koszul differential of the
concatenated family, over every characteristic.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.TensorKoszulSplit
open Classical CommAlg
open scoped TensorProduct
universe u
variable {K A V W : Type u} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]

local instance : LinearOrder (V ⊕ W) :=
  LinearOrder.lift' (fun z : V ⊕ W => (toLex z : Lex (V ⊕ W))) (fun _ _ h => h)

def join :
    ((A ⊗[K] Simplicial.Ambient V K) ⊗[K] Simplicial.Ambient W K) ≃ₗ[K]
      (A ⊗[K] Simplicial.Ambient (V ⊕ W) K) :=
  (TensorProduct.assoc K A (Simplicial.Ambient V K) (Simplicial.Ambient W K)).trans
    (TensorProduct.congr (LinearEquiv.refl K A) ExteriorSumTensor.join)

@[simp] theorem join_tmul (a : A) (z : Simplicial.Ambient V K)
    (w : Simplicial.Ambient W K) :
    join ((a ⊗ₜ[K] z) ⊗ₜ[K] w) = a ⊗ₜ[K] ExteriorSumTensor.join (z ⊗ₜ[K] w) := rfl

def rightOperator (g : W → A) (w : W) :
    Module.End K (A ⊗[K] Simplicial.Ambient V K) :=
  TensorProduct.map (Algebra.lsmul K K A (g w))
    CliffordAlgebra.involute.toLinearMap

@[simp] theorem rightOperator_tmul (g : W → A) (w : W)
    (a : A) (z : Simplicial.Ambient V K) :
    rightOperator (V := V) g w (a ⊗ₜ[K] z)=
      (g w*a) ⊗ₜ[K] CliffordAlgebra.involute z := rfl

def splitDifferential (f : V → A) (g : W → A) :
    Module.End K ((A ⊗[K] Simplicial.Ambient V K) ⊗[K] Simplicial.Ambient W K) :=
  (TensorExteriorKoszul.differential (K := K) (M := A) f).rTensor
      (Simplicial.Ambient W K) +
    TensorExteriorPerturbation.differential (rightOperator (V := V) g)

theorem differential_join_tmul (f : V → A) (g : W → A)
    (a : A) (z : Simplicial.Ambient V K) (w : Simplicial.Ambient W K) :
    TensorExteriorKoszul.differential (K := K) (M := A) (Sum.elim f g)
      (join ((a ⊗ₜ[K] z) ⊗ₜ[K] w)) =
        join (splitDifferential f g ((a ⊗ₜ[K] z) ⊗ₜ[K] w)) := by
  rw [join_tmul, TensorExteriorKoszul.differential_tmul,Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,smul_eq_mul,
    ExteriorSumTensor.contraction_left,ExteriorSumTensor.contraction_right]
  rw [splitDifferential,LinearMap.add_apply,LinearMap.rTensor_tmul,
    TensorExteriorKoszul.differential_tmul,TensorExteriorPerturbation.differential_tmul,
    TensorProduct.sum_tmul,map_add,map_sum,map_sum]
  congr 1

theorem differential_join (f : V → A) (g : W → A)
    (z : (A ⊗[K] Simplicial.Ambient V K) ⊗[K] Simplicial.Ambient W K) :
    TensorExteriorKoszul.differential (K := K) (M := A) (Sum.elim f g) (join z)=
      join (splitDifferential f g z) := by
  have he : (TensorExteriorKoszul.differential (K := K) (M := A) (Sum.elim f g)).comp
      (join (K := K) (A := A) (V := V) (W := W)).toLinearMap =
      join.toLinearMap.comp (splitDifferential f g) := by
    apply TensorProduct.ext'
    intro x w
    induction x using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul,map_zero]
    | add x y hx hy =>
        simp only [TensorProduct.add_tmul,map_add,LinearMap.comp_apply] at *
        exact congrArg₂ (·+·) hx hy
    | tmul a z => exact differential_join_tmul f g a z w
  exact LinearMap.congr_fun he z

theorem splitDifferential_square (f : V → A) (g : W → A) :
    splitDifferential (K := K) f g * splitDifferential f g=0 := by
  apply LinearMap.ext
  intro z
  apply (join (K := K) (A := A) (V := V) (W := W)).injective
  rw [LinearMap.zero_apply, map_zero]
  change join (splitDifferential f g (splitDifferential f g z))=0
  rw [← differential_join,← differential_join]
  exact LinearMap.congr_fun (TensorExteriorKoszul.differential_comp (Sum.elim f g)) _

end FourPapers.TensorKoszulSplit

end
end
end

end
