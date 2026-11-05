module
public import shared_results.part014
public import shared_results.part002
public import mixed_results.koszul_augmentation

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialCoefficientContraction -/
section

/-! # The polynomial-variable Koszul contraction with arbitrary coefficients -/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.PolynomialCoefficientContraction
open Classical CommAlg MvPolynomial HomologicalPerturbation
open scoped TensorProduct
universe u
variable {K A Y : Type u} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype Y] [LinearOrder Y]
local notation "R" => MvPolynomial Y K
local notation "E" => Simplicial.Ambient Y K

def evaluation : (A ⊗[K] R) →ₐ[K] A :=
  (Algebra.TensorProduct.rid K K A).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id K A) (MvPolynomial.aeval (fun _ : Y => (0 : K))))

@[simp] theorem evaluation_tmul (a : A) (r : R) :
    evaluation (a ⊗ₜ[K] r)=constantCoeff r • a := by
  change (MvPolynomial.aeval (fun _ : Y => (0 : K)) r) • a=_
  rw [MvPolynomial.aeval_zero',Algebra.algebraMap_self]
  rfl

def «variables» (y : Y) : A ⊗[K] R := (1 : A) ⊗ₜ[K] X y

def contraction : LinearContraction
    («R» := K) (M := (A ⊗[K] R) ⊗[K] E) (H := A) :=
  ((((PolynomialFineContraction.polynomialContraction («R» := K) (V := Y)).baseChange A).changeSource
    (TensorProduct.AlgebraTensorModule.assoc K K A A R E).symm).changeTarget
      (TensorProduct.AlgebraTensorModule.rid K A A)).restrictScalars K

theorem contraction_d_tmul (a : A) (r : R) (z : E) :
    (contraction (K := K) (A := A) (Y := Y)).d ((a ⊗ₜ[K] r) ⊗ₜ[K] z)=
      TensorExteriorKoszul.differential (K := K) («R» := A ⊗[K] R) (M := A ⊗[K] R)
        («variables» (K := K) (A := A) (Y := Y)) ((a ⊗ₜ[K] r) ⊗ₜ[K] z) := by
  change (TensorProduct.AlgebraTensorModule.assoc K K A A R E).symm
    (a ⊗ₜ[K] (PolynomialFineContraction.polynomialContraction («R» := K) (V := Y)).d
      (r ⊗ₜ[K] z))=_
  rw [PolynomialFineContraction.polynomialContraction_d,
    TensorExteriorKoszul.differential_tmul,TensorProduct.tmul_sum,map_sum,
    TensorExteriorKoszul.differential_tmul]
  apply Finset.sum_congr rfl
  intro y hy
  change (a ⊗ₜ[K] (X y*r)) ⊗ₜ[K] Simplicial.contraction y z=
    («variables» (K := K) (A := A) y*(a ⊗ₜ[K] r)) ⊗ₜ[K] Simplicial.contraction y z
  rw [«variables»,Algebra.TensorProduct.tmul_mul_tmul,one_mul]

theorem contraction_d : (contraction (K := K) (A := A) (Y := Y)).d=
    TensorExteriorKoszul.differential (K := K) («R» := A ⊗[K] R) (M := A ⊗[K] R)
      («variables» (K := K) (A := A) (Y := Y)) := by
  apply TensorProduct.ext'
  intro x z
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul,map_zero]
  | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
  | tmul a r => exact contraction_d_tmul a r z

theorem contraction_projection : (contraction (K := K) (A := A) (Y := Y)).projection=
    (KoszulAugmentation.augmentation (V := Y) (evaluation (K := K) (A := A) (Y := Y))).toLinearMap := by
  apply TensorProduct.ext'
  intro x z
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul,map_zero]
  | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
  | tmul a r =>
      have he : (contraction (K := K) (A := A) (Y := Y)).projection.comp
          (TensorProduct.mk K (A ⊗[K] R) E (a ⊗ₜ[K] r))=
        (KoszulAugmentation.augmentation (V := Y) (evaluation (K := K) (A := A) (Y := Y))).toLinearMap.comp
          (TensorProduct.mk K (A ⊗[K] R) E (a ⊗ₜ[K] r)) := by
        apply (Simplicial.basis (V := Y) (k := K)).ext
        intro F
        change (PolynomialFineContraction.polynomialContraction («R» := K) (V := Y)).projection
            (r ⊗ₜ[K] Simplicial.basis F) • a=
          KoszulAugmentation.augmentation evaluation ((a ⊗ₜ[K] r) ⊗ₜ[K] Simplicial.basis F)
        rw [PolynomialFineContraction.polynomialContraction_projection_tmul_basis,
          KoszulAugmentation.augmentation_tmul_basis,evaluation_tmul]
        split_ifs <;> simp only [zero_smul]
      exact LinearMap.congr_fun he z

end FourPapers.PolynomialCoefficientContraction

end
end
end

end
