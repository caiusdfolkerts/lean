module

public import PaperVerification.HomogeneousQuadraticDual

/-! # Tensor-algebra functoriality and the canonical dual pairing

These exact generic maps support the intrinsic quadratic-dual identification.
They are split from that application solely to check their actual proof bodies
with the abstract diagonal-homology dependencies.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.AlternatingForms.IntrinsicQuadraticDual

section TensorFunctor

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def tensorAlgebraMap (e : V →ₗ[K] W) : TensorAlgebra K V →ₐ[K] TensorAlgebra K W :=
  TensorAlgebra.lift K ((TensorAlgebra.ι K).comp e)

@[simp] theorem tensorAlgebraMap_ι (e : V →ₗ[K] W) (x : V) :
    tensorAlgebraMap e (TensorAlgebra.ι K x)=TensorAlgebra.ι K (e x) := by
  rw [tensorAlgebraMap,TensorAlgebra.lift_ι_apply,LinearMap.comp_apply]

def tensorAlgebraCongr (e : V ≃ₗ[K] W) : TensorAlgebra K V ≃ₐ[K] TensorAlgebra K W :=
  AlgEquiv.ofAlgHom (tensorAlgebraMap e.toLinearMap) (tensorAlgebraMap e.symm.toLinearMap)
    (by
      apply TensorAlgebra.hom_ext
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,AlgHom.comp_apply,
        tensorAlgebraMap_ι,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,AlgHom.id_apply])
    (by
      apply TensorAlgebra.hom_ext
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,AlgHom.comp_apply,
        tensorAlgebraMap_ι,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,AlgHom.id_apply])

@[simp] theorem tensorAlgebraCongr_ι (e : V ≃ₗ[K] W) (x : V) :
    tensorAlgebraCongr e (TensorAlgebra.ι K x)=TensorAlgebra.ι K (e x) :=
  tensorAlgebraMap_ι e.toLinearMap x

theorem tensorAlgebraCongr_quadratic (e : V ≃ₗ[K] W) :
    (tensorAlgebraCongr e).toLinearMap.comp
        (HomogeneousQuadraticDual.quadraticInclusion (K := K) (V := V))=
      HomogeneousQuadraticDual.quadraticInclusion.comp
        (TensorProduct.congr e e).toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change tensorAlgebraCongr e
      (HomogeneousQuadraticDual.quadraticInclusion (x ⊗ₜ[K] y))=
    HomogeneousQuadraticDual.quadraticInclusion
      (TensorProduct.congr e e (x ⊗ₜ[K] y))
  rw [HomogeneousQuadraticDual.quadraticInclusion_tmul,TensorProduct.congr_tmul,
    HomogeneousQuadraticDual.quadraticInclusion_tmul,map_mul,
    tensorAlgebraCongr_ι,tensorAlgebraCongr_ι]

/-- Functoriality of the actual canonical tensor evaluation pairing. -/
theorem tensorDual_pairing (e : V ≃ₗ[K] W)
    (q : Module.Dual K W ⊗[K] Module.Dual K W) (z : V ⊗[K] V) :
    TensorProduct.dualDistrib K V V (TensorProduct.congr e.dualMap e.dualMap q) z=
      TensorProduct.dualDistrib K W W q (TensorProduct.congr e e z) := by
  induction q using TensorProduct.induction_on with
  | zero => simp only [map_zero,LinearMap.zero_apply]
  | tmul φ ψ =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul x y =>
          simp only [TensorProduct.congr_tmul,TensorProduct.dualDistrib_apply,
            LinearEquiv.dualMap_apply]
      | add z w hz hw => simp only [map_add,hz,hw]
  | add q r hq hr =>
      simp only [map_add,LinearMap.add_apply,hq,hr]

end TensorFunctor

end PaperVerification.AlternatingForms.IntrinsicQuadraticDual
