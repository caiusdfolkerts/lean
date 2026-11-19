module

public import PaperVerification.AlternatingFormsQuadraticDual
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The coordinate quadratic dual is the literal tensor-algebra quotient

The algebra used in the dual calculation is presented in free-generator
coordinates.  This file supplies the actual comparison with Mathlib's
tensor algebra on the actual dual of the original generator vector space.  The two maps descend the
genuine tensor/free-algebra equivalence, and their inverse laws are proved
on the original quotient maps.  The displayed quadratic tensors become
the literal products of the two tensor-algebra inclusions.

This is a candidate until checked with its complete closure.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.AlternatingForms.QuadraticDual

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]

/-- Coordinates in the tensor square of the actual dual space. -/
def dualTensorCoordinates :
    (Module.Dual K (ν → K) ⊗[K] Module.Dual K (ν → K)) ≃ₗ[K]
      Coordinates (K := K) (ν := ν) :=
  ((Pi.basisFun K ν).dualBasis.tensorProduct (Pi.basisFun K ν).dualBasis).equivFun

/-- The coefficient pairing is exactly the canonical tensor evaluation pairing. -/
theorem actual_tensor_pairing (q t : Coordinates (K := K) (ν := ν)) :
    TensorProduct.dualDistrib K (ν → K) (ν → K)
      (dualTensorCoordinates.symm q) (tensorCoordinates.symm t)=dotDual q t := by
  have h :
      (LinearMap.lcomp K K (tensorCoordinates (K := K) (ν := ν)).symm.toLinearMap).comp
        ((TensorProduct.dualDistrib K (ν → K) (ν → K)).comp
          (dualTensorCoordinates (K := K) (ν := ν)).symm.toLinearMap)=dotDual := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨u,v⟩
    simp only [LinearMap.comp_apply, LinearMap.lcomp_apply, dotDual_basis_right]
    simp [LinearMap.lcomp_apply,dualTensorCoordinates,tensorCoordinates,
      Module.Basis.equivFun_symm_apply,Module.Basis.tensorProduct_apply,
      Pi.basisFun_apply,Pi.single_apply,TensorProduct.dualDistrib_apply,
      Module.Basis.dualBasis_apply,dotDual_basis_right,Prod.mk.injEq]
    split_ifs <;> simp_all
  exact LinearMap.congr_fun (LinearMap.congr_fun h q) t

/-- No self-duality convention is assumed: these are precisely the tensors
in the actual dual tensor square annihilating the original quadratic relations. -/
theorem mem_dualRelations_actual (f g : ⋀[K]^2 (ν → K))
    (q : Coordinates (K := K) (ν := ν)) :
    q∈dualRelations f g ↔
      ∀ z : (ν → K) ⊗[K] (ν → K),
        wedgeMap (tensorCoordinates z)∈
          Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) →
        TensorProduct.dualDistrib K (ν → K) (ν → K) (dualTensorCoordinates.symm q) z=0 := by
  rw [mem_dualRelations]
  constructor
  · intro h z hz
    have hh := h (tensorCoordinates z) hz
    rw [←actual_tensor_pairing] at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  · intro h t ht
    have hh := h (tensorCoordinates.symm t) (by
      simpa only [LinearEquiv.apply_symm_apply] using ht)
    rw [actual_tensor_pairing] at hh
    exact hh

def tensorFreeEquiv : TensorAlgebra K (Module.Dual K (ν → K)) ≃ₐ[K] FreeAlgebra K ν :=
  TensorAlgebra.equivFreeAlgebra (Pi.basisFun K ν).dualBasis

def tensorWordMap : Coordinates (K := K) (ν := ν) →ₗ[K]
    TensorAlgebra K (Module.Dual K (ν → K)) :=
  (Pi.basisFun K (ν × ν)).constr K (fun p =>
    TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis p.1)*
      TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis p.2))

@[simp] theorem tensorWordMap_basis (i j : ν) :
    tensorWordMap (Pi.basisFun K (ν × ν) (i,j))=
      TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis i)*
        TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis j) := by
  simp only [tensorWordMap,Module.Basis.constr_basis]

def tensorQuadraticInclusion :
    (Module.Dual K (ν → K) ⊗[K] Module.Dual K (ν → K)) →ₗ[K]
      TensorAlgebra K (Module.Dual K (ν → K)) :=
  TensorProduct.lift ((LinearMap.mul K (TensorAlgebra K (Module.Dual K (ν → K)))).compl₁₂
    (TensorAlgebra.ι K) (TensorAlgebra.ι K))

/-- The quadratic relation element is the genuine degree-two tensor inclusion. -/
theorem tensorWordMap_eq_actual_inclusion :
    tensorWordMap (K := K) (ν := ν)=
      tensorQuadraticInclusion.comp dualTensorCoordinates.symm.toLinearMap := by
  apply (Pi.basisFun K (ν × ν)).ext
  rintro ⟨i,j⟩
  rw [LinearMap.comp_apply,tensorWordMap_basis]
  simp [tensorQuadraticInclusion,dualTensorCoordinates,
    Module.Basis.equivFun_symm_apply,Module.Basis.tensorProduct_apply,
    Pi.basisFun_apply,Pi.single_apply]

theorem tensorFreeEquiv_word (q : Coordinates (K := K) (ν := ν)) :
    tensorFreeEquiv (tensorWordMap q)=wordMap q := by
  have h : (tensorFreeEquiv (K := K) (ν := ν)).toLinearMap.comp tensorWordMap=wordMap := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    change tensorFreeEquiv (tensorWordMap (Pi.basisFun K (ν × ν) (i,j)))=
      wordMap (Pi.basisFun K (ν × ν) (i,j))
    rw [tensorWordMap_basis,map_mul]
    simp only [tensorFreeEquiv,TensorAlgebra.equivFreeAlgebra_ι_apply,
      wordMap,Module.Basis.constr_basis]
  exact LinearMap.congr_fun h q

theorem tensorFreeEquiv_symm_word (q : Coordinates (K := K) (ν := ν)) :
    tensorFreeEquiv.symm (wordMap q)=tensorWordMap q := by
  apply tensorFreeEquiv.injective
  rw [AlgEquiv.apply_symm_apply,tensorFreeEquiv_word]

inductive TensorDualRelation (f g : ⋀[K]^2 (ν → K)) :
    TensorAlgebra K (Module.Dual K (ν → K)) →
      TensorAlgebra K (Module.Dual K (ν → K)) → Prop
  | annihilator (q : Coordinates (K := K) (ν := ν)) (hq : q∈dualRelations f g) :
      TensorDualRelation f g (tensorWordMap q) 0

/-- The ordinary tensor-algebra quotient by the actual annihilator relations. -/
abbrev TensorQuadraticDual (f g : ⋀[K]^2 (ν → K)) := RingQuot (TensorDualRelation f g)

def tensorDualToCoordinates (f g : ⋀[K]^2 (ν → K)) :
    TensorQuadraticDual f g →ₐ[K] QuadraticDual f g :=
  RingQuot.liftAlgHom K
    ⟨(RingQuot.mkAlgHom K (DualRelation f g)).comp tensorFreeEquiv.toAlgHom,by
      intro x y h
      cases h with
      | annihilator q hq =>
          simp only [AlgHom.comp_apply,AlgEquiv.toAlgHom_apply,tensorFreeEquiv_word,map_zero]
          exact (RingQuot.mkAlgHom_rel K (DualRelation.annihilator q hq)).trans (map_zero _)⟩

def coordinatesToTensorDual (f g : ⋀[K]^2 (ν → K)) :
    QuadraticDual f g →ₐ[K] TensorQuadraticDual f g :=
  RingQuot.liftAlgHom K
    ⟨(RingQuot.mkAlgHom K (TensorDualRelation f g)).comp tensorFreeEquiv.symm.toAlgHom,by
      intro x y h
      cases h with
      | annihilator q hq =>
          simp only [AlgHom.comp_apply,AlgEquiv.toAlgHom_apply,tensorFreeEquiv_symm_word,map_zero]
          exact (RingQuot.mkAlgHom_rel K
            (TensorDualRelation.annihilator q hq)).trans (map_zero _)⟩

@[simp] theorem tensorDualToCoordinates_mk (f g : ⋀[K]^2 (ν → K))
    (x : TensorAlgebra K (Module.Dual K (ν → K))) :
    tensorDualToCoordinates f g (RingQuot.mkAlgHom K (TensorDualRelation f g) x)=
      RingQuot.mkAlgHom K (DualRelation f g) (tensorFreeEquiv x) := by
  simp only [tensorDualToCoordinates,RingQuot.liftAlgHom_mkAlgHom_apply,
    AlgHom.comp_apply,AlgEquiv.toAlgHom_apply]

@[simp] theorem coordinatesToTensorDual_mk (f g : ⋀[K]^2 (ν → K))
    (x : FreeAlgebra K ν) :
    coordinatesToTensorDual f g (RingQuot.mkAlgHom K (DualRelation f g) x)=
      RingQuot.mkAlgHom K (TensorDualRelation f g) (tensorFreeEquiv.symm x) := by
  simp only [coordinatesToTensorDual,RingQuot.liftAlgHom_mkAlgHom_apply,
    AlgHom.comp_apply,AlgEquiv.toAlgHom_apply]

/-- A proved equivalence of the actual quotients, preserving the original generators. -/
def tensorDualEquiv (f g : ⋀[K]^2 (ν → K)) :
    TensorQuadraticDual f g ≃ₐ[K] QuadraticDual f g :=
  AlgEquiv.ofAlgHom (tensorDualToCoordinates f g) (coordinatesToTensorDual f g)
    (by
      apply RingQuot.ringQuot_ext'
      apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply,coordinatesToTensorDual_mk,tensorDualToCoordinates_mk,
        AlgEquiv.apply_symm_apply,AlgHom.id_apply])
    (by
      apply RingQuot.ringQuot_ext'
      apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply,tensorDualToCoordinates_mk,coordinatesToTensorDual_mk,
        AlgEquiv.symm_apply_apply,AlgHom.id_apply])

@[simp] theorem tensorDualEquiv_generator (f g : ⋀[K]^2 (ν → K)) (i : ν) :
    tensorDualEquiv f g
      (RingQuot.mkAlgHom K (TensorDualRelation f g)
        (TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis i)))=
      RingQuot.mkAlgHom K (DualRelation f g) (FreeAlgebra.ι K i) := by
  change tensorDualToCoordinates f g
    (RingQuot.mkAlgHom K (TensorDualRelation f g)
      (TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis i)))=_
  rw [tensorDualToCoordinates_mk,tensorFreeEquiv,
    TensorAlgebra.equivFreeAlgebra_ι_apply]

variable [Nonempty ν]

def tensorQuadraticDualEnvelopingEquiv (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    TensorQuadraticDual f g ≃ₐ[K]
      UniversalEnvelopingAlgebra K (TwoStepCentralLie.LieSpace (TwoStepDual.bracketData f g)) :=
  (tensorDualEquiv f g).trans (quadraticDualEnvelopingEquiv f g hinj)

end PaperVerification.AlternatingForms.QuadraticDual
