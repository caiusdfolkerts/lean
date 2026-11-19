module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # Exact coordinates after quotienting by a subset of a genuine basis -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.BasisQuotientSelection

variable {K M I : Type*} [Field K] [AddCommGroup M] [Module K M]
  (B : Module.Basis I K M) (P : I → Prop)

def discarded : Submodule K M := Submodule.span K (B '' {i | ¬P i})

def projection : M →ₗ[K] ({i // P i} →₀ K) :=
  (Finsupp.lcomapDomain (R := K) (M := K) Subtype.val Subtype.val_injective).comp B.repr.toLinearMap

@[simp] theorem projection_apply (x : M) (i : {i // P i}) :
    projection B P x i=B.repr x i.val := rfl

theorem projection_surjective : Function.Surjective (projection B P) := by
  intro x
  refine ⟨B.repr.symm (Finsupp.mapDomain Subtype.val x),?_⟩
  change Finsupp.lcomapDomain (R := K) (M := K) Subtype.val Subtype.val_injective
    (B.repr (B.repr.symm (Finsupp.mapDomain Subtype.val x)))=x
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.leftInverse_lcomapDomain_mapDomain Subtype.val Subtype.val_injective x

@[simp] theorem projection_basis (i : {i // P i}) :
    projection B P (B i.val)=Finsupp.single i 1 := by
  apply Finsupp.ext
  intro j
  rw [projection_apply,Module.Basis.repr_self]
  simp only [Finsupp.single_apply,Subtype.ext_iff]

theorem discarded_eq_ker : discarded B P=(projection B P).ker := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Finsupp.ext
    intro j
    rw [projection_apply,Module.Basis.repr_self,Finsupp.zero_apply]
    exact Finsupp.single_eq_of_ne (fun h => hi (h ▸ j.property))
  · intro x hx
    have hz := LinearMap.mem_ker.mp hx
    rw [←B.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨i,?_,rfl⟩
    intro hP
    have he := congrArg (fun z : {i // P i} →₀ K => z ⟨i,hP⟩) hz
    rw [projection_apply,Finsupp.zero_apply] at he
    exact (Finsupp.mem_support_iff.mp hi) he

/-- This is an equivalence of the literal vector-space quotient by the
specified span, with all retained coordinates. -/
def quotientCoordinates : (M ⧸ discarded B P) ≃ₗ[K] ({i // P i} →₀ K) :=
  (Submodule.quotEquivOfEq _ _ (discarded_eq_ker B P)).trans
    ((projection B P).quotKerEquivOfSurjective (projection_surjective B P))

@[simp] theorem quotientCoordinates_mk (x : M) :
    quotientCoordinates B P (Submodule.Quotient.mk x)=projection B P x := by
  simp only [quotientCoordinates,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

def quotientBasis : Module.Basis {i // P i} K (M ⧸ discarded B P) :=
  .ofRepr (quotientCoordinates B P)

@[simp] theorem quotientBasis_apply (i : {i // P i}) :
    quotientBasis B P i=Submodule.Quotient.mk (B i.val) := by
  apply (quotientCoordinates B P).injective
  rw [quotientCoordinates_mk,projection_basis]
  exact Module.Basis.repr_self (quotientBasis B P) i

end PaperVerification.BasisQuotientSelection
