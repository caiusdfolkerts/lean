module

public import PaperVerification.AlternatingFormsTwoStepDual
public import PaperVerification.AlternatingFormsExteriorTransport
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The ordinary quadratic dual and its commutator presentation

Ordered-pair coordinates are the tensor-square coordinates in the standard
basis.  The original quadratic relation space is the inverse image of
`span{f,g}` under the literal wedge map.  The dual relation space is its
ordinary coefficient-pairing annihilator.  This file compares that
annihilator with the kernel-commutator presentation; neither algebra is
defined to make the comparison automatic.

The source remains a proof candidate until its complete closure is checked.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.AlternatingForms.QuadraticDual

open QuadraticCommutatorQuotient TwoStepDual

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]

abbrev Coordinates := (ν × ν) → K

/-- The coefficient space is rigorously identified with the actual
tensor square, through its usual tensor-product basis. -/
def tensorCoordinates : ((ν → K) ⊗[K] (ν → K)) ≃ₗ[K]
    Coordinates (K := K) (ν := ν) :=
  ((Pi.basisFun K ν).tensorProduct (Pi.basisFun K ν)).equivFun

@[simp] theorem tensorCoordinates_tmul (v w : ν → K) (i j : ν) :
    tensorCoordinates (v ⊗ₜ[K] w) (i,j)=v i*w j := by
  simp [tensorCoordinates,Module.Basis.equivFun_apply,
    Module.Basis.tensorProduct_repr_tmul_apply,mul_comm]

def wordMap : Coordinates (K := K) (ν := ν) →ₗ[K] FreeAlgebra K ν :=
  (Pi.basisFun K (ν × ν)).constr K
    (fun p => FreeAlgebra.ι K p.1*FreeAlgebra.ι K p.2)

def wedgeMap : Coordinates (K := K) (ν := ν) →ₗ[K] (⋀[K]^2 (ν → K)) :=
  (Pi.basisFun K (ν × ν)).constr K
    (fun p => exteriorPower.ιMulti K 2 ![Pi.basisFun K ν p.1,Pi.basisFun K ν p.2])

def dotDual : Coordinates (K := K) (ν := ν) →ₗ[K]
    Module.Dual K (Coordinates (K := K) (ν := ν)) :=
  (Pi.basisFun K (ν × ν)).constr K (fun p => LinearMap.proj p)

def coefficientDual : Coordinates (K := K) (ν := ν) →ₗ[K]
    Module.Dual K (⋀[K]^2 (ν → K)) :=
  (Pi.basisFun K (ν × ν)).constr K
    (fun p => orbitExteriorCoefficient p.1 p.2)

def skew : Coordinates (K := K) (ν := ν) →ₗ[K] Coordinates (K := K) (ν := ν) where
  toFun a p := a p-a (p.2,p.1)
  map_add' a b := by ext p; simp; ring
  map_smul' c a := by ext p; simp; ring

@[simp] theorem skew_apply (a : Coordinates (K := K) (ν := ν)) (i j : ν) :
    skew a (i,j)=a (i,j)-a (j,i) := rfl

@[simp] theorem dotDual_basis_right (a : Coordinates (K := K) (ν := ν)) (p : ν × ν) :
    dotDual a (Pi.basisFun K (ν × ν) p)=a p := by
  simp [dotDual,Module.Basis.constr_apply_fintype,Pi.basisFun_equivFun,
    Pi.basisFun_apply,Pi.single_apply]

@[simp] theorem wedgeMap_basis (i j : ν) :
    wedgeMap (Pi.basisFun K (ν × ν) (i,j))=
      exteriorPower.ιMulti K 2 ![Pi.basisFun K ν i,Pi.basisFun K ν j] := by
  simp [wedgeMap]

theorem wedgeMap_surjective : Function.Surjective (wedgeMap (K := K) (ν := ν)) := by
  letI : LinearOrder ν := linearOrderOfSTO WellOrderingRel
  let b := (Pi.basisFun K ν).exteriorPower 2
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro z ⟨s,rfl⟩
  let a := Set.powersetCard.ofFinEmbEquiv.symm s
  refine ⟨Pi.basisFun K (ν × ν) (a 0,a 1),?_⟩
  rw [wedgeMap_basis]
  change exteriorPower.ιMulti K 2 ![Pi.basisFun K ν (a 0),Pi.basisFun K ν (a 1)]=_
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext i
  fin_cases i <;> rfl

theorem wedgeMap_symmetric (i j : ν) :
    wedgeMap (Pi.basisFun K (ν × ν) (i,j)+Pi.basisFun K (ν × ν) (j,i))=0 := by
  apply orbitExteriorCoefficientMatrix_injective
  funext u v
  simp only [map_add,wedgeMap_basis,orbitExteriorCoefficientMatrix,
    orbitExteriorCoefficient_word,map_zero,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- This identity is the actual adjoint relation between the exterior
wedge map and antisymmetrization of tensor coefficients. -/
theorem coefficientDual_wedge (a t : Coordinates (K := K) (ν := ν)) :
    coefficientDual a (wedgeMap t)=dotDual (skew a) t := by
  have H : (LinearMap.lcomp K _ (wedgeMap (K := K) (ν := ν))).comp coefficientDual=
      dotDual.comp skew := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨u,v⟩
    simp only [LinearMap.comp_apply,LinearMap.lcomp_apply,coefficientDual,
      Module.Basis.constr_basis,wedgeMap_basis,orbitExteriorCoefficient_word,
      dotDual_basis_right,skew_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp only [Pi.basisFun_apply,Pi.single_apply,Prod.mk.injEq]
    by_cases hiu : i=u <;> by_cases hiv : i=v <;>
      by_cases hju : j=u <;> by_cases hjv : j=v <;>
      simp [hiu,hiv,hju,hjv,eq_comm]
  exact LinearMap.congr_fun (LinearMap.congr_fun H a) t

theorem bracketMap_eq_coefficientDual (f g : ⋀[K]^2 (ν → K))
    (a : Coordinates (K := K) (ν := ν)) :
    bracketMap (bracketData f g) a=(coefficientDual a f,coefficientDual a g) := by
  have h : bracketMap (bracketData f g)=
      ((LinearMap.applyₗ (R := K) (M₂ := K) f).comp coefficientDual).prod
        ((LinearMap.applyₗ (R := K) (M₂ := K) g).comp coefficientDual) := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    simp only [bracketMap,coefficientDual,Module.Basis.constr_basis,bracketData_basis,
      LinearMap.prod_apply,LinearMap.comp_apply,Function.prod_apply,
      LinearMap.coe_comp,Function.comp_apply,LinearMap.applyₗ_apply_apply,
      orbitExteriorCoefficientMatrix]
  exact LinearMap.congr_fun h a

/-- The original quadratic relations, before taking their annihilator. -/
def originalRelations (f g : ⋀[K]^2 (ν → K)) :
    Submodule K (Coordinates (K := K) (ν := ν)) :=
  (Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K)))).comap wedgeMap

theorem wedge_zero_degree (f : ⋀[K]^2 (ν → K)) :
    exteriorPower.wedge K (ν → K) 2 0 f=
      (exteriorPower.zeroEquiv K (ν → K)).toLinearMap.smulRight f := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  apply Subtype.ext
  simp only [LinearMap.compAlternatingMap_apply,LinearMap.smulRight_apply,
    LinearEquiv.coe_coe,exteriorPower.zeroEquiv_ιMulti,one_smul,
    exteriorPower.wedge,DirectSum.gMulLHom_apply_apply,SetLike.coe_gMul,
    exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_zero_apply,mul_one]

/-- In degree two, the actual generated exterior ideal contains exactly
the linear span of the original forms. -/
theorem exterior_degree_two_relations (f g : ⋀[K]^2 (ν → K)) :
    exteriorDegreeRelations f g 2=Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) := by
  apply le_antisymm ?_ (quadraticSpan_le_exteriorDegreeRelations f g)
  change exteriorDegreeRelations f g (2+0) ≤ _
  rw [exteriorDegreeRelations_eq_images]
  apply sup_le
  · rintro z ⟨v,rfl⟩
    rw [wedge_zero_degree]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rintro z ⟨v,rfl⟩
    rw [wedge_zero_degree]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The original tensor relation space is the kernel of projection to
the actual degree-two quotient, not a postulated presentation. -/
theorem originalRelations_eq_actualKernel (f g : ⋀[K]^2 (ν → K)) :
    originalRelations f g=
      LinearMap.ker ((exteriorDegreeRelations f g 2).mkQ.comp wedgeMap) := by
  rw [LinearMap.ker_comp,Submodule.ker_mkQ,exterior_degree_two_relations]
  rfl

/-- The ordinary tensor coefficient pairing defines the dual relation
space.  It includes the annihilator of the exterior square relations and
of the two specified forms. -/
def dualRelations (f g : ⋀[K]^2 (ν → K)) :
    Submodule K (Coordinates (K := K) (ν := ν)) :=
  (originalRelations f g).dualAnnihilator.comap dotDual

theorem mem_dualRelations (f g : ⋀[K]^2 (ν → K))
    (q : Coordinates (K := K) (ν := ν)) :
    q∈dualRelations f g ↔ ∀ t,
      wedgeMap t∈Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) → dotDual q t=0 := by
  simp only [dualRelations,Submodule.mem_comap,Submodule.mem_dualAnnihilator,
    originalRelations]

theorem skew_mem_dualRelations (f g : ⋀[K]^2 (ν → K))
    (a : Coordinates (K := K) (ν := ν))
    (ha : bracketMap (bracketData f g) a=0) : skew a∈dualRelations f g := by
  rw [bracketMap_eq_coefficientDual] at ha
  have hf : coefficientDual a f=0 := congrArg Prod.fst ha
  have hg : coefficientDual a g=0 := congrArg Prod.snd ha
  apply (mem_dualRelations f g _).mpr
  intro t ht
  rw [← coefficientDual_wedge]
  have hker : Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) ≤
      LinearMap.ker (coefficientDual a) := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with rfl | rfl
    · exact hf
    · exact hg
  exact hker ht

/-- Every ordinary dual quadratic relation is an actual commutator
coefficient vector whose bracket direction vanishes. -/
theorem mem_dualRelations_iff (f g : ⋀[K]^2 (ν → K))
    (q : Coordinates (K := K) (ν := ν)) :
    q∈dualRelations f g ↔ ∃ a, bracketMap (bracketData f g) a=0 ∧ skew a=q := by
  constructor
  · intro hq
    have hq' := (mem_dualRelations f g q).mp hq
    have hskew (i j : ν) : q (i,j)+q (j,i)=0 := by
      have h := hq' (Pi.basisFun K (ν × ν) (i,j)+Pi.basisFun K (ν × ν) (j,i))
        (by rw [wedgeMap_symmetric]; exact Submodule.zero_mem _)
      simpa only [map_add,dotDual_basis_right] using h
    let a : Coordinates (K := K) (ν := ν) := (2 : K)⁻¹ • q
    have haq : skew a=q := by
      funext p
      rcases p with ⟨i,j⟩
      change (2 : K)⁻¹*q (i,j)-(2 : K)⁻¹*q (j,i)=q (i,j)
      have hs := hskew i j
      field_simp
      linear_combination -hs
    refine ⟨a,?_,haq⟩
    rw [bracketMap_eq_coefficientDual]
    apply Prod.ext
    · obtain ⟨t,ht⟩ := wedgeMap_surjective (K := K) (ν := ν) f
      have h := hq' t (by rw [ht]; exact Submodule.subset_span (by simp))
      rw [← haq,← coefficientDual_wedge,ht] at h
      exact h
    · obtain ⟨t,ht⟩ := wedgeMap_surjective (K := K) (ν := ν) g
      have h := hq' t (by rw [ht]; exact Submodule.subset_span (by simp))
      rw [← haq,← coefficientDual_wedge,ht] at h
      exact h
  · rintro ⟨a,ha,rfl⟩
    exact skew_mem_dualRelations f g a ha

theorem wordMap_skew (a : Coordinates (K := K) (ν := ν)) :
    wordMap (skew a)=commutatorMap (FreeAlgebra.ι K) a := by
  have h : (wordMap (K := K) (ν := ν)).comp (skew (K := K) (ν := ν))=
      commutatorMap (FreeAlgebra.ι K : ν → FreeAlgebra K ν) := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    have hs : skew (Pi.basisFun K (ν × ν) (i,j))=
        Pi.basisFun K (ν × ν) (i,j)-Pi.basisFun K (ν × ν) (j,i) := by
      funext p
      rcases p with ⟨u,v⟩
      simp [skew_apply,Pi.basisFun_apply,Pi.single_apply,Prod.mk.injEq,and_comm]
    rw [LinearMap.comp_apply,hs,map_sub]
    simp only [wordMap,commutatorMap,Module.Basis.constr_basis,
      QuadraticCommutatorQuotient.commutator]
  exact LinearMap.congr_fun h a

inductive DualRelation (f g : ⋀[K]^2 (ν → K)) : FreeAlgebra K ν → FreeAlgebra K ν → Prop
  | annihilator (q : Coordinates (K := K) (ν := ν)) (hq : q∈dualRelations f g) :
      DualRelation f g (wordMap q) 0

/-- The ordinary quadratic dual in tensor-square coordinates. -/
abbrev QuadraticDual (f g : ⋀[K]^2 (ν → K)) := RingQuot (DualRelation f g)

theorem definingRelations_eq (f g : ⋀[K]^2 (ν → K)) :
    QuadraticCommutatorQuotient.Relation (bracketData f g)=DualRelation f g := by
  funext x y
  apply propext
  constructor
  · intro h
    cases h with
    | kernel a ha =>
        rw [← wordMap_skew]
        exact DualRelation.annihilator (skew a) (skew_mem_dualRelations f g a ha)
  · intro h
    cases h with
    | annihilator q hq =>
        obtain ⟨a,ha,rfl⟩ := (mem_dualRelations_iff f g q).mp hq
        rw [wordMap_skew]
        exact QuadraticCommutatorQuotient.Relation.kernel a ha

def quotientRelEquiv
    {r s : FreeAlgebra K ν → FreeAlgebra K ν → Prop} (h : r=s) :
    RingQuot r ≃ₐ[K] RingQuot s := by
  cases h
  exact AlgEquiv.refl

theorem quotientRelEquiv_mk
    {r s : FreeAlgebra K ν → FreeAlgebra K ν → Prop} (h : r=s)
    (x : FreeAlgebra K ν) :
    quotientRelEquiv h (RingQuot.mkAlgHom K r x)=RingQuot.mkAlgHom K s x := by
  cases h
  rfl

def commutatorEquiv (f g : ⋀[K]^2 (ν → K)) :
    QuadraticDual f g ≃ₐ[K] QuadraticCommutatorQuotient.Algebra (bracketData f g) :=
  quotientRelEquiv (definingRelations_eq f g).symm

@[simp] theorem commutatorEquiv_mk (f g : ⋀[K]^2 (ν → K))
    (x : FreeAlgebra K ν) :
    commutatorEquiv f g (RingQuot.mkAlgHom K (DualRelation f g) x)=
      QuadraticCommutatorQuotient.quotientMap (bracketData f g) x :=
  quotientRelEquiv_mk (definingRelations_eq f g).symm x

variable [Nonempty ν]

/-- The conventional annihilator-defined quadratic dual is isomorphic to
the genuine enveloping algebra of the actual ordinary two-step Lie
algebra, whenever the actual cubic wedge map is injective. -/
def quadraticDualEnvelopingEquiv (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    QuadraticDual f g ≃ₐ[K]
      UniversalEnvelopingAlgebra K (TwoStepCentralLie.LieSpace (bracketData f g)) :=
  (commutatorEquiv f g).trans (actualCommutatorEnvelopingEquiv f g hinj)

@[simp] theorem quadraticDualEnvelopingEquiv_generator
    (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) (i : ν) :
    quadraticDualEnvelopingEquiv f g hinj
      (RingQuot.mkAlgHom K (DualRelation f g) (FreeAlgebra.ι K i))=
      UniversalEnvelopingAlgebra.ι K
        (TwoStepCentralLie.generator (bracketData f g) (Pi.basisFun K ν i)) := by
  rw [quadraticDualEnvelopingEquiv,AlgEquiv.trans_apply,commutatorEquiv_mk]
  exact QuadraticCommutatorQuotient.toEnveloping_X (bracketData f g) i

end PaperVerification.AlternatingForms.QuadraticDual
