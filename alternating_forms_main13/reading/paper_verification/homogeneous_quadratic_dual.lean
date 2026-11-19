module

public import PaperVerification.HomogeneousMultiplicationRows
public import PaperVerification.BarQuadraticPairing
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis

/-!
# The multiplication-row quotient is the conventional quadratic dual

The intrinsic dual is the actual tensor algebra on the actual degree-one
dual, modulo the annihilator of actual multiplication. It does not depend
on a choice of homogeneous basis. The proved comparison with the literal
multiplication-row quotient preserves generators and all their powers.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct Pointwise

namespace PaperVerification.HomogeneousQuadraticDual

section QuotientTransport
variable {K A D : Type*} [Field K] [Ring A] [Algebra K A] [Ring D] [Algebra K D]

theorem relation_iff (S : Submodule K A) (x y : A) :
    QuadraticWordFunctionals.Relation S x y ↔ x∈S ∧ y=0 := by
  constructor
  · intro h
    cases h
    exact ⟨by assumption,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact QuadraticWordFunctionals.Relation.relation x hx

def ofRelationEq {r s : A → A → Prop} (h : r=s) : RingQuot r ≃ₐ[K] RingQuot s := by
  cases h
  exact AlgEquiv.refl

@[simp] theorem ofRelationEq_mk {r s : A → A → Prop} (h : r=s) (x : A) :
    ofRelationEq (K := K) h (RingQuot.mkAlgHom K r x)=RingQuot.mkAlgHom K s x := by
  cases h
  rfl

theorem transported_relation (e : A ≃ₐ[K] D) (S : Submodule K A) :
    (fun x y : D => QuadraticWordFunctionals.Relation S (e.symm x) (e.symm y))=
      QuadraticWordFunctionals.Relation (S.map e.toLinearMap) := by
  funext x y
  apply propext
  rw [relation_iff,relation_iff,Submodule.mem_map_equiv (e := e.toLinearEquiv)]
  change (e.symm x∈S ∧ e.symm y=0) ↔ (e.symm x∈S ∧ y=0)
  exact and_congr_right (fun _ => e.symm.toRingEquiv.map_eq_zero_iff)

def quotientEquivMap (e : A ≃ₐ[K] D) (S : Submodule K A) :
    QuadraticWordFunctionals.Quotient S ≃ₐ[K]
      QuadraticWordFunctionals.Quotient (S.map e.toLinearMap) :=
  (RingQuot.algEquivQuotAlgEquiv e (QuadraticWordFunctionals.Relation S)).trans
    (ofRelationEq (transported_relation e S))

@[simp] theorem quotientEquivMap_mk (e : A ≃ₐ[K] D) (S : Submodule K A) (x : A) :
    quotientEquivMap e S (QuadraticWordFunctionals.quotientMap S x)=
      QuadraticWordFunctionals.quotientMap (S.map e.toLinearMap) (e x) := by
  simp only [quotientEquivMap,QuadraticWordFunctionals.quotientMap,AlgEquiv.trans_apply,
    RingQuot.algEquivQuotAlgEquiv,AlgEquiv.ofAlgHom_apply,
    RingQuot.liftAlgHom_mkAlgHom_apply,AlgHom.comp_apply,AlgEquiv.toAlgHom_apply,
    ofRelationEq_mk]

def ofSubmoduleEq {S T : Submodule K A} (h : S=T) :
    QuadraticWordFunctionals.Quotient S ≃ₐ[K] QuadraticWordFunctionals.Quotient T := by
  cases h
  exact AlgEquiv.refl

@[simp] theorem ofSubmoduleEq_mk {S T : Submodule K A} (h : S=T) (x : A) :
    ofSubmoduleEq h (QuadraticWordFunctionals.quotientMap S x)=
      QuadraticWordFunctionals.quotientMap T x := by
  cases h
  rfl
end QuotientTransport

section TensorInclusion
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The genuine degree-two inclusion in the tensor algebra. -/
def quadraticInclusion : (V ⊗[K] V) →ₗ[K] TensorAlgebra K V :=
  TensorProduct.lift ((LinearMap.mul K (TensorAlgebra K V)).compl₁₂
    (TensorAlgebra.ι K) (TensorAlgebra.ι K))

@[simp] theorem quadraticInclusion_tmul (x y : V) :
    quadraticInclusion (x ⊗ₜ[K] y)=TensorAlgebra.ι K x*TensorAlgebra.ι K y := rfl
end TensorInclusion

section Intrinsic
universe u
variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  (G : TauCeti.InternalGrading K A ℕ)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

/-- Conventional annihilator of the actual quadratic multiplication kernel. -/
def dualRelations : Submodule K (Module.Dual K (G.piece 1) ⊗[K] Module.Dual K (G.piece 1)) :=
  (LinearMap.ker (HomogeneousMultiplicationRows.multiplication G hmul)).dualAnnihilator.comap
    (TensorProduct.dualDistrib K (G.piece 1) (G.piece 1))

def tensorRelationSpace : Submodule K (TensorAlgebra K (Module.Dual K (G.piece 1))) :=
  (dualRelations G hmul).map
    (quadraticInclusion (K := K) (V := Module.Dual K (G.piece 1)))

/-- The actual tensor-algebra quadratic dual, independent of B and δ. -/
abbrev conventionalDual := QuadraticWordFunctionals.Quotient (tensorRelationSpace G hmul)

def generatorMap : Module.Dual K (G.piece 1) →ₗ[K] conventionalDual G hmul :=
  (QuadraticWordFunctionals.quotientMap (tensorRelationSpace G hmul)).toLinearMap.comp
    (TensorAlgebra.ι K)

def wordPiece (n : ℕ) : Submodule K (conventionalDual G hmul) :=
  (generatorMap G hmul).range^n
end Intrinsic

section Coordinates
universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i))
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

local notation "J₁" => DiagonalBarWords.DegreeOne δ
local notation "J₂" => DiagonalBarWords.DegreeTwo δ
local notation "b" => (FreeAlgebraWordDegree.basis (K := K) (J := J₁))

def coordinateEquiv : TensorAlgebra K (Module.Dual K (G.piece 1)) ≃ₐ[K] FreeAlgebra K J₁ :=
  TensorAlgebra.equivFreeAlgebra
    (HomogeneousMultiplicationRows.homogeneousBasis G B δ hzero hunit hhom 1 (by decide)).dualBasis

theorem freeWord_pair (a d : J₁) :
    b [a,d]=FreeAlgebra.ι K a*FreeAlgebra.ι K d := by
  change b ([a]++[d])=_
  rw [FreeAlgebraWordDegree.basis_append,FreeAlgebraWordDegree.basis_singleton,
    FreeAlgebraWordDegree.basis_singleton]

/-- Literal row tensors map to the independently defined free-algebra rows. -/
theorem tensorRow_image (c : J₂) :
    coordinateEquiv G B δ hzero hunit hhom
        (quadraticInclusion (HomogeneousMultiplicationRows.tensorRow G B δ hzero hunit hhom c))=
      BarQuadraticPairing.rowRelation B δ c := by
  simp only [HomogeneousMultiplicationRows.tensorRow,map_sum,map_smul,
    quadraticInclusion_tmul,map_mul,coordinateEquiv,
    TensorAlgebra.equivFreeAlgebra_ι_apply,BarQuadraticPairing.rowRelation,freeWord_pair]

theorem tensorRelationSpace_image_eq :
    (tensorRelationSpace G hmul).map (coordinateEquiv G B δ hzero hunit hhom).toLinearMap=
      BarQuadraticPairing.relationSpace B δ := by
  rw [tensorRelationSpace,dualRelations,
    ←HomogeneousMultiplicationRows.tensorRow_span_eq_actual_annihilator G B δ hzero hunit hhom hmul,
    ←Submodule.map_comp,Submodule.map_span,←Set.range_comp]
  change Submodule.span K (Set.range (fun c : J₂ =>
      coordinateEquiv G B δ hzero hunit hhom
        (quadraticInclusion (HomogeneousMultiplicationRows.tensorRow G B δ hzero hunit hhom c))))=
    Submodule.span K (Set.range (BarQuadraticPairing.rowRelation B δ))
  apply congrArg (Submodule.span K)
  apply congrArg Set.range
  funext c
  exact tensorRow_image G B δ hzero hunit hhom c

/-- A genuine algebra equivalence from the conventional dual to the row quotient. -/
def rowQuotientEquiv : conventionalDual G hmul ≃ₐ[K]
    QuadraticWordFunctionals.Quotient (BarQuadraticPairing.relationSpace B δ) :=
  (quotientEquivMap (coordinateEquiv G B δ hzero hunit hhom)
    (tensorRelationSpace G hmul)).trans
      (ofSubmoduleEq (tensorRelationSpace_image_eq G B δ hzero hunit hhom hmul))

@[simp] theorem rowQuotientEquiv_generator (i : J₁) :
    rowQuotientEquiv G B δ hzero hunit hhom hmul
        (generatorMap G hmul
          ((HomogeneousMultiplicationRows.homogeneousBasis G B δ hzero hunit hhom 1
            (by decide)).dualBasis i))=
      QuadraticWordFunctionals.quotientMap (BarQuadraticPairing.relationSpace B δ)
        (FreeAlgebra.ι K i) := by
  simp only [rowQuotientEquiv,AlgEquiv.trans_apply,generatorMap,LinearMap.comp_apply,
    AlgHom.toLinearMap_apply,quotientEquivMap_mk,ofSubmoduleEq_mk,coordinateEquiv,
    TensorAlgebra.equivFreeAlgebra_ι_apply]

theorem generatorSpace_transport :
    (generatorMap G hmul).range.map (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap=
      QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) 1 := by
  rw [←LinearMap.range_comp]
  let b₁ := (HomogeneousMultiplicationRows.homogeneousBasis G B δ hzero hunit hhom 1
    (by decide)).dualBasis
  let L := (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap.comp
    (generatorMap G hmul)
  change LinearMap.range L=_
  calc
    LinearMap.range L=(Submodule.span K (Set.range b₁)).map L := by
      rw [b₁.span_eq,Submodule.map_top]
    _ = Submodule.span K (Set.range (fun i : J₁ =>
        QuadraticWordFunctionals.quotientMap (BarQuadraticPairing.relationSpace B δ)
          (FreeAlgebra.ι K i))) := by
      rw [Submodule.map_span,←Set.range_comp]
      apply congrArg (Submodule.span K)
      apply congrArg Set.range
      funext i
      exact rowQuotientEquiv_generator G B δ hzero hunit hhom hmul i
    _ = QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) 1 := by
      rw [QuadraticWordFunctionals.quotientPiece,FreeAlgebraWordDegree.degreeSpace_one,
        FreeAlgebraWordDegree.generatorSpace,Submodule.map_span,←Set.range_comp]
      rfl

/-- Every natural generator degree is preserved, including degree zero. -/
theorem wordPiece_transport (n : ℕ) :
    (wordPiece G hmul n).map (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap=
      QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) n := by
  change ((generatorMap G hmul).range^n).map
    (rowQuotientEquiv G B δ hzero hunit hhom hmul).toAlgHom.toLinearMap=_
  rw [Submodule.map_pow]
  change ((generatorMap G hmul).range.map
    (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap)^n = _
  rw [generatorSpace_transport]
  exact (QuadraticWordFunctionals.quotientPiece_eq_power b
    FreeAlgebraWordDegree.basis_append FreeAlgebraWordDegree.basis_nil
    (BarQuadraticPairing.relationSpace B δ) n).symm

def rowDegreeEquiv (n : ℕ) : wordPiece G hmul n ≃ₗ[K]
    QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) n :=
  (Submodule.equivMapOfInjective
    (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap
    (rowQuotientEquiv G B δ hzero hunit hhom hmul).injective (wordPiece G hmul n)).trans
      (LinearEquiv.ofEq _ _ (wordPiece_transport G B δ hzero hunit hhom hmul n))

include hzero hunit hhom in
theorem degree_finrank_eq (n : ℕ) :
    Module.finrank K (wordPiece G hmul n)=
      Module.finrank K
        (QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) n) :=
  (rowDegreeEquiv G B δ hzero hunit hhom hmul n).finrank_eq
end Coordinates

end PaperVerification.HomogeneousQuadraticDual
