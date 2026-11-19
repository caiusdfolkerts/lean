module

public import PaperVerification.AlternatingFormsExteriorAugmentation
public import PaperVerification.AlternatingFormsQuadraticDualTensor

/-!
# The actual exterior quotient multiplication kernel

The generator map is the original exterior inclusion followed by the
literal quotient map. Its tensor-square multiplication is proved to factor
through the ordinary wedge map. The kernel is exactly the inverse image
of the span of the two given forms, and the actual dual-tensor annihilator
is exactly the relation space used by the quadratic dual. No genericity,
rank, or Koszul premise enters these comparisons.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.AlternatingForms.QuadraticDual

universe u
variable {K ν : Type u} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]
  (f g : ⋀[K]^2 (ν → K))

/-- The actual degree-one generators in the original ring quotient. -/
def actualGenerator : (ν → K) →ₗ[K] ExteriorAugmented.Quotient f g :=
  (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)).toLinearMap.comp (ExteriorAlgebra.ι K)

@[simp] theorem actualGenerator_apply (v : ν → K) :
    actualGenerator f g v=
      Ideal.Quotient.mk (exteriorRelationIdeal f g) (ExteriorAlgebra.ι K v) := rfl

theorem actualGenerator_injective : Function.Injective (actualGenerator f g) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  change actualGenerator f g v=0 at hv
  have hι : ExteriorAlgebra.ι K v∈(⋀[K]^1 (ν → K)) := by
    rw [ExteriorAlgebra.exteriorPower,pow_one]
    exact ⟨v,rfl⟩
  have hrel : (⟨ExteriorAlgebra.ι K v,hι⟩ : ⋀[K]^1 (ν → K))∈
      exteriorDegreeRelations f g 1 := by
    change ExteriorAlgebra.ι K v∈exteriorRelationIdeal f g
    exact Ideal.Quotient.eq_zero_iff_mem.mp hv
  rw [exteriorDegreeRelations_eq_bot f g (by decide)] at hrel
  have hz : ExteriorAlgebra.ι K v=0 := congrArg Subtype.val ((Submodule.mem_bot K).mp hrel)
  exact (Submodule.mem_bot K).mpr ((ExteriorAlgebra.ι_eq_zero_iff v).mp hz)

theorem actualGenerator_range :
    LinearMap.range (actualGenerator f g)=(ExteriorAugmented.grading f g).piece 1 := by
  rw [ExteriorAugmented.grading_piece,ExteriorAlgebra.exteriorPower,pow_one,
    actualGenerator,LinearMap.range_comp]

def actualDegreeOneEquiv : (ν → K) ≃ₗ[K] (ExteriorAugmented.grading f g).piece 1 :=
  (LinearEquiv.ofInjective (actualGenerator f g) (actualGenerator_injective f g)).trans
    (LinearEquiv.ofEq _ _ (actualGenerator_range f g))

@[simp] theorem actualDegreeOneEquiv_apply (v : ν → K) :
    (actualDegreeOneEquiv f g v : ExteriorAugmented.Quotient f g)=actualGenerator f g v := rfl

/-- The ordinary multiplication of the actual degree-one generators. -/
def actualQuadraticMultiplication :
    ((ν → K) ⊗[K] (ν → K)) →ₗ[K] ExteriorAugmented.Quotient f g :=
  TensorProduct.lift
    ((LinearMap.mul K (ExteriorAugmented.Quotient f g)).compl₁₂
      (actualGenerator f g) (actualGenerator f g))

@[simp] theorem actualQuadraticMultiplication_tmul (v w : ν → K) :
    actualQuadraticMultiplication f g (v ⊗ₜ[K] w)=
      actualGenerator f g v*actualGenerator f g w := rfl

/-- The literal inclusion of degree two followed by the original quotient. -/
def actualDegreeTwoProjection :
    (⋀[K]^2 (ν → K)) →ₗ[K] ExteriorAugmented.Quotient f g :=
  (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)).toLinearMap.comp
    (Submodule.subtype (⋀[K]^2 (ν → K)))

@[simp] theorem actualDegreeTwoProjection_apply (x : ⋀[K]^2 (ν → K)) :
    actualDegreeTwoProjection f g x=
      Ideal.Quotient.mk (exteriorRelationIdeal f g) (x : ExteriorAlgebra K (ν → K)) := rfl

theorem actualDegreeTwoProjection_range :
    LinearMap.range (actualDegreeTwoProjection f g)=(ExteriorAugmented.grading f g).piece 2 := by
  rw [ExteriorAugmented.grading_piece,actualDegreeTwoProjection,
    LinearMap.range_comp,Submodule.range_subtype]

/-- The degree-two kernel is proved from the actual homogeneous ideal. -/
theorem actualDegreeTwoProjection_ker :
    LinearMap.ker (actualDegreeTwoProjection f g)=
      Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) := by
  ext x
  change (Ideal.Quotient.mk (exteriorRelationIdeal f g)
    (x : ExteriorAlgebra K (ν → K))=0) ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change x∈exteriorDegreeRelations f g 2 ↔ _
  rw [exterior_degree_two_relations]

@[simp] theorem tensorCoordinates_basis (i j : ν) :
    tensorCoordinates (Pi.basisFun K ν i ⊗ₜ[K] Pi.basisFun K ν j)=
      Pi.basisFun K (ν × ν) (i,j) := by
  ext p
  rcases p with ⟨a,b⟩
  simp only [tensorCoordinates_tmul,Pi.basisFun_apply,Pi.single_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The wedge comparison is an identity between independently defined maps. -/
theorem actualQuadraticMultiplication_eq :
    actualQuadraticMultiplication f g=
      (actualDegreeTwoProjection f g).comp
        (wedgeMap.comp (tensorCoordinates (K := K) (ν := ν)).toLinearMap) := by
  apply ((Pi.basisFun K ν).tensorProduct (Pi.basisFun K ν)).ext
  rintro ⟨i,j⟩
  simp only [Module.Basis.tensorProduct_apply,actualQuadraticMultiplication_tmul,
    LinearMap.comp_apply,LinearEquiv.coe_coe,tensorCoordinates_basis,wedgeMap_basis,
    actualDegreeTwoProjection_apply,actualGenerator_apply]
  rw [←map_mul]
  congr 1
  simp only [exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply,Matrix.vecTail,Matrix.cons_val_zero,
    Matrix.cons_val_one,mul_one]
  rfl

/-- Products of the actual generators span exactly the original degree-two piece. -/
theorem actualQuadraticMultiplication_range :
    LinearMap.range (actualQuadraticMultiplication f g)=(ExteriorAugmented.grading f g).piece 2 := by
  have hs : Function.Surjective
      (wedgeMap.comp (tensorCoordinates (K := K) (ν := ν)).toLinearMap) :=
    (wedgeMap_surjective (K := K) (ν := ν)).comp
      (tensorCoordinates (K := K) (ν := ν)).surjective
  rw [actualQuadraticMultiplication_eq,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hs,Submodule.map_top,actualDegreeTwoProjection_range]

/-- The kernel condition in literal tensor coordinates. -/
theorem actualQuadraticMultiplication_eq_zero_iff
    (z : (ν → K) ⊗[K] (ν → K)) :
    actualQuadraticMultiplication f g z=0 ↔
      wedgeMap (tensorCoordinates z)∈
        Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) := by
  rw [actualQuadraticMultiplication_eq]
  change actualDegreeTwoProjection f g (wedgeMap (tensorCoordinates z))=0 ↔ _
  rw [←LinearMap.mem_ker,actualDegreeTwoProjection_ker]

/-- The actual tensor-square multiplication kernel is exactly the relation
space used by the quadratic dual, under the proved tensor coordinates. -/
theorem actualQuadraticMultiplication_ker :
    LinearMap.ker (actualQuadraticMultiplication f g)=
      (originalRelations f g).comap (tensorCoordinates (K := K) (ν := ν)).toLinearMap := by
  ext z
  exact actualQuadraticMultiplication_eq_zero_iff f g z

theorem actualQuadraticMultiplication_ker_coordinates :
    (LinearMap.ker (actualQuadraticMultiplication f g)).map
        (tensorCoordinates (K := K) (ν := ν)).toLinearMap=originalRelations f g := by
  rw [actualQuadraticMultiplication_ker]
  exact Submodule.map_comap_eq_of_surjective
    (tensorCoordinates (K := K) (ν := ν)).surjective (originalRelations f g)

/-- The independent canonical tensor evaluation pairing, applied to the
annihilator of actual multiplication relations. -/
def actualTensorDualRelations :
    Submodule K (Module.Dual K (ν → K) ⊗[K] Module.Dual K (ν → K)) :=
  (LinearMap.ker (actualQuadraticMultiplication f g)).dualAnnihilator.comap
    (TensorProduct.dualDistrib K (ν → K) (ν → K))

/-- Coordinate dual relations are the annihilator of literal multiplication,
not a relation space chosen solely to obtain a desired Hilbert series. -/
theorem mem_dualRelations_iff_actual_multiplication
    (q : Coordinates (K := K) (ν := ν)) :
    q∈dualRelations f g ↔
      ∀ z : (ν → K) ⊗[K] (ν → K),actualQuadraticMultiplication f g z=0 →
        TensorProduct.dualDistrib K (ν → K) (ν → K) (dualTensorCoordinates.symm q) z=0 := by
  rw [mem_dualRelations_actual]
  simp only [actualQuadraticMultiplication_eq_zero_iff]

/-- Equality of submodules in the actual tensor square of the actual dual
space, with no self-duality convention or nondegeneracy assumption. -/
theorem actualTensorDualRelations_eq :
    actualTensorDualRelations f g=
      (dualRelations f g).comap (dualTensorCoordinates (K := K) (ν := ν)).toLinearMap := by
  ext q
  simp only [actualTensorDualRelations,Submodule.mem_comap,Submodule.mem_dualAnnihilator]
  rw [mem_dualRelations_iff_actual_multiplication]
  simp only [LinearMap.mem_ker,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

end PaperVerification.AlternatingForms.QuadraticDual
