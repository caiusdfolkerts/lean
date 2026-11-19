module

public import PaperVerification.AlternatingFormsIntrinsicTensorFunctor
public import PaperVerification.AlternatingFormsActualQuadraticKernel
public import PaperVerification.AlternatingFormsQuadraticDualTensorHilbert

/-!
# The intrinsic quadratic dual of the actual exterior quotient

The actual degree-one equivalence induces the dual tensor and tensor-algebra
maps. The canonical evaluation pairing transports the annihilator of the
actual multiplication kernel to the original exterior relation annihilator.
The resulting ordinary quotient equivalence preserves the original generator
map, every generator power, and therefore every Hilbert coefficient.
No genericity, rank, or Koszul hypothesis enters this identification.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct PowerSeries

namespace PaperVerification.AlternatingForms.IntrinsicQuadraticDual

open HomogeneousQuadraticDual HomogeneousMultiplicationRows


universe u
variable {K ν : Type u} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
  (f g : ⋀[K]^2 (ν → K))

local notation "G" => ExteriorAugmented.grading f g
local notation "hmul" => ExteriorAugmented.grading_mul f g

def primalTensorEquiv :
    ((ν → K) ⊗[K] (ν → K)) ≃ₗ[K] ((G).piece 1 ⊗[K] (G).piece 1) :=
  TensorProduct.congr (QuadraticDual.actualDegreeOneEquiv f g)
    (QuadraticDual.actualDegreeOneEquiv f g)

def dualGeneratorEquiv : Module.Dual K ((G).piece 1) ≃ₗ[K] Module.Dual K (ν → K) :=
  (QuadraticDual.actualDegreeOneEquiv f g).dualMap

def dualTensorEquiv :
    (Module.Dual K ((G).piece 1) ⊗[K] Module.Dual K ((G).piece 1)) ≃ₗ[K]
      (Module.Dual K (ν → K) ⊗[K] Module.Dual K (ν → K)) :=
  TensorProduct.congr (dualGeneratorEquiv f g) (dualGeneratorEquiv f g)

/-- The independent actual multiplication maps agree on the original generators. -/
theorem multiplication_transport (z : (ν → K) ⊗[K] (ν → K)) :
    (HomogeneousMultiplicationRows.multiplication G hmul (primalTensorEquiv f g z) :
      ExteriorAugmented.Quotient f g)=QuadraticDual.actualQuadraticMultiplication f g z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [(primalTensorEquiv f g).map_zero,
        (HomogeneousMultiplicationRows.multiplication G hmul).map_zero,
        (QuadraticDual.actualQuadraticMultiplication f g).map_zero]
      rfl
  | tmul x y =>
      simp only [primalTensorEquiv,TensorProduct.congr_tmul,
        HomogeneousMultiplicationRows.multiplication_tmul_val,
        QuadraticDual.actualDegreeOneEquiv_apply,QuadraticDual.actualQuadraticMultiplication_tmul]
  | add z w hz hw => simp only [map_add,Submodule.coe_add,hz,hw]

theorem multiplication_zero_iff (z : (ν → K) ⊗[K] (ν → K)) :
    HomogeneousMultiplicationRows.multiplication G hmul (primalTensorEquiv f g z)=0 ↔
      QuadraticDual.actualQuadraticMultiplication f g z=0 := by
  constructor
  · intro h
    exact (multiplication_transport f g z).symm.trans (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (multiplication_transport f g z).trans h

theorem pairing_transport
    (q : Module.Dual K ((G).piece 1) ⊗[K] Module.Dual K ((G).piece 1))
    (z : (ν → K) ⊗[K] (ν → K)) :
    TensorProduct.dualDistrib K (ν → K) (ν → K) (dualTensorEquiv f g q) z=
      TensorProduct.dualDistrib K ((G).piece 1) ((G).piece 1) q (primalTensorEquiv f g z) :=
  tensorDual_pairing (QuadraticDual.actualDegreeOneEquiv f g) q z

/-- Exact annihilator transport, not an assumed quadratic-dual identification. -/
theorem mem_dualRelations_iff
    (q : Module.Dual K ((G).piece 1) ⊗[K] Module.Dual K ((G).piece 1)) :
    q∈HomogeneousQuadraticDual.dualRelations G hmul ↔
      dualTensorEquiv f g q∈QuadraticDual.actualTensorDualRelations f g := by
  simp only [HomogeneousQuadraticDual.dualRelations,QuadraticDual.actualTensorDualRelations,
    Submodule.mem_comap,Submodule.mem_dualAnnihilator,LinearMap.mem_ker]
  constructor
  · intro h z hz
    rw [pairing_transport]
    exact h (primalTensorEquiv f g z) ((multiplication_zero_iff f g z).mpr hz)
  · intro h z hz
    obtain ⟨w,rfl⟩ := (primalTensorEquiv f g).surjective z
    rw [←pairing_transport]
    exact h w ((multiplication_zero_iff f g w).mp hz)

theorem dualRelations_image :
    (HomogeneousQuadraticDual.dualRelations G hmul).map (dualTensorEquiv f g).toLinearMap=
      QuadraticDual.actualTensorDualRelations f g := by
  ext q
  rw [Submodule.mem_map_equiv]
  simpa only [LinearEquiv.apply_symm_apply] using
    (mem_dualRelations_iff f g ((dualTensorEquiv f g).symm q))

def originalTensorAlgebraEquiv :
    TensorAlgebra K (Module.Dual K ((G).piece 1)) ≃ₐ[K]
      TensorAlgebra K (Module.Dual K (ν → K)) :=
  tensorAlgebraCongr (dualGeneratorEquiv f g)

theorem originalTensorAlgebraEquiv_quadratic :
    (originalTensorAlgebraEquiv f g).toLinearMap.comp
        (HomogeneousQuadraticDual.quadraticInclusion (K := K)
          (V := Module.Dual K ((G).piece 1)))=
      QuadraticDual.tensorQuadraticInclusion.comp (dualTensorEquiv f g).toLinearMap :=
  tensorAlgebraCongr_quadratic (dualGeneratorEquiv f g)

theorem tensorRelationSpace_image :
    (HomogeneousQuadraticDual.tensorRelationSpace G hmul).map
        (originalTensorAlgebraEquiv f g).toLinearMap=
      (QuadraticDual.dualRelations f g).map QuadraticDual.tensorWordMap := by
  rw [HomogeneousQuadraticDual.tensorRelationSpace,←Submodule.map_comp,
    originalTensorAlgebraEquiv_quadratic,Submodule.map_comp,dualRelations_image,
    QuadraticDual.actualTensorDualRelations_eq,Submodule.comap_equiv_eq_map_symm,
    ←Submodule.map_comp,←QuadraticDual.tensorWordMap_eq_actual_inclusion]

/-- The coordinate-generated tensor relations and the submodule relation
presentation define exactly the same ordinary relation. -/
theorem originalTensorRelation_eq :
    QuadraticWordFunctionals.Relation
        ((QuadraticDual.dualRelations f g).map QuadraticDual.tensorWordMap)=
      QuadraticDual.TensorDualRelation f g := by
  funext x y
  apply propext
  rw [HomogeneousQuadraticDual.relation_iff]
  constructor
  · rintro ⟨hx,rfl⟩
    obtain ⟨q,hq,rfl⟩ := hx
    exact QuadraticDual.TensorDualRelation.annihilator q hq
  · intro h
    cases h with
    | annihilator q hq => exact ⟨⟨q,hq,rfl⟩,rfl⟩

/-- Actual algebra equivalence from the intrinsic dual of A to the original
annihilator presentation. Every relation and both inverse laws are proved. -/
def intrinsicTensorEquiv : HomogeneousQuadraticDual.conventionalDual G hmul ≃ₐ[K]
    QuadraticDual.TensorQuadraticDual f g :=
  ((HomogeneousQuadraticDual.quotientEquivMap (originalTensorAlgebraEquiv f g)
      (HomogeneousQuadraticDual.tensorRelationSpace G hmul)).trans
    (HomogeneousQuadraticDual.ofSubmoduleEq (tensorRelationSpace_image f g))).trans
      (HomogeneousQuadraticDual.ofRelationEq (originalTensorRelation_eq f g))

@[simp] theorem intrinsicTensorEquiv_generator (φ : Module.Dual K ((G).piece 1)) :
    intrinsicTensorEquiv f g (HomogeneousQuadraticDual.generatorMap G hmul φ)=
      QuadraticDual.tensorGeneratorMap f g (dualGeneratorEquiv f g φ) := by
  simp only [intrinsicTensorEquiv,AlgEquiv.trans_apply,
    HomogeneousQuadraticDual.generatorMap,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
    HomogeneousQuadraticDual.quotientEquivMap_mk,HomogeneousQuadraticDual.ofSubmoduleEq_mk,
    HomogeneousQuadraticDual.ofRelationEq_mk,originalTensorAlgebraEquiv,tensorAlgebraCongr_ι,
    QuadraticDual.tensorGeneratorMap]
  simp only [QuadraticWordFunctionals.quotientMap,HomogeneousQuadraticDual.ofRelationEq_mk]

theorem generatorMap_transport :
    (intrinsicTensorEquiv f g).toLinearMap.comp (HomogeneousQuadraticDual.generatorMap G hmul)=
      (QuadraticDual.tensorGeneratorMap f g).comp (dualGeneratorEquiv f g).toLinearMap := by
  apply LinearMap.ext
  intro φ
  exact intrinsicTensorEquiv_generator f g φ

/-- All original generator powers are transported, including degree zero. -/
theorem wordPiece_transport (n : ℕ) :
    (HomogeneousQuadraticDual.wordPiece G hmul n).map (intrinsicTensorEquiv f g).toLinearMap=
      QuadraticDual.tensorWordPiece f g n := by
  change ((HomogeneousQuadraticDual.generatorMap G hmul).range^n).map
    (intrinsicTensorEquiv f g).toAlgHom.toLinearMap=_
  rw [Submodule.map_pow]
  change ((HomogeneousQuadraticDual.generatorMap G hmul).range.map
    (intrinsicTensorEquiv f g).toLinearMap)^n=_
  rw [←LinearMap.range_comp,generatorMap_transport,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (dualGeneratorEquiv f g).surjective,Submodule.map_top]
  rfl

def degreeEquiv (n : ℕ) : HomogeneousQuadraticDual.wordPiece G hmul n ≃ₗ[K]
    QuadraticDual.tensorWordPiece f g n :=
  (Submodule.equivMapOfInjective (intrinsicTensorEquiv f g).toLinearMap
    (intrinsicTensorEquiv f g).injective (HomogeneousQuadraticDual.wordPiece G hmul n)).trans
      (LinearEquiv.ofEq _ _ (wordPiece_transport f g n))

theorem degree_finrank_eq (n : ℕ) :
    Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul n)=
      Module.finrank K (QuadraticDual.tensorWordPiece f g n) :=
  (degreeEquiv f g n).finrank_eq

/-- The coefficient of the genuine original quadratic-dual Hilbert series. -/
theorem degree_finrank_eq_coeff (n : ℕ) :
    (Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul n) : ℤ)=
      PowerSeries.coeff n (QuadraticDual.tensorHilbertSeries f g) := by
  rw [QuadraticDual.tensorHilbertSeries,PowerSeries.coeff_mk,degree_finrank_eq]

end PaperVerification.AlternatingForms.IntrinsicQuadraticDual
