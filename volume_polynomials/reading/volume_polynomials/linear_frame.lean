module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp

@[expose] public section
set_option autoImplicit false

/-!
# Linear frames adapted to a nonzero functional

The kernel coordinate is literal subtraction of a chosen right inverse.
The volume factor is the positive scalar furnished by uniqueness of actual
additive Haar measures. No determinant or orthonormal-basis normalization is
needed, and no change of measure is left as an unproved hypothesis.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Module

namespace VolumePolynomials.LinearFrame

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def kernelPart (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    E →ₗ[ℝ] LinearMap.ker l.toLinearMap where
  toFun x := ⟨x - l x • v, by simp [map_sub, map_smul, hv]⟩
  map_add' x y := by
    first
    | apply Subtype.ext
      change x + y - l (x + y) • v = (x - l x • v) + (y - l y • v)
      simp only [map_add, add_smul]
      abel
  map_smul' r x := by
    first
    | apply Subtype.ext
      change r • x - l (r • x) • v = r • (x - l x • v)
      simp only [map_smul, smul_eq_mul, smul_sub, smul_smul]

@[simp] theorem kernelPart_coe (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) (x : E) :
    ((kernelPart l v hv x : LinearMap.ker l.toLinearMap) : E) = x - l x • v := rfl

def equiv (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    E ≃ₗ[ℝ] ℝ × LinearMap.ker l.toLinearMap where
  toFun x := (l x, kernelPart l v hv x)
  invFun p := p.1 • v + p.2.val
  left_inv x := by
    first
    | change l x • v + (x - l x • v) = x
      abel
  right_inv p := by
    first
    | apply Prod.ext
      · change l (p.1 • v + p.2.val) = p.1
        simp [map_add, map_smul, hv, p.2.property]
      · apply Subtype.ext
        change p.1 • v + p.2.val - l (p.1 • v + p.2.val) • v = p.2.val
        simp [map_add, map_smul, hv, p.2.property]
  map_add' x y := Prod.ext (map_add l x y) (map_add (kernelPart l v hv) x y)
  map_smul' r x := Prod.ext (map_smul l r x) (map_smul (kernelPart l v hv) r x)

def continuousEquiv [FiniteDimensional ℝ E]
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    E ≃L[ℝ] ℝ × LinearMap.ker l.toLinearMap :=
  (equiv l v hv).toContinuousLinearEquiv

@[simp] theorem continuousEquiv_fst [FiniteDimensional ℝ E]
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) (x : E) :
    (continuousEquiv l v hv x).1 = l x := rfl

@[simp] theorem continuousEquiv_snd [FiniteDimensional ℝ E]
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) (x : E) :
    (continuousEquiv l v hv x).2 = kernelPart l v hv x := rfl

theorem exists_unit_value (l : E →L[ℝ] ℝ) (hl : l ≠ 0) : ∃ v, l v = 1 := by
  first
  | have hn : ∃ x, l x ≠ 0 := by
      by_contra! h
      apply hl
      ext x
      exact h x
    obtain ⟨x, hx⟩ := hn
    exact ⟨(l x)⁻¹ • x, by simp [map_smul, hx]⟩

theorem finrank_kernel_add_one [FiniteDimensional ℝ E]
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    finrank ℝ (LinearMap.ker l.toLinearMap) + 1 = finrank ℝ E := by
  first
  | have h := (equiv l v hv).finrank_eq
    simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using h.symm

section Measure

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F]
  [IsAddHaarMeasure (volume : Measure E)] [IsAddHaarMeasure (volume : Measure F)]

/-- Expose the product-volume identity before instance search. This wrapper is
useful with Lean's public module interfaces, which otherwise may leave the
`volume` projection opaque during synthesis. -/
instance volume_product_isAddHaarMeasure :
    IsAddHaarMeasure (volume : Measure (E × F)) := by
  first
  | rw [Measure.volume_eq_prod]
    infer_instance

/-- The scalar multiplying target volume to recover source volume. -/
def volumeFactor (T : E ≃L[ℝ] F) : NNReal :=
  addHaarScalarFactor ((volume : Measure E).map T) (volume : Measure F)

theorem volumeFactor_pos (T : E ≃L[ℝ] F) : 0 < volumeFactor T :=
  addHaarScalarFactor_pos_of_isAddHaarMeasure ((volume : Measure E).map T) (volume : Measure F)

theorem realVolume_eq_factor_mul_image (T : E ≃L[ℝ] F) (S : Set E) :
    volume.real S = (volumeFactor T : ℝ) * volume.real (T '' S) := by
  first
  | have hm : ((volume : Measure E).map T) (T '' S) = volume S := by
      change ((volume : Measure E).map T.toHomeomorph) (T.toHomeomorph '' S) = volume S
      rw [T.toHomeomorph.measurableEmbedding.map_apply,
        Set.preimage_image_eq S T.toHomeomorph.injective]
    have heq : (volume : Measure E).map T = volumeFactor T • (volume : Measure F) :=
      isAddLeftInvariant_eq_smul _ _
    have h := congrArg ENNReal.toReal hm.symm
    rw [heq, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul] at h
    simpa only [ENNReal.coe_toReal, measureReal_def] using h

end Measure
end VolumePolynomials.LinearFrame
