module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

@[expose] public section

/-! # The actual affine dimension of an integral arrangement stratum

A stratum is the literal intersection of its active affine hyperplanes and its
open unit slabs. Its affine hull has exactly the intersection of the active
linear kernels as its direction; this is proved from relative openness.
-/

noncomputable section
namespace Unimodular.CycleBounds
open Set
attribute [local instance] Classical.propDecidable
variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [Finite I]

/-- The lifted stratum containing x in the periodic integral hyperplane arrangement. -/
def integerStratum (f : I → W →ₗ[ℝ] ℝ) (x : W) : Set W :=
  {y | ∀ i, if ∃ z : ℤ, f i x = (z : ℝ) then f i y = f i x
    else (⌊f i x⌋ : ℝ) < f i y ∧ f i y < (⌈f i x⌉ : ℝ)}

/-- Its actual active linear equations. -/
def integerStratumDirection (f : I → W →ₗ[ℝ] ℝ) (x : W) : Submodule ℝ W where
  carrier := {y | ∀ i, (∃ z : ℤ, f i x = (z : ℝ)) → f i y = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  smul_mem' := by intro r a ha i hi; simp [ha i hi]

theorem self_mem_integerStratum (f : I → W →ₗ[ℝ] ℝ) (x : W) :
    x ∈ integerStratum f x := by
  intro i
  by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
  · simp [hi]
  · simp only [if_neg hi]
    constructor
    · exact lt_of_le_of_ne (Int.floor_le _) (fun h ↦ hi ⟨⌊f i x⌋, h.symm⟩)
    · exact lt_of_le_of_ne (Int.le_ceil _) (fun h ↦ hi ⟨⌈f i x⌉, h⟩)

/-- The ceiling representative is constant on every literal arrangement stratum. -/
theorem ceil_eq_of_mem_integerStratum (f : I → W →ₗ[ℝ] ℝ) {x y : W}
    (hy : y ∈ integerStratum f x) (i : I) : ⌈f i y⌉ = ⌈f i x⌉ := by
  have h := hy i
  by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
  · rw [if_pos hi] at h
    rw [h]
  · rw [if_neg hi] at h
    apply Int.ceil_eq_iff.mpr
    refine ⟨?_, h.2.le⟩
    have hb : (⌈f i x⌉ : ℝ) ≤ (⌊f i x⌋ : ℝ) + 1 := by
      exact_mod_cast Int.ceil_le_floor_add_one (f i x)
    linarith [h.1]

/-- Integral translations leave exactly the same active direction space. This
is the independence of the lift used for periodic-arrangement dimensions. -/
theorem integerStratumDirection_add_of_integral (f : I → W →ₗ[ℝ] ℝ)
    (x m : W) (hm : ∀ i, ∃ z : ℤ, f i m = (z : ℝ)) :
    integerStratumDirection f (x + m) = integerStratumDirection f x := by
  have heq (i : I) : (∃ z : ℤ, f i (x + m) = (z : ℝ)) ↔
      ∃ z : ℤ, f i x = (z : ℝ) := by
    obtain ⟨k, hk⟩ := hm i
    rw [map_add, hk]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z - k, ?_⟩
      push_cast
      linarith
    · rintro ⟨z, hz⟩
      refine ⟨z + k, ?_⟩
      push_cast
      rw [hz]
  ext d
  change (∀ i, (∃ z : ℤ, f i (x + m) = (z : ℝ)) → f i d = 0) ↔
    (∀ i, (∃ z : ℤ, f i x = (z : ℝ)) → f i d = 0)
  simp only [heq]

/-- The affine hull of the actual cell has precisely its active-kernel direction.
In particular its dimension is not introduced as an assumed graph rank formula. -/
theorem direction_integerStratum_eq (f : I → W →ₗ[ℝ] ℝ) (x : W) :
    (affineSpan ℝ (integerStratum f x)).direction = integerStratumDirection f x := by
  let D := integerStratumDirection f x
  let U : Set D := ⋂ i : I, if ∃ z : ℤ, f i x = (z : ℝ) then Set.univ else
    {d | (⌊f i x⌋ : ℝ) < f i (x + d.val) ∧ f i (x + d.val) < (⌈f i x⌉ : ℝ)}
  have hopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
    · simp only [if_pos hi]
      exact isOpen_univ
    · simp only [if_neg hi]
      have hc : Continuous (fun d : D ↦ f i (x + d.val)) :=
        (f i).continuous_of_finiteDimensional.comp (continuous_const.add continuous_subtype_val)
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hzero : (0 : D) ∈ U := by
    apply Set.mem_iInter.mpr
    intro i
    have hh := self_mem_integerStratum f x i
    by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
    · simp [hi]
    · simpa [hi] using hh
  let F : D →ᵃ[ℝ] W := (AffineEquiv.constVAdd ℝ W x).toAffineMap.comp D.subtype.toAffineMap
  have hF (d : D) : F d = x + d.val := rfl
  have himage : F '' U = integerStratum f x := by
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩ i
      rw [hF]
      by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
      · simp only [if_pos hi, map_add, d.property i hi, add_zero]
      · simpa only [if_neg hi, Set.mem_setOf_eq] using Set.mem_iInter.mp hd i
    · intro hy
      have hd : y - x ∈ D := by
        intro i hi
        have hh := hy i
        rw [if_pos hi] at hh
        simp only [map_sub, hh, sub_self]
      refine ⟨⟨y - x, hd⟩, ?_, by simp [hF]⟩
      apply Set.mem_iInter.mpr
      intro i
      have hh := hy i
      by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
      · simp [hi]
      · simpa only [if_neg hi, Set.mem_setOf_eq, add_sub_cancel] using hh
  have hspan : affineSpan ℝ U = ⊤ := hopen.affineSpan_eq_top ⟨0, hzero⟩
  rw [← himage, ← AffineSubspace.map_span, hspan, AffineSubspace.map_direction, AffineSubspace.direction_top]
  change Submodule.map D.subtype (⊤ : Submodule ℝ D) = D
  simp

/-- Equality with the actual affine-geometric stratum dimension. -/
theorem finrank_integerStratum (f : I → W →ₗ[ℝ] ℝ) (x : W) :
    Module.finrank ℝ (affineSpan ℝ (integerStratum f x)).direction =
      Module.finrank ℝ (integerStratumDirection f x) := by
  rw [direction_integerStratum_eq]

/-- The geometric dimension is well defined under every integral translation
of the chosen lift of a periodic-arrangement stratum. -/
theorem finrank_integerStratum_add_of_integral (f : I → W →ₗ[ℝ] ℝ)
    (x m : W) (hm : ∀ i, ∃ z : ℤ, f i m = (z : ℝ)) :
    Module.finrank ℝ (affineSpan ℝ (integerStratum f (x + m))).direction =
      Module.finrank ℝ (affineSpan ℝ (integerStratum f x)).direction := by
  rw [finrank_integerStratum, finrank_integerStratum,
    integerStratumDirection_add_of_integral f x m hm]

#print axioms direction_integerStratum_eq
end Unimodular.CycleBounds
