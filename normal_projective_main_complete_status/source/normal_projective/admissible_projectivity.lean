module
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Bounded halfspaces and the inverse projective denominator

RECOVERY DRAFT, NOT COMPILED.
This is a new complete source candidate, not a recovered checked module.
-/

@[expose] public section
noncomputable section
open Set

namespace NormalProjective.ProjectiveBridge

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HRegion (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) : Set E :=
  {x | ∀ i, f i x ≤ h i}

def changedNormals (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (u : E →ₗ[ℝ] ℝ) : ι → E →ₗ[ℝ] ℝ :=
  fun i => f i + h i • u

def elementary (u : E →ₗ[ℝ] ℝ) (x : E) : E :=
  (1 + u x)⁻¹ • x

@[simp] theorem changedNormals_apply (f : ι → E →ₗ[ℝ] ℝ)
    (h : ι → ℝ) (u : E →ₗ[ℝ] ℝ) (i : ι) (x : E) :
    changedNormals f h u i x = f i x + h i * u x := by
  simp [changedNormals]

theorem changedNormals_neg (f : ι → E →ₗ[ℝ] ℝ)
    (h : ι → ℝ) (u : E →ₗ[ℝ] ℝ) :
    changedNormals (changedNormals f h u) h (-u) = f := by
  funext i
  ext x
  simp [changedNormals] <;> ring

/-- Boundedness excludes every nonzero feasible recession direction. -/
theorem recession_zero (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) (hb : Bornology.IsBounded (HRegion f h))
    {v : E} (hv : ∀ i, f i v ≤ 0) : v = 0 := by
  by_contra hv0
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  obtain ⟨C, hC, hbound⟩ := hb.exists_pos_norm_le
  let t : ℝ := (C + 1) / ‖v‖
  have ht : 0 ≤ t := le_of_lt (div_pos (by linarith) hnv)
  have htv : t • v ∈ HRegion f h := by
    intro i
    have hmul : t * f i v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (hv i)
    simpa only [map_smul, smul_eq_mul] using hmul.trans (hh i)
  have hn := hbound (t • v) htv
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hn
  have hcancel : t * ‖v‖ = C + 1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ (ne_of_gt hnv)
  rw [hcancel] at hn
  linarith

/-- No extra branch of the transformed H-region lies behind the inverse pole. -/
theorem inverse_denominator_pos (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) (hb : Bornology.IsBounded (HRegion f h))
    (u : E →ₗ[ℝ] ℝ) {y : E}
    (hy : y ∈ HRegion (changedNormals f h u) h) :
    0 < 1 - u y := by
  by_contra hpos
  have hd : 1 - u y ≤ 0 := le_of_not_gt hpos
  have hz : y = 0 := recession_zero f h hh hb (fun i => by
    have hi : f i y + h i * u y ≤ h i := hy i
    have hm : h i * (1 - u y) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hh i) hd
    nlinarith)
  subst y
  have hbad : (1 : ℝ) ≤ 0 := by simpa using hd
  exact (not_le.mpr zero_lt_one) hbad

@[simp] theorem linear_elementary (f u : E →ₗ[ℝ] ℝ) (x : E) :
    f (elementary u x) = f x / (1 + u x) := by
  simp [elementary, div_eq_mul_inv, mul_comm]

theorem elementary_inverse_denominator (u : E →ₗ[ℝ] ℝ) (x : E)
    (hx : 1 + u x ≠ 0) :
    1 + (-u) (elementary u x) = (1 + u x)⁻¹ := by
  simp only [LinearMap.neg_apply, linear_elementary]
  field_simp [hx] <;> ring

theorem elementary_inverse (u : E →ₗ[ℝ] ℝ) (x : E)
    (hx : 1 + u x ≠ 0) :
    elementary (-u) (elementary u x) = x := by
  change (1 + (-u) (elementary u x))⁻¹ • elementary u x = x
  rw [elementary_inverse_denominator u x hx]
  simp [elementary, smul_smul, hx]

theorem mem_changed_iff (f : ι → E →ₗ[ℝ] ℝ)
    (h : ι → ℝ) (u : E →ₗ[ℝ] ℝ) (x : E)
    (hx : 0 < 1 + u x) :
    elementary u x ∈ HRegion (changedNormals f h u) h ↔
      x ∈ HRegion f h := by
  constructor
  · intro hy i
    have hi : (f i x + h i * u x) / (1 + u x) ≤ h i := by
      simpa only [linear_elementary, changedNormals_apply] using hy i
    have hmul := (div_le_iff₀ hx).mp hi
    nlinarith
  · intro hy i
    change changedNormals f h u i (elementary u x) ≤ h i
    rw [linear_elementary, changedNormals_apply]
    apply (div_le_iff₀ hx).mpr
    have hi := hy i
    nlinarith

/-- Formula (1) with the inverse positivity proved from boundedness. -/
theorem elementary_image_HRegion (f : ι → E →ₗ[ℝ] ℝ)
    (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (hb : Bornology.IsBounded (HRegion f h))
    (u : E →ₗ[ℝ] ℝ)
    (hforward : ∀ x ∈ HRegion f h, 0 < 1 + u x) :
    elementary u '' HRegion f h = HRegion (changedNormals f h u) h := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (mem_changed_iff f h u x (hforward x hx)).mpr hx
  · intro y hy
    have hback : 0 < 1 + (-u) y := by
      simpa using inverse_denominator_pos f h hh hb u hy
    have hmem : elementary (-u) y ∈ HRegion f h := by
      have hm := (mem_changed_iff (changedNormals f h u) h (-u) y hback).mpr hy
      simpa only [changedNormals_neg] using hm
    refine ⟨elementary (-u) y, hmem, ?_⟩
    simpa only [neg_neg] using elementary_inverse (-u) y (ne_of_gt hback)

end NormalProjective.ProjectiveBridge

