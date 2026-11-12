module

public import ToricPower.Core
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull

@[expose] public section
noncomputable section

open Set
open scoped Pointwise

namespace ToricPower

variable {E ι κ : Type*} [AddCommGroup E] [Module ℝ E]

/-- A family of literal closed halfspaces with affine right-hand sides. -/
def parametricRegion (f : ι → E →ₗ[ℝ] ℝ) (d e : ι → ℝ) (t : ℝ) : Set E :=
  {x | ∀ i, f i x ≤ t * d i + e i}

def slopeRegion (f : ι → E →ₗ[ℝ] ℝ) (d : ι → ℝ) : Set E :=
  {x | ∀ i, f i x ≤ d i}

lemma parametricRegion_convex (f : ι → E →ₗ[ℝ] ℝ)
    (d e : ι → ℝ) (t : ℝ) : Convex ℝ (parametricRegion f d e t) := by
  intro x hx y hy a b ha hb hab i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a * f i x + b * f i y ≤ a * (t * d i + e i) + b * (t * d i + e i) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = t * d i + e i := by rw [← add_mul, hab, one_mul]

lemma slopeRegion_convex (f : ι → E →ₗ[ℝ] ℝ)
    (d : ι → ℝ) : Convex ℝ (slopeRegion f d) := by
  simpa [slopeRegion, parametricRegion] using parametricRegion_convex f d 0 1

lemma affine_slope_nonpos (a b L : ℝ)
    (h : ∀ t : ℝ, L ≤ t → t * a + b ≤ 0) : a ≤ 0 := by
  by_contra ha
  have hap : 0 < a := lt_of_not_ge ha
  let t : ℝ := max L ((-b + 1) / a)
  have htL : L ≤ t := le_max_left _ _
  have hta : (-b + 1) ≤ t * a := by
    have ht : (-b + 1) / a ≤ t := le_max_right _ _
    exact (div_le_iff₀ hap).mp ht
  have hh := h t htL
  linarith

lemma slope_mem_of_all_large_vertices (f : ι → E →ₗ[ℝ] ℝ)
    (d e : ι → ℝ) (x y : E) (L : ℝ)
    (h : ∀ t : ℝ, L ≤ t → t • x + y ∈ parametricRegion f d e t) :
    x ∈ slopeRegion f d := by
  intro i
  have hneg : f i x - d i ≤ 0 := by
    apply affine_slope_nonpos (f i x - d i) (f i y - e i) L
    intro t ht
    have hi := h t ht i
    simp only [map_add, map_smul, smul_eq_mul] at hi
    nlinarith
  linarith

/-- A fixed list of affine feasible vertices gives an exact Minkowski expansion.
The hypotheses refer to actual halfspace regions. Empty and lower-dimensional
regions are permitted. This lemma does not assume equality of normal fans. -/
theorem parametric_region_minkowski (f : ι → E →ₗ[ℝ] ℝ)
    (d e : ι → ℝ) (S : Set κ) (x y : κ → E) (L : ℝ)
    (hvertices : ∀ t : ℝ, L ≤ t →
      parametricRegion f d e t =
        convexHull ℝ ((fun i => t • x i + y i) '' S))
    (t : ℝ) (ht : L ≤ t) :
    parametricRegion f d e t =
      parametricRegion f d e L + (t - L) • slopeRegion f d := by
  have hmember (i : κ) (hi : i ∈ S) (u : ℝ) (hu : L ≤ u) :
      u • x i + y i ∈ parametricRegion f d e u := by
    rw [hvertices u hu]
    exact subset_convexHull ℝ _ ⟨i, hi, rfl⟩
  have hslope (i : κ) (hi : i ∈ S) : x i ∈ slopeRegion f d :=
    slope_mem_of_all_large_vertices f d e (x i) (y i) L
      (fun u hu => hmember i hi u hu)
  apply le_antisymm
  · rw [hvertices t ht]
    apply convexHull_min
    · rintro z ⟨i, hi, rfl⟩
      refine ⟨L • x i + y i, hmember i hi L le_rfl,
        (t - L) • x i, ⟨x i, hslope i hi, rfl⟩, ?_⟩
      rw [sub_smul]
      abel
    · exact (parametricRegion_convex f d e L).add
        ((slopeRegion_convex f d).smul (t - L))
  · rintro z ⟨p, hp, v, ⟨q, hq, rfl⟩, rfl⟩ i
    simp only [map_add, map_smul, smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left (hq i) (sub_nonneg.mpr ht)
    have hh := hp i
    nlinarith

end ToricPower
