module

public import VolumePolynomials.HalfspacePyramids
public import VolumePolynomials.PolytopeFaces
public import Mathlib.Order.Filter.Finite
public import Mathlib.Tactic.FieldSimp

@[expose] public section
set_option autoImplicit false

/-! # Radial fibers of an actual Minkowski perturbation

The old polytope is the literal bounded intersection `lᵢ x ≤ 1`. At a point
lying on exactly one old facet, a maximizer of that facet functional on the
added body gives the exact moving radial endpoint for all sufficiently small
nonnegative parameters. This is the geometric input to first variation;
no mixed-volume or first-variation formula is assumed.
-/

noncomputable section
open Set Filter
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials.PolytopeRadialGeometry

open HalfspacePyramids

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem convex_body (l : ι → E →L[ℝ] ℝ) : Convex ℝ (body l) := by
  first
  | intro x hx y hy a b ha hb hab i
    change l i (a • x + b • y) ≤ 1
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hb)
    simpa only [mul_one, hab] using h

theorem mem_smul_body_iff (l : ι → E →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r) (x : E) :
    x ∈ r • body l ↔ ∀ i, l i x ≤ r := by
  first
  | constructor
    · rintro ⟨y, hy, rfl⟩ i
      simpa only [map_smul, smul_eq_mul, mul_one] using
        mul_le_mul_of_nonneg_left (hy i) hr.le
    · intro hx
      refine ⟨r⁻¹ • x, ?_, by simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
      intro i
      change l i (r⁻¹ • x) ≤ 1
      rw [map_smul, smul_eq_mul]
      simpa only [inv_mul_cancel₀ hr.ne'] using
        mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr hr.le)

theorem body_subset_add_smul (l : ι → E →L[ℝ] ℝ) {A : Set E}
    (hA0 : (0 : E) ∈ A) (t : ℝ) : body l ⊆ body l + t • A := by
  first
  | intro x hx
    exact ⟨x, hx, 0, ⟨0, hA0, by simp⟩, add_zero x⟩

theorem add_smul_subset_smul_body (l : ι → E →L[ℝ] ℝ) {A : Set E}
    {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hbound : ∀ i a, a ∈ A → l i a ≤ C) :
    body l + t • A ⊆ (1 + t * C) • body l := by
  first
  | rintro x ⟨s, hs, z, ⟨a, ha, rfl⟩, rfl⟩
    apply Iff.mpr (mem_smul_body_iff l (by positivity) _)
    intro i
    change l i (s + t • a) ≤ 1 + t * C
    rw [map_add, map_smul, smul_eq_mul]
    exact add_le_add (hs i) (mul_le_mul_of_nonneg_left (hbound i a ha) ht)

/-- The candidate endpoint is obtained by translating an old facet point back
by an actual support maximizer. All inactive inequalities remain strict locally. -/
theorem eventually_radial_endpoint_mem
    (l : ι → E →L[ℝ] ℝ) (i : ι) {q a : E}
    (hq : q ∈ face l i) (hstrict : ∀ j, j ≠ i → l j q < 1)
    {A : Set E} (ha : a ∈ A) :
    ∀ᶠ t : ℝ in 𝓝 0, (1 + t * l i a) • q ∈ body l + t • A := by
  first
  | have hall : ∀ j, ∀ᶠ t : ℝ in 𝓝 0,
        l j ((1 + t * l i a) • q - t • a) ≤ 1 := by
      first
      | intro j
        by_cases hji : j = i
        · subst j
          exact Eventually.of_forall fun t => by
            rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hq.2]
            linarith
        · have hc : Continuous (fun t : ℝ => l j ((1 + t * l i a) • q - t • a)) := by
            first
            | fun_prop
          have hh : l j ((1 + (0 : ℝ) * l i a) • q - (0 : ℝ) • a) < 1 := by
            first
            | simpa using hstrict j hji
          exact (hc.continuousAt.eventually (Iio_mem_nhds hh)).mono fun _ h => h.le
    filter_upwards [Filter.eventually_all.mpr hall] with t ht
    refine ⟨(1 + t * l i a) • q - t • a, ht, t • a, ⟨a, ha, rfl⟩, ?_⟩
    exact sub_add_cancel _ _

/-- At almost every old facet point, every nonnegative radial coordinate has
the exact interval-membership description for a small positive perturbation. -/
theorem eventually_radial_mem_iff
    (l : ι → E →L[ℝ] ℝ) (i : ι) {q a : E}
    (hq : q ∈ face l i) (hstrict : ∀ j, j ≠ i → l j q < 1)
    {A : Set E} (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A)
    (ha : a ∈ A) (hmax : ∀ x ∈ A, l i x ≤ l i a) :
    ∀ᶠ t : ℝ in 𝓝[≥] 0, ∀ r : ℝ, 0 ≤ r →
      (r • q ∈ body l + t • A ↔ r ≤ 1 + t * l i a) := by
  first
  | have hc : 0 ≤ l i a := by simpa using hmax 0 hA0
    have hend : ∀ᶠ t : ℝ in 𝓝[≥] 0,
        (1 + t * l i a) • q ∈ body l + t • A :=
      (eventually_radial_endpoint_mem l i hq hstrict ha).filter_mono nhdsWithin_le_nhds
    filter_upwards [hend, self_mem_nhdsWithin] with t ht htn
    have ht0 : 0 ≤ t := htn
    have hlam : 0 < 1 + t * l i a := by positivity
    have hzero : (0 : E) ∈ body l + t • A :=
      body_subset_add_smul l hA0 t (zero_mem_body l)
    have hconv : Convex ℝ (body l + t • A) := (convex_body l).add (hA.smul t)
    intro r hr
    constructor
    · rintro ⟨s, hs, z, ⟨b, hb, rfl⟩, heq⟩
      have hli := congrArg (l i) heq
      simp only [map_add, map_smul, smul_eq_mul, hq.2, mul_one] at hli
      have hb' := mul_le_mul_of_nonneg_left (hmax b hb) ht0
      linarith [hs i]
    · intro hrlam
      have hratio : r / (1 + t * l i a) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hr hlam.le, (div_le_one hlam).mpr hrlam⟩
      have hm := hconv.smul_mem_of_zero_mem hzero ht hratio
      simpa only [smul_smul, div_mul_cancel₀ _ hlam.ne'] using hm

/-- Compactness supplies a genuine uniform bound on every normal, independent
of the boundary point and of the perturbation parameter. -/
theorem exists_uniform_normal_bound
    (l : ι → E →L[ℝ] ℝ) {A : Set E} (hA : IsCompact A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i a, a ∈ A → |l i a| ≤ C := by
  first
  | classical
    obtain ⟨R, hR, hbound⟩ := hA.isBounded.exists_pos_norm_le
    refine ⟨R * ∑ j, ‖l j‖, mul_nonneg hR.le (Finset.sum_nonneg fun _ _ => norm_nonneg _), ?_⟩
    intro i a ha
    have hnorm : ‖l i‖ ≤ ∑ j, ‖l j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (l j)) (Finset.mem_univ i)
    calc
      |l i a| = ‖l i a‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖l i‖ * ‖a‖ := (l i).le_opNorm a
      _ ≤ ‖l i‖ * R := mul_le_mul_of_nonneg_left (hbound a ha) (norm_nonneg _)
      _ ≤ (∑ j, ‖l j‖) * R := mul_le_mul_of_nonneg_right hnorm hR.le
      _ = _ := mul_comm _ _

end VolumePolynomials.PolytopeRadialGeometry
