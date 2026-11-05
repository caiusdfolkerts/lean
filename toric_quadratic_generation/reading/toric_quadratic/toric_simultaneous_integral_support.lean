module

public import PaperVerification.ToricSimultaneousSupport
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
# Integral strict support after all disjoint star subdivisions

A single sufficiently small reciprocal integer parameter works at every
selected center. Scaling by that integer makes every actual support
coefficient integral, so the terminating primitive reduction applies to the
constructed simultaneous fan without a projectivity assumption.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem exists_integral_strictSupport_simultaneousSubdivision
    {ι : Type*} [Fintype ι]
    (T : ι → Finset (Lattice n)) (hT : ∀ i, T i ∈ «Σ».cones)
    (hne : ∀ i, (T i).Nonempty) (hdisj : «Σ».PairwiseDisjointFoci T)
    (hcard : ∀ i, 2 ≤ (T i).card)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ))) :
    ∃ K : Lattice n → ℤ,
      («Σ».simultaneousSubdivision T hT hne hdisj).IsStrictSupport
        (fun v => (K v : ℝ)) := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    «Σ».strictSupport_simultaneousSubdivision_all_small T hT hne hdisj hcard
      (fun v => (H v : ℝ)) hH
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (max (1 : ℝ) δ⁻¹)
  have hNR : (0 : ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hNlarge)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hε : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNR
  have hεle : (N : ℝ)⁻¹ ≤ δ := by
    have hlarge : δ⁻¹ < (N : ℝ) := (le_max_right _ _).trans_lt hNlarge
    have hmul := mul_lt_mul_of_pos_left hlarge hδ
    rw [mul_inv_cancel₀ (ne_of_gt hδ)] at hmul
    simpa only [one_div] using (div_le_iff₀ hNR).mpr hmul.le
  have hs := hsmall (N : ℝ)⁻¹ hε hεle
  have hscaled := IsStrictSupport.smul («Σ».simultaneousSubdivision T hT hne hdisj) hs hNR
  let K : Lattice n → ℤ :=
    simultaneousSupport T (fun v => (N : ℤ) * H v) (fun _ => 1)
  have hcoeff : (fun v => (K v : ℝ)) = (N : ℝ) •
      simultaneousSupport T (fun v => (H v : ℝ)) (fun _ => (N : ℝ)⁻¹) := by
    funext v
    simp only [K, simultaneousSupport, Pi.smul_apply, smul_eq_mul,
      Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hv : v = ∑ w ∈ T i, w
    · simp only [if_pos hv, Int.cast_sub, Int.cast_sum, Int.cast_mul,
        Int.cast_natCast, Int.cast_one, mul_sub, Finset.mul_sum,
        mul_inv_cancel₀ hNne]
    · simp only [if_neg hv, Int.cast_zero, mul_zero]
  exact ⟨K, hcoeff.symm ▸ hscaled⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
