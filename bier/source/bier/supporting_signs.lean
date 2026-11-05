import bier.facet_coordinates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # The strict coordinate signs forced by the two neighboring facets -/

noncomputable section

namespace Bier

open Classical Finset Matrix

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

theorem linearMap_mulVec (f : (I → ℝ) →ₗ[ℝ] ℝ) (C : Matrix I I ℝ) (a : I → ℝ) :
    f (C *ᵥ a) = ∑ j, a j * f (C.col j) := by
  have he : C *ᵥ a = ∑ j, a j • C.col j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, mul_comm]
  rw [he, map_sum]
  simp

theorem exchange_coordinate_neg (C : Matrix I I ℝ) (x a : I → ℝ) (j : I)
    (he : C *ᵥ a = x) (f g : (I → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, f (C.col i) = 1) (hfx : f x < 1)
    (hg : ∀ i, i ≠ j → g (C.col i) = 1) (hgx : g x = 1)
    (hgj : g (C.col j) < 1) : a j < 0 := by
  have hsum : ∑ i, a i < 1 := by
    have hh := congrArg f he
    rw [linearMap_mulVec] at hh
    simp only [hf, mul_one] at hh
    linarith
  have hh := congrArg g he
  rw [linearMap_mulVec, hgx] at hh
  have hv (i : I) : g (C.col i) = 1 + if i = j then g (C.col j) - 1 else 0 := by
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi, hg i hi]
  have hsumeq : (∑ i, a i * g (C.col i)) =
      (∑ i, a i) + a j * (g (C.col j) - 1) := by
    calc
      _ = ∑ i, a i * (1 + if i = j then g (C.col j) - 1 else 0) :=
        Finset.sum_congr rfl (fun i _ => congrArg (a i * ·) (hv i))
      _ = _ := by simp [mul_add, mul_ite, Finset.sum_add_distrib]
  rw [hsumeq] at hh
  by_contra hn
  have ha : 0 ≤ a j := by linarith
  nlinarith

theorem transition_coordinate_pos (C : Matrix I I ℝ) (x a : I → ℝ) (j : I)
    (he : C *ᵥ a = x) (f : (I → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, i ≠ j → f (C.col i) = 0)
    (hfx : f x < 0) (hfj : f (C.col j) < 0) : 0 < a j := by
  have hh := congrArg f he
  rw [linearMap_mulVec] at hh
  have hsum : (∑ i, a i * f (C.col i)) = a j * f (C.col j) := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      simp [hf i hij]
    · simp
  rw [hsum] at hh
  by_contra hn
  have ha : a j ≤ 0 := by linarith
  nlinarith

namespace CoordinateModel

theorem supporting_normalized {K : Complex V} (M : CoordinateModel K I)
    (s : Finset ↥K.vertices) (hs : K.face (s.image Subtype.val)) (hne : s.Nonempty)
    (z : ↥K.vertices) (hz : M.point z = 0) (hzs : z ∉ s) :
    ∃ l : (I → ℝ) →ₗ[ℝ] ℝ,
      (∀ v, l (M.point v) ≤ 1) ∧ (∀ v, l (M.point v) = 1 ↔ v ∈ s) := by
  obtain ⟨l, c, hle, he⟩ := M.supporting s hs hne
  have hzc := hle z
  rw [hz, map_zero] at hzc
  have hne0 : 0 ≠ c := by
    intro hc
    apply hzs
    apply (he z).mp
    rw [hz, map_zero, hc]
  have hc : 0 < c := lt_of_le_of_ne hzc hne0
  refine ⟨c⁻¹ • l, ?_, ?_⟩
  · intro v
    change c⁻¹ * l (M.point v) ≤ 1
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hc).mpr (hle v)
  · intro v
    change c⁻¹ * l (M.point v) = 1 ↔ _
    rw [mul_comm, ← div_eq_mul_inv, div_eq_one_iff_eq hc.ne']
    exact he v

end CoordinateModel
end Bier
