module
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Rational certificates for finite polyhedra

The coefficient fields in Corollary 7.2 may have arbitrary characteristic.
Its convex polytope is a separate real geometric object with integral vertices.
This file proves the exact bridge to rational certificates by eliminating one
variable at a time from a finite family of rational linear inequalities.
-/

noncomputable section
namespace FourPapers.Symmetric.RationalPolyhedra
open scoped BigOperators

private theorem between_finsets (L U : Finset ℚ)
    (hLU : ∀ a ∈ L, ∀ b ∈ U, a ≤ b) :
    ∃ z : ℚ, (∀ a ∈ L, a ≤ z) ∧ (∀ b ∈ U, z ≤ b) := by
  classical
  by_cases hL : L.Nonempty
  · refine ⟨L.sup' hL id, ?_, ?_⟩
    · intro a ha
      exact Finset.le_sup' id ha
    · intro b hb
      exact Finset.sup'_le _ _ (fun a ha => hLU a ha b hb)
  · by_cases hU : U.Nonempty
    · refine ⟨U.inf' hU id, ?_, ?_⟩
      · intro a ha
        exact (hL ⟨a, ha⟩).elim
      · intro b hb
        exact Finset.inf'_le id hb
    · refine ⟨0, ?_, ?_⟩
      · intro a ha
        exact (hL ⟨a, ha⟩).elim
      · intro b hb
        exact (hU ⟨b, hb⟩).elim

/-- Every feasible finite system of rational weak linear inequalities has
a rational solution.  No boundedness or strict-feasibility assumption is needed. -/
theorem rational_solution {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Fin n → ℚ) (b : ι → ℚ)
    (h : ∃ x : Fin n → ℝ, ∀ i, ∑ j, (A i j : ℝ) * x j ≤ b i) :
    ∃ x : Fin n → ℚ, ∀ i, ∑ j, A i j * x j ≤ b i := by
  classical
  induction n generalizing ι with
  | zero =>
      obtain ⟨x, hx⟩ := h
      refine ⟨Fin.elim0, ?_⟩
      intro i
      have hi := hx i
      simp only [Fin.sum_univ_zero] at hi ⊢
      exact_mod_cast hi
  | succ n ih =>
      let Z := {i : ι // A i 0 = 0}
      let N := {i : ι // A i 0 < 0}
      let P := {i : ι // 0 < A i 0}
      let J := Z ⊕ (N × P)
      let B : J → Fin n → ℚ := fun q j => match q with
        | Sum.inl i => A i.val j.succ
        | Sum.inr (i,k) => A k.val j.succ / A k.val 0 - A i.val j.succ / A i.val 0
      let c : J → ℚ := fun q => match q with
        | Sum.inl i => b i.val
        | Sum.inr (i,k) => b k.val / A k.val 0 - b i.val / A i.val 0
      have reduced : ∃ y : Fin n → ℝ, ∀ q, ∑ j, (B q j : ℝ) * y j ≤ c q := by
        obtain ⟨x, hx⟩ := h
        refine ⟨fun j => x j.succ, ?_⟩
        intro q
        cases q with
        | inl i =>
            have hi := hx i.val
            simpa only [Fin.sum_univ_succ, i.property, Rat.cast_zero, zero_mul,
              zero_add, B, c] using hi
        | inr pair =>
            obtain ⟨i,k⟩ := pair
            have hi := hx i.val
            have hk := hx k.val
            rw [Fin.sum_univ_succ] at hi hk
            have hn : (A i.val 0 : ℝ) < 0 := by exact_mod_cast i.property
            have hp : (0 : ℝ) < A k.val 0 := by exact_mod_cast k.property
            have hil : (b i.val - ∑ j : Fin n, (A i.val j.succ : ℝ) * x j.succ) /
                A i.val 0 ≤ x 0 := (div_le_iff_of_neg hn).mpr (by linarith)
            have hku : x 0 ≤ (b k.val - ∑ j : Fin n, (A k.val j.succ : ℝ) * x j.succ) /
                A k.val 0 := (le_div_iff₀ hp).mpr (by linarith)
            have hlu := hil.trans hku
            dsimp only [B, c]
            push_cast
            simp only [sub_mul, Finset.sum_sub_distrib, div_mul_eq_mul_div,
              ← Finset.sum_div]
            rw [sub_div, sub_div] at hlu
            linarith
      obtain ⟨y, hy⟩ := ih B c reduced
      let low : N → ℚ := fun i => (b i.val - ∑ j, A i.val j.succ * y j) / A i.val 0
      let up : P → ℚ := fun i => (b i.val - ∑ j, A i.val j.succ * y j) / A i.val 0
      have cross : ∀ i : N, ∀ k : P, low i ≤ up k := by
        intro i k
        have hk := hy (Sum.inr (i,k))
        dsimp only [B, c] at hk
        simp only [sub_mul, Finset.sum_sub_distrib, div_mul_eq_mul_div,
          ← Finset.sum_div] at hk
        dsimp only [low, up]
        rw [sub_div, sub_div]
        linarith
      obtain ⟨z, hzL, hzU⟩ := between_finsets (Finset.univ.image low) (Finset.univ.image up)
        (by
          intro a ha d hd
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hd
          exact cross i k)
      refine ⟨Fin.cons z y, ?_⟩
      intro i
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rcases lt_trichotomy (A i 0) 0 with hn | hz | hp
      · have hlo := hzL (low ⟨i,hn⟩) (Finset.mem_image.mpr ⟨⟨i,hn⟩, Finset.mem_univ _, rfl⟩)
        have hh := (div_le_iff_of_neg hn).mp hlo
        dsimp only [low] at hh
        linarith
      · have hh := hy (Sum.inl ⟨i,hz⟩)
        simpa only [B, c, hz, zero_mul, zero_add] using hh
      · have hup := hzU (up ⟨i,hp⟩) (Finset.mem_image.mpr ⟨⟨i,hp⟩, Finset.mem_univ _, rfl⟩)
        have hh := (le_div_iff₀ hp).mp hup
        dsimp only [up] at hh
        linarith

end FourPapers.Symmetric.RationalPolyhedra
end
