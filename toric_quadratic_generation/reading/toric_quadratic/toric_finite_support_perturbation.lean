module
public import PaperVerification.ToricNefCone
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# Finite strict support perturbations

All choices of a sufficiently small positive real number are reduced here
to minima of finitely many positive explicit ratios. The later subdivision
argument therefore does not assume that strict inequalities survive a
perturbation without proving a common parameter works for every cone.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Finitely many strict affine inequalities hold simultaneously after a
sufficiently small positive perturbation. -/
theorem finite_strict_perturbation_all_small {ι : Type*} (I : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ I, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ i ∈ I, 0 < f i + ε * g i := by
  by_cases hI : I.Nonempty
  · obtain ⟨j, hj, hmin⟩ := I.exists_min_image (fun i => f i / (|g i| + 1)) hI
    let δ := f j / (|g j| + 1)
    have hδ : 0 < δ := div_pos (hf j hj) (by have h := abs_nonneg (g j); linarith)
    refine ⟨δ, hδ, ?_⟩
    intro ε hε hεδ i hi
    have hden : 0 < |g i| + 1 := by have h := abs_nonneg (g i); linarith
    have hδbound : δ * (|g i| + 1) ≤ f i :=
      (le_div_iff₀ hden).mp (hmin i hi)
    have hbound : ε * (|g i| + 1) ≤ f i :=
      (mul_le_mul_of_nonneg_right hεδ hden.le).trans hδbound
    have hg : 0 ≤ g i + |g i| := by have h := neg_abs_le (g i); linarith
    have hprod := mul_nonneg hε.le hg
    nlinarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ε hε hεδ i hi
    exact (hI ⟨i, hi⟩).elim

theorem finite_strict_perturbation {ι : Type*} (I : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ I, 0 < f i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ I, 0 < f i + ε * g i := by
  obtain ⟨δ, hδ, hsmall⟩ := finite_strict_perturbation_all_small I f g hf
  exact ⟨δ, hδ, hsmall δ hδ le_rfl⟩

/-- A finite family of supporting linear forms with lexicographically
positive inactive slacks admits one common positive perturbation parameter. -/
theorem finite_lexicographic_support_perturbation_all_small {n : ℕ}
    (C : Finset (Finset (Lattice n))) (R : Finset (Lattice n))
    (a₀ a₁ : Lattice n → ℝ)
    (L₀ L₁ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ)
    (heq : ∀ s ∈ C, ∀ v ∈ s,
      L₀ s (embed n v) = a₀ v ∧ L₁ s (embed n v) = a₁ v)
    (hlex : ∀ s ∈ C, ∀ v ∈ R, v ∉ s →
      L₀ s (embed n v) < a₀ v ∨
      (L₀ s (embed n v) = a₀ v ∧ L₁ s (embed n v) < a₁ v)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ s ∈ C,
      (∀ v ∈ s, (L₀ s + ε • L₁ s) (embed n v) = a₀ v + ε * a₁ v) ∧
      (∀ v ∈ R, v ∉ s →
        (L₀ s + ε • L₁ s) (embed n v) < a₀ v + ε * a₁ v) := by
  let I := (C.product R).filter (fun p => p.2 ∉ p.1 ∧ L₀ p.1 (embed n p.2) < a₀ p.2)
  let f : Finset (Lattice n) × Lattice n → ℝ :=
    fun p => a₀ p.2 - L₀ p.1 (embed n p.2)
  let g : Finset (Lattice n) × Lattice n → ℝ :=
    fun p => a₁ p.2 - L₁ p.1 (embed n p.2)
  have hf : ∀ p ∈ I, 0 < f p := by
    intro p hp
    exact sub_pos.mpr (Finset.mem_filter.mp hp).2.2
  obtain ⟨δ, hδ, hpert⟩ := finite_strict_perturbation_all_small I f g hf
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ s hs
  constructor
  · intro v hv
    obtain ⟨h₀, h₁⟩ := heq s hs v hv
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₀, h₁]
  · intro v hv hvs
    rcases hlex s hs v hv hvs with h₀ | ⟨h₀, h₁⟩
    · have hmem : (s, v) ∈ I := Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs, hv⟩, hvs, h₀⟩
      have h := hpert ε hε hεδ (s, v) hmem
      change 0 < (a₀ v - L₀ s (embed n v)) + ε * (a₁ v - L₁ s (embed n v)) at h
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      nlinarith
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₀]
      exact add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left h₁ hε)

theorem finite_lexicographic_support_perturbation {n : ℕ}
    (C : Finset (Finset (Lattice n))) (R : Finset (Lattice n))
    (a₀ a₁ : Lattice n → ℝ)
    (L₀ L₁ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ)
    (heq : ∀ s ∈ C, ∀ v ∈ s,
      L₀ s (embed n v) = a₀ v ∧ L₁ s (embed n v) = a₁ v)
    (hlex : ∀ s ∈ C, ∀ v ∈ R, v ∉ s →
      L₀ s (embed n v) < a₀ v ∨
      (L₀ s (embed n v) = a₀ v ∧ L₁ s (embed n v) < a₁ v)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ C,
      (∀ v ∈ s, (L₀ s + ε • L₁ s) (embed n v) = a₀ v + ε * a₁ v) ∧
      (∀ v ∈ R, v ∉ s →
        (L₀ s + ε • L₁ s) (embed n v) < a₀ v + ε * a₁ v) := by
  obtain ⟨δ, hδ, hsmall⟩ := finite_lexicographic_support_perturbation_all_small
    C R a₀ a₁ L₀ L₁ heq hlex
  exact ⟨δ, hδ, hsmall δ hδ le_rfl⟩

end PaperVerification.ToricGeometry
