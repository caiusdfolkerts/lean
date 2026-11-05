import PaperVerification.ExactSequenceRank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Rank bounds along a finite exact filtration

At each step the original three maps are required to be exact at the middle
term. The theorem does not assume that either outside map is surjective.
It applies to the actual pair sequence once its relative groups have been
computed from the geometry of a stratum.
-/

namespace PaperVerification.FiniteExactFiltration

noncomputable section

open scoped BigOperators

variable {K : Type*} [Field K]
  (V R : ℕ → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, AddCommGroup (R i)] [∀ i, Module K (R i)]
  (f : ∀ i, R i →ₗ[K] V (i + 1))
  (g : ∀ i, V (i + 1) →ₗ[K] V i)
  (hexact : ∀ i, LinearMap.range (f i) = LinearMap.ker (g i))
  (hzero : Subsingleton (V 0))

include f g hexact hzero

/-- The dimension of a filtered object is bounded by the sum of the actual
relative dimensions. The first term is genuinely zero. -/
theorem finite_and_finrank_le_sum [∀ i, Module.Finite K (R i)] (n : ℕ) :
    Module.Finite K (V n) ∧
      Module.finrank K (V n) ≤ ∑ i ∈ Finset.range n, Module.finrank K (R i) := by
  induction n with
  | zero =>
      letI := hzero
      exact ⟨inferInstance, by simp [Module.finrank_zero_of_subsingleton]⟩
  | succ n ih =>
      letI := ih.1
      letI := ExactSequenceRank.finite_middle (f n) (g n) (hexact n)
      refine ⟨inferInstance, ?_⟩
      calc
        Module.finrank K (V (n + 1)) ≤
            Module.finrank K (R n) + Module.finrank K (V n) :=
          ExactSequenceRank.finrank_middle_le (f n) (g n) (hexact n)
        _ ≤ Module.finrank K (R n) +
            ∑ i ∈ Finset.range n, Module.finrank K (R i) :=
          Nat.add_le_add_left ih.2 _
        _ = ∑ i ∈ Finset.range (n + 1), Module.finrank K (R i) := by
          rw [Finset.sum_range_succ, Nat.add_comm]

/-- A stratumwise bound can be substituted only after each actual relative
group has been proved finite and its rank has been bounded. -/
theorem finite_and_finrank_le_bound [∀ i, Module.Finite K (R i)]
    (b : ℕ → ℕ) (hbound : ∀ i, Module.finrank K (R i) ≤ b i) (n : ℕ) :
    Module.Finite K (V n) ∧
      Module.finrank K (V n) ≤ ∑ i ∈ Finset.range n, b i := by
  obtain ⟨hfinite, hrank⟩ := finite_and_finrank_le_sum V R f g hexact hzero n
  exact ⟨hfinite, hrank.trans (Finset.sum_le_sum fun i _ => hbound i)⟩

/-- If every relative group in a degree vanishes, every filtered stage
vanishes in that degree. -/
theorem subsingleton_of_relative_zero (hrelative : ∀ i, Subsingleton (R i)) (n : ℕ) :
    Subsingleton (V n) := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
      letI := ih
      letI := hrelative n
      exact ExactSequenceRank.subsingleton_middle (f n) (g n) (hexact n)

end
end PaperVerification.FiniteExactFiltration
