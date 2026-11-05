module

public import PaperVerification.FinitePavingChowRank

/-! A finite paving indexed only where its actual strata exist. This avoids
introducing an arbitrary dummy open after the last stage. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TotalChow
open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry
open scoped BigOperators

section Filtration

variable (stage : ℕ → Scheme.{0}) [∀ m, AlgebraicGeometry.IsNoetherian (stage m)]
  (base : ∀ m, stage m ⟶ complexBase) [∀ m, LocallyOfFiniteType (base m)]
  (closed : ∀ m, stage (m+1) ⟶ stage m) [∀ m, IsClosedImmersion (closed m)]
  (over_base : ∀ m, closed m ≫ base m = base (m+1))
  (N : ℕ)
  (cell : ∀ m, m < N → (stage m).Opens)
  (complement : ∀ (m : ℕ) (hm : m < N),
    Set.range (closed m) = (Set.range (cell m hm).ι)ᶜ)
  (last_empty : IsEmpty (stage N))
  (budget : ℕ → ℕ)
  (cell_rank : ∀ (m : ℕ) (hm : m < N),
    Module.Finite ℚ (TotalChowQ ((cell m hm).ι ≫ base m)) ∧
      Module.finrank ℚ (TotalChowQ ((cell m hm).ι ≫ base m)) ≤ budget m)

include over_base complement last_empty cell_rank

/-- The inductive bound uses every stratum and reaches the original stage. -/
theorem boundedFinitePaving_total_rank :
    Module.Finite ℚ (TotalChowQ (base 0)) ∧
      Module.finrank ℚ (TotalChowQ (base 0)) ≤ ∑ m ∈ Finset.range N, budget m := by
  have h : ∀ m ≤ N, Module.Finite ℚ (TotalChowQ (base m)) ∧
      Module.finrank ℚ (TotalChowQ (base m)) ≤ ∑ j ∈ Finset.Ico m N, budget j := by
    intro m hm
    induction hm using Nat.decreasingInduction with
    | self =>
      letI := last_empty
      have he := finite_and_finrank_eq_zero_of_empty (base N)
      exact ⟨he.1,by simp only [he.2,Finset.Ico_self,Finset.sum_empty,le_refl]⟩
    | @of_succ m hm ih =>
      have hc := cell_rank m hm
      letI := hc.1
      letI : Module.Finite ℚ (TotalChowQ (closed m ≫ base m)) := by
        rw [over_base m]
        exact ih.1
      have hf := finite_of_closed_open (cell m hm).ι (closed m) (base m) (complement m hm)
      refine ⟨hf,?_⟩
      have hr := finrank_le_closed_add_open (cell m hm).ι (closed m) (base m) (complement m hm)
      rw [over_base m] at hr
      rw [Finset.sum_eq_sum_Ico_succ_bot hm]
      exact hr.trans ((Nat.add_le_add ih.2 hc.2).trans_eq (Nat.add_comm _ _))
  simpa only [Nat.Ico_zero_eq_range] using h 0 (Nat.zero_le N)

end Filtration

end PaperVerification.TotalChow
