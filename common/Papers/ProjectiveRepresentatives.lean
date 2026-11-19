module
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Basic.Real.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Push

@[expose] public section

noncomputable section

namespace Papers.RationalityTen

/-- A choice of one genuine nonzero vector on each projective point.
Zero labels are kept separately and receive no representative constraint. -/
structure ProjectiveRepresentatives {ι W : Type*}
    [Fintype ι] [AddCommGroup W] [Module ℝ W] (p : ι → W) where
  support : Finset ι
  nonzero : ∀ i ∈ support, p i ≠ 0
  independent : ∀ i ∈ support, ∀ j ∈ support, i ≠ j →
    LinearIndependent ℝ ![p i,p j]
  index : ι → ι
  coefficient : ι → ℝ
  index_mem : ∀ i, p i ≠ 0 → index i ∈ support
  coefficient_ne_zero : ∀ i, p i ≠ 0 → coefficient i ≠ 0
  eq_smul : ∀ i, p i ≠ 0 → coefficient i • p (index i) = p i

theorem exists_projectiveRepresentatives
    {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℝ W]
    (p : ι → W) : Nonempty (ProjectiveRepresentatives p) := by
  classical
  let good : Finset ι → Prop := fun S =>
    (∀ i ∈ S, p i ≠ 0) ∧
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → LinearIndependent ℝ ![p i,p j]
  let candidates : Finset (Finset ι) := Finset.univ.filter good
  have hne : candidates.Nonempty := ⟨∅,by simp [candidates,good]⟩
  obtain ⟨S,hS,hmax⟩ := Finset.exists_max_image candidates Finset.card hne
  have hgood : good S := (Finset.mem_filter.mp hS).2
  have hrep : ∀ i, p i ≠ 0 →
      ∃ j ∈ S, ∃ c : ℝ, c ≠ 0 ∧ c • p j = p i := by
    intro i hi
    have hdep : ∃ j ∈ S, ¬ LinearIndependent ℝ ![p j,p i] := by
      by_contra h
      push_neg at h
      have hiS : i ∉ S := by
        intro hiS
        have hli := h i hiS
        have hh := (LinearIndependent.pair_iff' hi).mp hli 1
        exact hh (one_smul ℝ (p i))
      have hins : good (insert i S) := by
        constructor
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hi
          · exact hgood.1 j hj
        · intro j hj k hk hjk
          rcases Finset.mem_insert.mp hj with rfl | hjs
          · rcases Finset.mem_insert.mp hk with rfl | hks
            · exact (hjk rfl).elim
            · exact LinearIndependent.pair_symm_iff.mp (h k hks)
          · rcases Finset.mem_insert.mp hk with rfl | hks
            · exact h j hjs
            · exact hgood.2 j hjs k hks hjk
      have hcard := hmax (insert i S) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hins⟩)
      rw [Finset.card_insert_of_notMem hiS] at hcard
      omega
    obtain ⟨j,hj,hdep⟩ := hdep
    rw [LinearIndependent.pair_iff' (hgood.1 j hj)] at hdep
    push_neg at hdep
    obtain ⟨c,hc⟩ := hdep
    have hc0 : c ≠ 0 := by
      intro hc0
      exact hi (by simpa [hc0] using hc.symm)
    exact ⟨j,hj,c,hc0,hc⟩
  let index : ι → ι := fun i =>
    if hi : p i = 0 then i else Classical.choose (hrep i hi)
  let coefficient : ι → ℝ := fun i =>
    if hi : p i = 0 then 0 else Classical.choose (Classical.choose_spec (hrep i hi)).2
  refine ⟨{
    support := S
    nonzero := hgood.1
    independent := hgood.2
    index := index
    coefficient := coefficient
    index_mem := ?_
    coefficient_ne_zero := ?_
    eq_smul := ?_ }⟩
  · intro i hi
    simpa [index,hi] using (Classical.choose_spec (hrep i hi)).1
  · intro i hi
    simpa [coefficient,hi] using
      (Classical.choose_spec (Classical.choose_spec (hrep i hi)).2).1
  · intro i hi
    simpa [index,coefficient,hi] using
      (Classical.choose_spec (Classical.choose_spec (hrep i hi)).2).2

end Papers.RationalityTen
