module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-! # Decomposition of a finite zero-sum family into minimal zero-sum families -/

@[expose] public section

namespace Cubical

open scoped BigOperators

variable {I W : Type*} [DecidableEq I] [AddCommGroup W]

/-- A nonempty zero-sum family with no nonempty proper zero-sum subfamily.
Indices are retained, so repeated vectors cause no loss of multiplicity. -/
structure IsZeroSumCircuit (f : I → W) (s : Finset I) : Prop where
  nonempty : s.Nonempty
  sum_eq_zero : ∑ i ∈ s, f i = 0
  minimal : ∀ t ⊆ s, t.Nonempty → (∑ i ∈ t, f i) = 0 → t = s

theorem exists_zeroSumCircuit_subset (f : I → W) (s : Finset I)
    (hne : s.Nonempty) (hsum : ∑ i ∈ s, f i = 0) :
    ∃ t ⊆ s, IsZeroSumCircuit f t := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hmin : ∀ t ⊆ s, t.Nonempty → (∑ i ∈ t, f i) = 0 → t = s
    · exact ⟨s, Finset.Subset.rfl, ⟨hne, hsum, hmin⟩⟩
    · push Not at hmin
      obtain ⟨t, hts, htne, htz, htneq⟩ := hmin
      obtain ⟨u, hut, hu⟩ := ih t (Finset.ssubset_iff_subset_ne.mpr ⟨hts, htneq⟩) htne htz
      exact ⟨u, hut.trans hts, hu⟩

/-- A finite partition with minimal zero-sum parts. -/
structure ZeroSumCircuitPartition (f : I → W) (s : Finset I) where
  parts : Finset (Finset I)
  circuit : ∀ t ∈ parts, IsZeroSumCircuit f t
  pairwise_disjoint : (↑parts : Set (Finset I)).Pairwise Disjoint
  cover : parts.biUnion id = s

theorem zeroSumCircuitPartition_exists (f : I → W) (s : Finset I)
    (hsum : ∑ i ∈ s, f i = 0) : Nonempty (ZeroSumCircuitPartition f s) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s = ∅
    · subst s
      exact ⟨⟨∅, by simp, by simp, by simp⟩⟩
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
      obtain ⟨t, hts, ht⟩ := exists_zeroSumCircuit_subset f s hne hsum
      have hstrict : s \ t ⊂ s := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        obtain ⟨i, hi⟩ := ht.nonempty
        have hin : i ∈ s \ t := by
          rw [heq]
          exact hts hi
        exact (Finset.mem_sdiff.mp hin).2 hi
      have hrem : ∑ i ∈ s \ t, f i = 0 := by
        have h := Finset.sum_sdiff hts (f := f)
        simpa [hsum, ht.sum_eq_zero] using h
      obtain ⟨p⟩ := ih (s \ t) hstrict hrem
      have hpartsub : ∀ u ∈ p.parts, u ⊆ s \ t := by
        intro u hu i hi
        rw [← p.cover]
        exact Finset.mem_biUnion.mpr ⟨u, hu, hi⟩
      have hdisj : ∀ u ∈ p.parts, Disjoint t u := by
        intro u hu
        apply Finset.disjoint_left.mpr
        intro i hit hiu
        exact (Finset.mem_sdiff.mp (hpartsub u hu hiu)).2 hit
      refine ⟨⟨insert t p.parts, ?_, ?_, ?_⟩⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ht
        · exact p.circuit u hu
      · intro u hu v hv huv
        rcases Finset.mem_insert.mp hu with rfl | hu
        · rcases Finset.mem_insert.mp hv with rfl | hv
          · exact (huv rfl).elim
          · exact hdisj v hv
        · rcases Finset.mem_insert.mp hv with rfl | hv
          · exact (hdisj u hu).symm
          · exact p.pairwise_disjoint hu hv huv
      · rw [Finset.biUnion_insert, p.cover]
        exact Finset.union_sdiff_of_subset hts

end Cubical
