module

public import Unimodular.FanCycleConverse
public import Unimodular.FanMaximalCones

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.CycleDegree.FullCones

attribute [local instance] Classical.propDecidable

variable {I N V : Type*} [Fintype I] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (S : FullCones I V) {ι : N →+ V} (hι : IsIntegralLattice ι)
  (hToric : ∀ i, IsToricCone ι (S.cone i))

def selectedCones (c : I → ℤ) : Set (PointedCone ℝ V) :=
  {C | ∃ i, c i = 1 ∧ S.cone i = C}

theorem selectedCones_finite (c : I → ℤ) : (S.selectedCones c).Finite :=
  (Set.finite_range S.cone).subset (fun _ ⟨i, _, h⟩ => ⟨i, h⟩)

/-- The actual bundled finite rational salient fan obtained from a complete decomposition. -/
noncomputable def fanOfDecomposition {c : I → ℤ} (hd : S.CompleteDecomposition c) : Fan ι :=
  Fan.ofCones hι (S.selectedCones c) (S.selectedCones_finite c)
    (by rintro _ ⟨i, _, rfl⟩; exact hToric i)
    (by rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩; exact hd.faces i j hi hj)

theorem mem_fanOfDecomposition_cones {c : I → ℤ} (hd : S.CompleteDecomposition c)
    (C : PointedCone ℝ V) : C ∈ (S.fanOfDecomposition hι hToric hd).cones ↔
      ∃ i, c i = 1 ∧ C.IsFaceOf (S.cone i) := by
  simp only [fanOfDecomposition, Fan.mem_ofCones_cones, selectedCones, Set.mem_setOf_eq]
  constructor
  · rintro ⟨D, ⟨i, hi, rfl⟩, hCD⟩
    exact ⟨i, hi, hCD⟩
  · rintro ⟨i, hi, hCi⟩
    exact ⟨S.cone i, ⟨i, hi, rfl⟩, hCi⟩

theorem fanOfDecomposition_complete {c : I → ℤ} (hd : S.CompleteDecomposition c) :
    (S.fanOfDecomposition hι hToric hd).IsComplete := by
  apply (Fan.isComplete_iff _).2
  intro x
  obtain ⟨i, hi, hxi⟩ := hd.cover x
  exact ⟨S.cone i, (S.mem_fanOfDecomposition_cones hι hToric hd _).2
    ⟨i, hi, PointedCone.IsFaceOf.refl _⟩, hxi⟩

theorem full_mem_fanOfDecomposition_iff {c : I → ℤ} (hd : S.CompleteDecomposition c)
    {C : PointedCone ℝ V} (hC : Submodule.span ℝ (C : Set V) = ⊤) :
    C ∈ (S.fanOfDecomposition hι hToric hd).cones ↔
      ∃ i, c i = 1 ∧ S.cone i = C := by
  constructor
  · intro hm
    obtain ⟨i, hi, hCi⟩ := (S.mem_fanOfDecomposition_cones hι hToric hd C).1 hm
    have he : C = S.cone i := by
      by_contra hn
      exact ConeInterior.span_ne_top_of_proper_face hCi hn hC
    exact ⟨i, hi, he.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact (S.mem_fanOfDecomposition_cones hι hToric hd _).2
      ⟨i, hi, PointedCone.IsFaceOf.refl _⟩

theorem coefficient_eq_fan_indicator (hinj : Function.Injective S.cone)
    {c : I → ℤ} (hd : S.CompleteDecomposition c) (i : I) :
    c i = if S.cone i ∈ (S.fanOfDecomposition hι hToric hd).cones then 1 else 0 := by
  by_cases hm : S.cone i ∈ (S.fanOfDecomposition hι hToric hd).cones
  · rw [if_pos hm]
    obtain ⟨j, hj, hji⟩ := (S.full_mem_fanOfDecomposition_iff hι hToric hd (S.full i)).1 hm
    exact hinj hji ▸ hj
  · rw [if_neg hm]
    rcases hd.indicator i with hi | hi
    · exact hi
    · exact (hm ((S.full_mem_fanOfDecomposition_iff hι hToric hd (S.full i)).2
        ⟨i, hi, rfl⟩)).elim

include hι hToric in
/-- Degree-one nonnegative integral cycles are exactly the maximal-cone indicators of
actual complete fans whose maximal cones are drawn from the prescribed finite family. -/
theorem positive_degree_one_iff_fan (hinj : Function.Injective S.cone)
    (c : I → ℤ) {w : V} (hw : S.Generic w) :
    ((∀ i, 0 ≤ c i) ∧ S.IsCycle c ∧ S.multiplicity c w = 1) ↔
      ∃ Φ : Fan ι, Φ.IsComplete ∧
        (∀ i, c i = if S.cone i ∈ Φ.cones then 1 else 0) ∧
        (∀ C ∈ Φ.cones, Submodule.span ℝ (C : Set V) = ⊤ → ∃ i, S.cone i = C) := by
  rw [S.positive_degree_one_iff_completeDecomposition hinj c hw]
  constructor
  · intro hd
    refine ⟨S.fanOfDecomposition hι hToric hd,
      S.fanOfDecomposition_complete hι hToric hd,
      S.coefficient_eq_fan_indicator hι hToric hinj hd, ?_⟩
    intro C hC hfull
    obtain ⟨i, _, hi⟩ := (S.full_mem_fanOfDecomposition_iff hι hToric hd hfull).1 hC
    exact ⟨i, hi⟩
  · rintro ⟨Φ, hΦ, hind, hmax⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [hind i]
      split_ifs <;> simp
    · intro x
      obtain ⟨C, hC, hfull, hxC⟩ := FanMaximalCones.full_cones_cover Φ hΦ x
      obtain ⟨i, rfl⟩ := hmax C hC hfull
      exact ⟨i, by rw [hind i, if_pos hC], hxC⟩
    · intro i j hi hj
      have hmi : S.cone i ∈ Φ.cones := by
        by_contra hn
        rw [hind i, if_neg hn] at hi
        norm_num at hi
      have hmj : S.cone j ∈ Φ.cones := by
        by_contra hn
        rw [hind j, if_neg hn] at hj
        norm_num at hj
      exact Φ.inf_isFaceOf_left hmi hmj

end Unimodular.CycleDegree.FullCones
