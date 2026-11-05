import cubical.polytope.monotone
import Mathlib.Algebra.Module.Submodule.Union

/-! # Generic separating heights for finite configurations -/

open Set

namespace LeanEval.Geometry.PlatonicClassification

variable {n : ℕ}

/-- A finite collection of Euclidean points is separated by one linear functional. -/
theorem exists_separating_functional (S : Finset (E n)) :
    ∃ l : E n →L[ℝ] ℝ, Set.InjOn l (S : Set (E n)) := by
  classical
  let I := {p : S × S // p.1 ≠ p.2}
  let v : I → E n := fun p => p.val.1.val - p.val.2.val
  have hv : ∀ p, v p ≠ 0 := by
    intro p
    apply sub_ne_zero.mpr
    intro h
    exact p.property (Subtype.ext h)
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) v hv
  refine ⟨f.toContinuousLinearMap, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  let p : I := ⟨(⟨x, hx⟩, ⟨y, hy⟩), fun h => hne (congrArg Subtype.val h)⟩
  have hp := hf p
  change f (x - y) ≠ 0 at hp
  rw [map_sub] at hp
  exact hp (sub_eq_zero.mpr hxy)

/-- Rank by the number of points strictly below a given height. -/
noncomputable def heightRank (S : Finset (E n)) (l : E n →L[ℝ] ℝ) (x : E n) : ℕ := by
  classical
  exact (S.filter (fun y => l y < l x)).card

theorem heightRank_strictMono (S : Finset (E n)) (l : E n →L[ℝ] ℝ)
    {x y : E n} (hx : x ∈ S) (hxy : l x < l y) :
    heightRank S l x < heightRank S l y := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    obtain ⟨hzS, hzx⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzS, hzx.trans hxy⟩
  · intro heq
    have hxin : x ∈ S.filter (fun z => l z < l y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← heq] at hxin
    exact lt_irrefl _ (Finset.mem_filter.mp hxin).2

theorem heightRank_lt_iff (S : Finset (E n)) (l : E n →L[ℝ] ℝ)
    {x y : E n} (hx : x ∈ S) (hy : y ∈ S) :
    heightRank S l x < heightRank S l y ↔ l x < l y := by
  constructor
  · intro h
    by_contra hnot
    have hle : l y ≤ l x := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · have hrank : heightRank S l y = heightRank S l x := by
        unfold heightRank
        rw [heq]
      omega
    · have hrev := heightRank_strictMono S l hy hlt
      omega
  · exact heightRank_strictMono S l hx

theorem heightRank_injOn (S : Finset (E n)) (l : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn l (S : Set (E n))) :
    Set.InjOn (heightRank S l) (S : Set (E n)) := by
  intro x hx y hy heq
  apply hinj hx hy
  rcases lt_trichotomy (l x) (l y) with hlt | hequal | hgt
  · have h := heightRank_strictMono S l hx hlt
    omega
  · exact hequal
  · have h := heightRank_strictMono S l hy hgt
    omega

end LeanEval.Geometry.PlatonicClassification
