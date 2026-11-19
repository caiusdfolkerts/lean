module
public import VolumePolynomials.BodyOperations
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Reading subspace constraints directly from volume evaluations

For bodies translated to contain zero, the linear hull of a Minkowski sum is
the sum of their linear hulls. In dimension three, pairwise zero volumes and a
positive triple volume force the three hulls to be lines. This proof does not
assume any sign property of mixed coefficients.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials

section Hull
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def linearHull (K : ConvexBody E) : Submodule ℝ E := Submodule.span ℝ (K : Set E)

theorem mem_linearHull {K : ConvexBody E} {x : E} (hx : x ∈ K) : x ∈ linearHull K :=
  Submodule.subset_span hx

theorem linearHull_mono {K L : ConvexBody E} (h : K ≤ L) : linearHull K ≤ linearHull L :=
  Submodule.span_mono h

theorem zero_mem_body_add {K L : ConvexBody E} (hK : (0 : E) ∈ K) (hL : (0 : E) ∈ L) :
    (0 : E) ∈ K + L := Set.mem_add.mpr ⟨0, hK, 0, hL, zero_add 0⟩

theorem linearHull_add {K L : ConvexBody E} (hK : (0 : E) ∈ K) (hL : (0 : E) ∈ L) :
    linearHull (K + L) = linearHull K ⊔ linearHull L := by
  first
  | apply le_antisymm
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_add.mp hz with ⟨x, hx, y, hy, rfl⟩
      exact Submodule.add_mem _
        ((show linearHull K ≤ linearHull K ⊔ linearHull L from le_sup_left)
          (mem_linearHull hx))
        ((show linearHull L ≤ linearHull K ⊔ linearHull L from le_sup_right)
          (mem_linearHull hy))
    · apply sup_le
      · apply Submodule.span_le.mpr
        intro x hx
        exact mem_linearHull (Set.mem_add.mpr ⟨x, hx, 0, hL, add_zero x⟩)
      · apply Submodule.span_le.mpr
        intro y hy
        exact mem_linearHull (Set.mem_add.mpr ⟨0, hK, y, hy, zero_add y⟩)

theorem affineSpan_eq_linearHull {K : ConvexBody E} (hK : (0 : E) ∈ K) :
    affineSpan ℝ (K : Set E) = (linearHull K).toAffineSubspace :=
  affineSpan_eq_span_of_zero_mem (mem_affineSpan ℝ hK)

end Hull

theorem bodyVolume_pos_iff_linearHull_eq_top {d : ℕ} {K : Body d}
    (hK : (0 : Space d) ∈ K) : 0 < bodyVolume K ↔ linearHull K = ⊤ := by
  first
  | have hreal : 0 < bodyVolume K ↔ 0 < volume (K : Set (Space d)) := by
      constructor
      · intro h
        exact (ENNReal.toReal_pos_iff.mp h).1
      · intro h
        exact ENNReal.toReal_pos h.ne' (bodyVolume_finite K)
    have hpos : 0 < volume (K : Set (Space d)) ↔
        (interior (K : Set (Space d))).Nonempty := by
      rw [pos_iff_ne_zero, ← measure_interior_of_null_frontier
        (K.convex.addHaar_frontier volume)]
      simpa only [Set.nonempty_iff_ne_empty] using
        not_congr (isOpen_interior.measure_eq_zero_iff volume)
    rw [hreal, hpos, K.convex.interior_nonempty_iff_affineSpan_eq_top,
      affineSpan_eq_linearHull hK]
    constructor
    · intro h
      simpa only [Submodule.toAffineSubspace_direction, AffineSubspace.direction_top] using
        congrArg AffineSubspace.direction h
    · intro h
      rw [h]
      rfl

theorem bodyVolume_eq_zero_iff_linearHull_ne_top {d : ℕ} {K : Body d}
    (hK : (0 : Space d) ∈ K) : bodyVolume K = 0 ↔ linearHull K ≠ ⊤ := by
  first
  | constructor
    · intro h hz
      have hp := (bodyVolume_pos_iff_linearHull_eq_top hK).mpr hz
      rw [h] at hp
      exact lt_irrefl 0 hp
    · intro h
      apply le_antisymm _ (bodyVolume_nonneg K)
      apply le_of_not_gt
      intro hp
      exact h ((bodyVolume_pos_iff_linearHull_eq_top hK).mp hp)

section ThreeDimensions
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem finrank_le_one_of_pair_sums_proper (U V W : Submodule ℝ E)
    (hdim : finrank ℝ E = 3) (hUV : U ⊔ V ≠ ⊤) (hUW : U ⊔ W ≠ ⊤)
    (hfull : U ⊔ V ⊔ W = ⊤) : finrank ℝ U ≤ 1 := by
  first
  | by_contra h
    have hU : 2 ≤ finrank ℝ U := by omega
    have hUVdim : finrank ℝ (U ⊔ V : Submodule ℝ E) ≤ 2 := by
      have hh := Submodule.finrank_lt hUV
      rw [hdim] at hh
      omega
    have hUWdim : finrank ℝ (U ⊔ W : Submodule ℝ E) ≤ 2 := by
      have hh := Submodule.finrank_lt hUW
      rw [hdim] at hh
      omega
    have hUVeq : U = U ⊔ V :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (hUVdim.trans hU)
    have hUWeq : U = U ⊔ W :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (hUWdim.trans hU)
    have hVU : V ≤ U := le_sup_right.trans_eq hUVeq.symm
    have hWU : W ≤ U := le_sup_right.trans_eq hUWeq.symm
    have hfullU : U ⊔ V ⊔ W ≤ U := sup_le (sup_le le_rfl hVU) hWU
    rw [hfull] at hfullU
    exact hUV (by rw [top_unique hfullU, top_sup_eq])

theorem finrank_eq_one_of_pair_sums_proper (U V W : Submodule ℝ E)
    (hdim : finrank ℝ E = 3) (hUV : U ⊔ V ≠ ⊤) (hUW : U ⊔ W ≠ ⊤)
    (hVW : V ⊔ W ≠ ⊤) (hfull : U ⊔ V ⊔ W = ⊤) : finrank ℝ U = 1 := by
  first
  | apply le_antisymm (finrank_le_one_of_pair_sums_proper U V W hdim hUV hUW hfull)
    apply Submodule.one_le_finrank_iff.mpr
    intro hU
    apply hVW
    simpa only [hU, bot_sup_eq] using hfull

theorem finrank_le_one_of_three_pair_sums_proper (U A B C : Submodule ℝ E)
    (hdim : finrank ℝ E = 3) (hUA : U ⊔ A ≠ ⊤) (hUB : U ⊔ B ≠ ⊤)
    (hUC : U ⊔ C ≠ ⊤) (hABC : A ⊔ B ⊔ C = ⊤) : finrank ℝ U ≤ 1 := by
  first
  | by_contra h
    have hU : 2 ≤ finrank ℝ U := by omega
    have hsubset : ∀ V : Submodule ℝ E, U ⊔ V ≠ ⊤ → V ≤ U := by
      intro V hV
      have hdimUV : finrank ℝ (U ⊔ V : Submodule ℝ E) ≤ 2 := by
        have hh := Submodule.finrank_lt hV
        rw [hdim] at hh
        omega
      have heq : U = U ⊔ V :=
        Submodule.eq_of_le_of_finrank_le le_sup_left (hdimUV.trans hU)
      exact le_sup_right.trans_eq heq.symm
    have hle : A ⊔ B ⊔ C ≤ U :=
      sup_le (sup_le (hsubset A hUA) (hsubset B hUB)) (hsubset C hUC)
    rw [hABC] at hle
    exact hUA (by rw [top_unique hle, top_sup_eq])

end ThreeDimensions

/-- Three compact convex bodies in three-space have one-dimensional hulls when
every pair has zero volume and the triple has positive volume. -/
theorem frame_linearHulls_are_lines (A B C : Body 3)
    (hA : (0 : Space 3) ∈ A) (hB : (0 : Space 3) ∈ B) (hC : (0 : Space 3) ∈ C)
    (hAB : bodyVolume (A + B) = 0) (hAC : bodyVolume (A + C) = 0)
    (hBC : bodyVolume (B + C) = 0) (hABC : 0 < bodyVolume (A + B + C)) :
    finrank ℝ (linearHull A) = 1 ∧ finrank ℝ (linearHull B) = 1 ∧
      finrank ℝ (linearHull C) = 1 := by
  first
  | have hUV := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hA hB)).mp hAB
    have hUW := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hA hC)).mp hAC
    have hVW := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hB hC)).mp hBC
    have hfull := (bodyVolume_pos_iff_linearHull_eq_top
      (zero_mem_body_add (zero_mem_body_add hA hB) hC)).mp hABC
    rw [linearHull_add hA hB] at hUV
    rw [linearHull_add hA hC] at hUW
    rw [linearHull_add hB hC] at hVW
    rw [linearHull_add (zero_mem_body_add hA hB) hC, linearHull_add hA hB] at hfull
    have hdim : finrank ℝ (Space 3) = 3 := by simp [Space]
    refine ⟨finrank_eq_one_of_pair_sums_proper _ _ _ hdim hUV hUW hVW hfull, ?_, ?_⟩
    · apply finrank_eq_one_of_pair_sums_proper (linearHull B) (linearHull A) (linearHull C)
        hdim (by simpa [sup_comm] using hUV) hVW hUW
      simpa [sup_comm, sup_left_comm, sup_assoc] using hfull
    · apply finrank_eq_one_of_pair_sums_proper (linearHull C) (linearHull A) (linearHull B)
        hdim (by simpa [sup_comm] using hUW) (by simpa [sup_comm] using hVW) hUV
      simpa [sup_comm, sup_left_comm, sup_assoc] using hfull

/-- A nonempty compact convex body with one-dimensional linear hull is an
actual closed segment. The endpoints are attained extrema of a linear
coordinate, including the possibility of a degenerate segment. -/
theorem exists_segment_of_finrank_linearHull_eq_one {d : ℕ} (K : Body d)
    (hK : finrank ℝ (linearHull K) = 1) :
    ∃ a b : Space d, a ∈ K ∧ b ∈ K ∧ (K : Set (Space d)) = segment ℝ a b := by
  first
  | have hnonzero : linearHull K ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hK
      exact Nat.zero_ne_one hK
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnonzero
    have hspan : linearHull K = ℝ ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hK hv hv0
    obtain ⟨i, hi⟩ : ∃ i : Fin d, v i ≠ 0 := by
      by_contra h
      apply hv0
      funext i
      exact not_not.mp (fun hi => h ⟨i, hi⟩)
    let f : Space d →L[ℝ] ℝ := (v i)⁻¹ • ContinuousLinearMap.proj i
    have hreconstruct : ∀ x ∈ linearHull K, f x • v = x := by
      intro x hx
      rw [hspan] at hx
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
      change ((v i)⁻¹ * (r * v i)) • v = r • v
      congr 1
      field_simp
    obtain ⟨a, ha, hmin⟩ := K.isCompact.exists_isMinOn K.nonempty f.continuous.continuousOn
    obtain ⟨b, hb, hmax⟩ := K.isCompact.exists_isMaxOn K.nonempty f.continuous.continuousOn
    refine ⟨a, b, ha, hb, subset_antisymm ?_ (K.convex.segment_subset ha hb)⟩
    intro x hx
    have hfx : f x ∈ segment ℝ (f a) (f b) := by
      rw [segment_eq_Icc (hmin hb)]
      exact ⟨hmin hx, hmax hx⟩
    change f.toLinearMap.toAffineMap x ∈
      segment ℝ (f.toLinearMap.toAffineMap a) (f.toLinearMap.toAffineMap b) at hfx
    rw [← image_segment ℝ f.toLinearMap.toAffineMap a b] at hfx
    obtain ⟨y, hy, hfy⟩ := hfx
    change f y = f x at hfy
    have hyK := K.convex.segment_subset ha hb hy
    have hyx : y = x := by
      calc
        y = f y • v := (hreconstruct y (mem_linearHull hyK)).symm
        _ = f x • v := by rw [hfy]
        _ = x := hreconstruct x (mem_linearHull hx)
    simpa only [hyx] using hy

theorem exists_segment_of_finrank_linearHull_le_one {d : ℕ} (K : Body d)
    (hzero : (0 : Space d) ∈ K) (hK : finrank ℝ (linearHull K) ≤ 1) :
    ∃ a b : Space d, a ∈ K ∧ b ∈ K ∧ (K : Set (Space d)) = segment ℝ a b := by
  first
  | rcases Nat.eq_zero_or_pos (finrank ℝ (linearHull K)) with hdim | hdim
    · have hbot : linearHull K = ⊥ := Submodule.finrank_eq_zero.mp hdim
      refine ⟨0, 0, hzero, hzero, ?_⟩
      rw [segment_same]
      apply subset_antisymm
      · intro x hx
        have hmem := mem_linearHull hx
        rw [hbot] at hmem
        simpa only [Submodule.mem_bot, Set.mem_singleton_iff] using hmem
      · exact singleton_subset_iff.mpr hzero
    · exact exists_segment_of_finrank_linearHull_eq_one K (by omega)

/-- Testing zero volume against the three spanning frame lines forces each
additional compact convex body to be a segment (possibly a point). -/
theorem body_is_segment_of_three_zero_volumes (H A B C : Body 3)
    (hH : (0 : Space 3) ∈ H) (hA : (0 : Space 3) ∈ A)
    (hB : (0 : Space 3) ∈ B) (hC : (0 : Space 3) ∈ C)
    (hHA : bodyVolume (H + A) = 0) (hHB : bodyVolume (H + B) = 0)
    (hHC : bodyVolume (H + C) = 0) (hABC : 0 < bodyVolume (A + B + C)) :
    ∃ a b : Space 3, a ∈ H ∧ b ∈ H ∧ (H : Set (Space 3)) = segment ℝ a b := by
  first
  | apply exists_segment_of_finrank_linearHull_le_one H hH
    have hUA := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hH hA)).mp hHA
    have hUB := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hH hB)).mp hHB
    have hUC := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hH hC)).mp hHC
    have hfull := (bodyVolume_pos_iff_linearHull_eq_top
      (zero_mem_body_add (zero_mem_body_add hA hB) hC)).mp hABC
    rw [linearHull_add hH hA] at hUA
    rw [linearHull_add hH hB] at hUB
    rw [linearHull_add hH hC] at hUC
    rw [linearHull_add (zero_mem_body_add hA hB) hC, linearHull_add hA hB] at hfull
    exact finrank_le_one_of_three_pair_sums_proper _ _ _ _ (by simp [Space])
      hUA hUB hUC hfull

/-- A zero volume test against a two-dimensional body forces containment in
that body's plane once both bodies have been translated to contain zero. -/
theorem linearHull_le_of_volume_zero_sum (K L : Body 3)
    (hK : (0 : Space 3) ∈ K) (hL : (0 : Space 3) ∈ L)
    (hdimL : finrank ℝ (linearHull L) = 2)
    (hvol : bodyVolume (K + L) = 0) : linearHull K ≤ linearHull L := by
  first
  | have hproper := (bodyVolume_eq_zero_iff_linearHull_ne_top
      (zero_mem_body_add hK hL)).mp hvol
    rw [linearHull_add hK hL] at hproper
    have hdim : finrank ℝ (linearHull K ⊔ linearHull L : Submodule ℝ (Space 3)) ≤ 2 := by
      have h := Submodule.finrank_lt hproper
      have hspace : finrank ℝ (Space 3) = 3 := by simp [Space]
      rw [hspace] at h
      omega
    have heq : linearHull L = linearHull K ⊔ linearHull L :=
      Submodule.eq_of_le_of_finrank_le le_sup_right (hdim.trans_eq hdimL.symm)
    exact le_sup_left.trans_eq heq.symm

theorem body_subset_linearHull_of_volume_zero_sum (K L : Body 3)
    (hK : (0 : Space 3) ∈ K) (hL : (0 : Space 3) ∈ L)
    (hdimL : finrank ℝ (linearHull L) = 2)
    (hvol : bodyVolume (K + L) = 0) : (K : Set (Space 3)) ⊆ linearHull L := by
  first
  | intro x hx
    exact linearHull_le_of_volume_zero_sum K L hK hL hdimL hvol (mem_linearHull hx)

/-- All three members of a volume-calibrated frame are genuine segments. -/
theorem frame_bodies_are_segments (A B C : Body 3)
    (hA : (0 : Space 3) ∈ A) (hB : (0 : Space 3) ∈ B) (hC : (0 : Space 3) ∈ C)
    (hAB : bodyVolume (A + B) = 0) (hAC : bodyVolume (A + C) = 0)
    (hBC : bodyVolume (B + C) = 0) (hABC : 0 < bodyVolume (A + B + C)) :
    (∃ a b : Space 3, a ∈ A ∧ b ∈ A ∧ (A : Set (Space 3)) = segment ℝ a b) ∧
    (∃ a b : Space 3, a ∈ B ∧ b ∈ B ∧ (B : Set (Space 3)) = segment ℝ a b) ∧
    (∃ a b : Space 3, a ∈ C ∧ b ∈ C ∧ (C : Set (Space 3)) = segment ℝ a b) := by
  first
  | obtain ⟨ha, hb, hc⟩ := frame_linearHulls_are_lines A B C hA hB hC hAB hAC hBC hABC
    exact ⟨exists_segment_of_finrank_linearHull_eq_one A ha,
      exists_segment_of_finrank_linearHull_eq_one B hb,
      exists_segment_of_finrank_linearHull_eq_one C hc⟩

end VolumePolynomials
