import cubical.pl_abstract

/-! Coordinate descriptions of the actual standard affine realization. -/

noncomputable section

namespace Bier

open Set Geometry
open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear

variable {V : Type*} [Fintype V] [DecidableEq V]

def positiveSupport (x : V → ℝ) : Finset V := Finset.univ.filter (fun v => 0 < x v)

@[simp] theorem mem_positiveSupport (x : V → ℝ) (v : V) :
    v ∈ positiveSupport x ↔ 0 < x v := by simp [positiveSupport]

theorem mem_standard_face_iff (s : Finset V) (x : V → ℝ) :
    x ∈ convexHull ℝ ((s.image (fun v => Pi.single v (1 : ℝ)) : Finset (V → ℝ)) : Set (V → ℝ)) ↔
      (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1 ∧ ∀ v ∉ s, x v = 0 := by
  classical
  let e : V → V → ℝ := fun v => Pi.single v 1
  have he : Function.Injective e := Cubical.PL.standardVertex_injective
  constructor
  · intro hx
    obtain ⟨w, hw, hsum, hvec⟩ := mem_convexHull_iff_exists_weights.mp hx
    rw [Finset.sum_image (fun i _ j _ hij => he hij)] at hsum hvec
    have hxv : ∀ v, x v = if v ∈ s then w (e v) else 0 := by
      intro v
      have h := congrFun hvec v
      simpa [e, Finset.sum_apply, Pi.single_apply, eq_comm] using h.symm
    refine ⟨fun v => ?_, ?_, fun v hv => by simp [hxv, hv]⟩
    · rw [hxv]
      split_ifs with hv
      · exact hw _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      · exact le_rfl
    · simp_rw [hxv]
      simpa using hsum
  · rintro ⟨hx, hsum, hzero⟩
    have hsumS : ∑ v ∈ s, x v = 1 := by
      rw [← hsum]
      exact Finset.sum_subset (Finset.subset_univ s) (fun v _ hv => hzero v hv)
    have hvec : (∑ v ∈ s, x v • e v) = x := by
      ext v
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp [e, Pi.single_apply, eq_comm, apply_ite]
      exact hzero v
    rw [← hvec]
    exact (convex_convexHull ℝ _).sum_mem (fun v _ => hx v) hsumS
      (fun v hv => subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))

theorem mem_standardRealization_iff (P : PreAbstractSimplicialComplex V) (x : V → ℝ) :
    x ∈ (standardRealization P).space ↔
      (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1 ∧ positiveSupport x ∈ P.faces := by
  classical
  rw [standardRealization_mem_space]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨hpos, hsum, hzero⟩ := (mem_standard_face_iff s x).mp hx
    have hsub : positiveSupport x ⊆ s := by
      intro v hv
      by_contra hvs
      have := mem_positiveSupport x v |>.mp hv
      rw [hzero v hvs] at this
      exact lt_irrefl _ this
    have hne : (positiveSupport x).Nonempty := by
      by_contra hn
      have hz : ∀ v, x v = 0 := by
        intro v
        apply le_antisymm _ (hpos v)
        exact not_lt.mp (fun hv => hn ⟨v, (mem_positiveSupport x v).mpr hv⟩)
      simp [hz] at hsum
    exact ⟨hpos, hsum, (P.isRelLowerSet_faces hs).2 hsub hne⟩
  · rintro ⟨hpos, hsum, hs⟩
    refine ⟨positiveSupport x, hs, (mem_standard_face_iff _ _).mpr ⟨hpos, hsum, ?_⟩⟩
    intro v hv
    exact le_antisymm (not_lt.mp (by simpa using hv)) (hpos v)

end Bier
