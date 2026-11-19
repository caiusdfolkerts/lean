module

public import Unimodular.ConeInterior

@[expose] public section

open scoped Pointwise Topology
open Filter Set

namespace Unimodular.FacetLine

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The integer sign of a real number. -/
noncomputable def signZ (a : ℝ) : ℤ := if 0 < a then 1 else if a < 0 then -1 else 0

@[simp] theorem signZ_zero : signZ 0 = 0 := by simp [signZ]
theorem signZ_of_pos {a : ℝ} (ha : 0 < a) : signZ a = 1 := by simp [signZ, ha]
theorem signZ_of_neg {a : ℝ} (ha : a < 0) : signZ a = -1 := by
  simp [signZ, ha, not_lt_of_ge ha.le]
@[simp] theorem signZ_neg (a : ℝ) : signZ (-a) = -signZ a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [signZ_of_neg ha, signZ_of_pos (neg_pos.2 ha)]; norm_num
  · simp
  · rw [signZ_of_pos ha, signZ_of_neg (neg_neg_of_pos ha)]

/-- Twice the interior indicator, with value one on the boundary. The boundary value
makes cancellation continuous along lines through a single facet stratum. -/
noncomputable def weight (C : PointedCone ℝ V) (x : V) : ℤ := by
  classical
  exact if x ∈ interior (C : Set V) then 2 else if x ∈ C then 1 else 0

theorem weight_of_interior {C : PointedCone ℝ V} {x : V}
    (hx : x ∈ interior (C : Set V)) : weight C x = 2 := by simp [weight, hx]
theorem weight_of_outside {C : PointedCone ℝ V} {x : V}
    (hx : x ∉ C) : weight C x = 0 := by
  have hi : x ∉ interior (C : Set V) := fun h => hx (interior_subset h)
  simp [weight, hx, hi]
theorem weight_of_boundary {C : PointedCone ℝ V} {x : V}
    (hx : x ∈ C) (hi : x ∉ interior (C : Set V)) : weight C x = 1 := by
  simp [weight, hx, hi]

/-- The exact membership test along a line through the relative interior of a facet.
The face and its supporting normal are actual geometric objects. -/
theorem eventually_line_membership_of_positive {C : PointedCone ℝ V} {x : V}
    (hx : x ∈ C) (hne : MinimalFaces.dominatedCone C x ≠ C)
    (f : V →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker f = Submodule.span ℝ
      (MinimalFaces.dominatedCone C x : Set V))
    {y : V} (hy : y ∈ interior (C : Set V)) (hfy : 0 < f y) (v : V) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (x + t • v ∈ C ↔ 0 ≤ t * f v) ∧
      (x + t • v ∈ interior (C : Set V) ↔ 0 < t * f v) := by
  let F := MinimalFaces.dominatedCone C x
  have hF : F.IsFaceOf C := MinimalFaces.dominatedCone_isFaceOf C x
  have hxF : x ∈ F := MinimalFaces.self_mem_dominatedCone hx
  have hfx : f x = 0 := by
    change x ∈ LinearMap.ker f
    rw [hker]
    exact Submodule.subset_span hxF
  let a : ℝ := f v / f y
  let l : V := v - a • y
  have hl : l ∈ Submodule.span ℝ (F : Set V) := by
    rw [← hker]
    change f (v - a • y) = 0
    simp only [map_sub, map_smul, smul_eq_mul, a]
    rw [div_mul_cancel₀ _ hfy.ne', sub_self]
  obtain ⟨δ, hδ, habs⟩ := MinimalFaces.absorb_span_two_sided hx hl
  have he : ∀ᶠ t : ℝ in 𝓝 0, |t| < δ := by
    have hm : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Metric.ball (0 : ℝ) δ :=
      Metric.ball_mem_nhds (0 : ℝ) hδ
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hm
  filter_upwards [he] with t ht
  have hbase : x + t • l ∈ F := habs t ht.le
  have hval : f (x + t • v) = t * f v := by simp [hfx]
  have hre : x + t • v = (t * a) • y + (x + t • l) := by dsimp [l]; module
  have hnonneg : ∀ z ∈ C, 0 ≤ f z :=
    ConeInterior.normal_nonneg_on_cone hF f hker (interior_subset hy) hfy
  have hinside : 0 < t * f v → x + t • v ∈ interior (C : Set V) := by
    intro hp
    have hta : 0 < t * a := by
      dsimp [a]
      rw [← mul_div_assoc]
      exact div_pos hp hfy
    rw [hre]
    exact ConeInterior.add_mem_interior (ConeInterior.smul_mem_interior hy hta)
      (hF.le hbase)
  have hzero : t * f v = 0 → x + t • v ∈ F := by
    intro hz
    have hta : t * a = 0 := by dsimp [a]; rw [← mul_div_assoc, hz, zero_div]
    rw [hre, hta, zero_smul, zero_add]
    exact hbase
  constructor
  · constructor
    · intro hm
      simpa only [hval] using hnonneg _ hm
    · intro hp
      rcases hp.eq_or_lt with heq | hp
      · exact hF.le (hzero heq.symm)
      · exact interior_subset (hinside hp)
  · constructor
    · intro hm
      have hge : 0 ≤ t * f v := by simpa only [hval] using hnonneg _ (interior_subset hm)
      apply lt_of_le_of_ne hge
      intro hz
      exact hne (ConeInterior.face_eq_of_mem_interior hF (hzero hz.symm) hm)
    · exact hinside

/-- The signed jump of one cone at one of its facet strata. -/
theorem eventually_weight_at_facet {C : PointedCone ℝ V} {x : V}
    (hx : x ∈ C) (hne : MinimalFaces.dominatedCone C x ≠ C)
    (f : V →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker f = Submodule.span ℝ
      (MinimalFaces.dominatedCone C x : Set V))
    {y : V} (hy : y ∈ interior (C : Set V)) (v : V) :
    ∀ᶠ t : ℝ in 𝓝 0,
      weight C (x + t • v) = 1 + signZ (t * f v) * signZ (f y) := by
  have hfy : f y ≠ 0 := ConeInterior.normal_ne_zero_at_interior
    (MinimalFaces.dominatedCone_isFaceOf C x) hne f hker hy
  rcases lt_or_gt_of_ne hfy with hn | hp
  · have hnegker : LinearMap.ker (-f) = Submodule.span ℝ
        (MinimalFaces.dominatedCone C x : Set V) := by simpa using hker
    have he := eventually_line_membership_of_positive hx hne (-f) hnegker hy
      (by simpa using neg_pos.2 hn) v
    filter_upwards [he] with t ht
    rw [signZ_of_neg hn]
    have hv : t * (-f) v = -(t * f v) := by simp
    rcases lt_trichotomy (t * f v) 0 with h | h | h
    · have hi := ht.2.2 (by rw [hv]; linarith)
      rw [weight_of_interior hi, signZ_of_neg h]; norm_num
    · have hm := ht.1.2 (by rw [hv, h]; norm_num)
      have hi : x + t • v ∉ interior (C : Set V) := by
        intro hi; have hh := ht.2.1 hi; rw [hv, h] at hh; linarith
      rw [weight_of_boundary hm hi, h, signZ_zero]; norm_num
    · have hm : x + t • v ∉ C := by
        intro hm; have hh := ht.1.1 hm; rw [hv] at hh; linarith
      rw [weight_of_outside hm, signZ_of_pos h]; norm_num
  · have he := eventually_line_membership_of_positive hx hne f hker hy hp v
    filter_upwards [he] with t ht
    rw [signZ_of_pos hp]
    rcases lt_trichotomy (t * f v) 0 with h | h | h
    · have hm : x + t • v ∉ C := fun hm => (not_le_of_gt h) (ht.1.1 hm)
      rw [weight_of_outside hm, signZ_of_neg h]; norm_num
    · have hm := ht.1.2 (by rw [h])
      have hi : x + t • v ∉ interior (C : Set V) := by
        intro hi; have hh := ht.2.1 hi; rw [h] at hh; linarith
      rw [weight_of_boundary hm hi, h, signZ_zero]; norm_num
    · rw [weight_of_interior (ht.2.2 h), signZ_of_pos h]; norm_num

theorem eventually_weight_of_interior {C : PointedCone ℝ V} {x : V}
    (hx : x ∈ interior (C : Set V)) (v : V) :
    ∀ᶠ t : ℝ in 𝓝 0, weight C (x + t • v) = weight C x := by
  have hc : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto (0 : ℝ)
  filter_upwards [ht.eventually (isOpen_interior.mem_nhds hx)] with t ht
  rw [weight_of_interior hx, weight_of_interior ht]

theorem eventually_weight_of_outside {C : PointedCone ℝ V} (hC : C.FG) {x : V}
    (hx : x ∉ C) (v : V) :
    ∀ᶠ t : ℝ in 𝓝 0, weight C (x + t • v) = weight C x := by
  have hc : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto (0 : ℝ)
  have he := ht.eventually ((ConeInterior.isClosed_of_fg hC).isOpen_compl.mem_nhds hx)
  filter_upwards [he] with t ht
  rw [weight_of_outside hx, weight_of_outside ht]

end Unimodular.FacetLine
