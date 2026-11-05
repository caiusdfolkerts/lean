module
public import normal_projective.admissible_projectivity
public import normal_projective.geometry
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
/-! # Uniform boundedness and compact exclusion for nearby halfspace systems -/
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace NormalProjective
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

abbrev HalfspaceData (ι E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (ι → E →L[ℝ] ℝ) × (ι → ℝ)

def dataRegion (p : HalfspaceData ι E) : Set E :=
  halfspaceRegion (fun i => (p.1 i).toLinearMap) p.2

theorem bounded_normals_separate_directions
    (f : ι → E →L[ℝ] ℝ)
    (hb : Bornology.IsBounded (dataRegion (f, fun _ => 1))) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E, ‖v‖ = 1 → ∃ i, c < f i v := by
  classical
  obtain ⟨R, hR, hbound⟩ := hb.exists_pos_norm_le
  refine ⟨1 / (R + 1), by positivity, ?_⟩
  intro v hv
  have hnP : (R + 1) • v ∉ dataRegion (f, fun _ => 1) := by
    intro hP
    have hh := hbound ((R + 1) • v) hP
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hv, mul_one] at hh
    linarith
  change ¬∀ i, f i ((R + 1) • v) ≤ 1 at hnP
  obtain ⟨i, hi⟩ := not_forall.mp hnP
  refine ⟨i, (div_lt_iff₀ (by linarith : 0 < R + 1)).mpr ?_⟩
  have hi' : 1 < (R + 1) * f i v := by
    simpa only [map_smul, smul_eq_mul] using lt_of_not_ge hi
  nlinarith

theorem nearby_region_norm_bound
    (f g : ι → E →L[ℝ] ℝ) (k : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (hsep : ∀ v : E, ‖v‖ = 1 → ∃ i, c < f i v)
    (hnear : ∀ i, ‖g i - f i‖ < c / 2) (hk : ∀ i, k i ≤ 2)
    {x : E} (hx : x ∈ dataRegion (g, k)) :
    ‖x‖ ≤ 4 / c := by
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]
    positivity
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let v : E := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnx),
      ne_of_gt hnx]
  obtain ⟨i, hi⟩ := hsep v hv
  have hd : |g i v - f i v| ≤ ‖g i - f i‖ := by
    simpa only [ContinuousLinearMap.sub_apply, Real.norm_eq_abs, hv, mul_one]
      using (g i - f i).le_opNorm v
  have hlower : c / 2 < g i v := by
    have hdiff := neg_abs_le (g i v - f i v)
    have hn := hnear i
    linarith
  have hscale : ‖x‖ * g i v = g i x := by
    simp [v, map_smul, smul_eq_mul, mul_assoc, ne_of_gt hnx]
  have hh := mul_lt_mul_of_pos_left hlower hnx
  rw [hscale] at hh
  have hxi : g i x ≤ 2 := (hx i).trans (hk i)
  apply le_of_lt
  apply (lt_div_iff₀ hc).mpr
  nlinarith

theorem dataRegion_closed (p : HalfspaceData ι E) : IsClosed (dataRegion p) :=
  isClosed_halfspaceRegion (fun i => (p.1 i).toLinearMap) p.2

theorem strict_mem_dataRegion_interior (p : HalfspaceData ι E) {x : E}
    (hx : ∀ i, p.1 i x < p.2 i) : x ∈ interior (dataRegion p) := by
  let U : Set E := {y | ∀ i, p.1 i y < p.2 i}
  have hU : IsOpen U := by
    simpa only [U, Set.ofPred_forall] using
      (isOpen_iInter_of_finite fun i => isOpen_lt (p.1 i).continuous continuous_const)
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy i => (hy i).le))

theorem normalized_data_eventually_bounded
    (f : ι → E →L[ℝ] ℝ)
    (hb : Bornology.IsBounded (dataRegion (f, fun _ => 1))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ p : HalfspaceData ι E in 𝓝 (f, fun _ => 1),
        dataRegion p ⊆ Metric.closedBall 0 C ∧
        0 ∈ interior (dataRegion p) := by
  classical
  obtain ⟨c, hc, hsep⟩ := bounded_normals_separate_directions f hb
  have hnear : ∀ i, ∀ᶠ p : HalfspaceData ι E in 𝓝 (f, fun _ => 1),
      ‖p.1 i - f i‖ < c / 2 ∧ 0 < p.2 i ∧ p.2 i < 2 := by
    intro i
    have hopen : IsOpen {p : HalfspaceData ι E |
        ‖p.1 i - f i‖ < c / 2 ∧ 0 < p.2 i ∧ p.2 i < 2} := by
      apply IsOpen.inter
      · exact isOpen_lt
          (show Continuous (fun p : HalfspaceData ι E => ‖p.1 i - f i‖) from by fun_prop)
          continuous_const
      · exact (isOpen_lt continuous_const ((continuous_apply i).comp continuous_snd)).inter
          (isOpen_lt ((continuous_apply i).comp continuous_snd) continuous_const)
    apply hopen.mem_nhds
    simp [hc]
  refine ⟨4 / c, by positivity, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hnear] with p hp
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact nearby_region_norm_bound f p.1 p.2 hc hsep (fun i => (hp i).1)
      (fun i => (hp i).2.2.le) hx
  · apply strict_mem_dataRegion_interior
    intro i
    simpa using (hp i).2.1

/-- Feasibility on a fixed compact set is closed in all halfspace parameters. -/
theorem compact_feasibility_isClosed
    (K : Set E) (hK : IsCompact K) (I : Set ι) :
    IsClosed {p : HalfspaceData ι E | ∃ x ∈ K,
      x ∈ dataRegion p ∧ ∀ i ∈ I, p.1 i x = p.2 i} := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set ((HalfspaceData ι E) × K) :=
    {q | q.2.val ∈ dataRegion q.1 ∧ ∀ i ∈ I, q.1.1 i q.2.val = q.1.2 i}
  have hS : IsClosed S := by
    apply IsClosed.inter
    · change IsClosed {q : HalfspaceData ι E × K | ∀ i, q.1.1 i q.2.val ≤ q.1.2 i}
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_le <;> fun_prop
    · change IsClosed {q : HalfspaceData ι E × K | ∀ i ∈ I, q.1.1 i q.2.val = q.1.2 i}
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro hi
      apply isClosed_eq <;> fun_prop
  have hh := isClosedMap_fst_of_compactSpace S hS
  convert hh using 1
  ext p
  change (∃ x ∈ K, x ∈ dataRegion p ∧ ∀ i ∈ I, p.1 i x = p.2 i) ↔ p ∈ Prod.fst '' S
  constructor
  · rintro ⟨x, hxK, hxP, hxI⟩
    exact ⟨(p, ⟨x, hxK⟩), ⟨hxP, hxI⟩, rfl⟩
  · rintro ⟨⟨q, x⟩, hq, hqp⟩
    change q = p at hqp
    subst q
    exact ⟨x.val, x.property, hq⟩

end NormalProjective

