module

public import tau_ceti.analysis.polynomial.continuity_of_roots.basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

noncomputable section

open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace EllipsoidVerification

theorem finite_vertical_separation (s : Finset ℂ) (c : ℝ)
    (hs : ∀ z ∈ s, z.re ≠ c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ s, ε ≤ |z.re - c| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert z s hz ih =>
      obtain ⟨ε, hε, hsep⟩ := ih (fun w hw => hs w (Finset.mem_insert_of_mem hw))
      refine ⟨min ε |z.re - c|, lt_min hε (abs_pos.mpr (sub_ne_zero.mpr
        (hs z (Finset.mem_insert_self _ _)))), ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hsep w hw)

theorem realPart_lt_iff_of_close {z w : ℂ} {c ε : ℝ}
    (hsep : ε ≤ |z.re - c|) (hclose : ‖z - w‖ < ε) :
    z.re < c ↔ w.re < c := by
  have hdist : |z.re - w.re| < ε := by
    have hreal : |z.re - w.re| ≤ ‖z - w‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - w)
    exact hreal.trans_lt hclose
  rcases lt_or_ge z.re c with hz | hz
  · rw [abs_of_neg (sub_neg.mpr hz)] at hsep
    have hh := (abs_lt.mp hdist).1
    constructor
    · intro _
      linarith
    · intro _
      exact hz
  · have hz' : c ≤ z.re := hz
    rw [abs_of_nonneg (sub_nonneg.mpr hz')] at hsep
    have hh := (abs_lt.mp hdist).2
    have hw : c < w.re := by linarith
    simp [not_lt.mpr hz, not_lt.mpr hw.le]

theorem countP_realPart_eq_of_rel {s t : Multiset ℂ} {c ε : ℝ}
    (hsep : ∀ z ∈ s, ε ≤ |z.re - c|)
    (hrel : s.Rel (fun z w => ‖z - w‖ < ε) t) :
    s.countP (fun z => z.re < c) = t.countP (fun z => z.re < c) := by
  classical
  obtain ⟨n, a, b, hs, ht, hab⟩ := Multiset.rel_iff_exists_fin.mp hrel
  rw [hs, ht, Multiset.countP_map, Multiset.countP_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro i hi
  exact realPart_lt_iff_of_close (hsep (a i) (by simp [hs])) (hab i)

/-- Root counts on one side of a vertical line are locally constant as
long as no root crosses the line. Multiplicities are retained throughout. -/
theorem isLocallyConstant_rootCount_left {B : Type*} [TopologicalSpace B]
    {F : B → ℂ[X]} {d : ℕ} (hF : ∀ k ≤ d, Continuous (fun b => (F b).coeff k))
    (hdeg : ∀ b, (F b).degree = d) (c : ℝ)
    (havoid : ∀ b z, z ∈ (F b).roots → z.re ≠ c) :
    IsLocallyConstant (fun b => (F b).roots.countP (fun z => z.re < c)) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro b
  obtain ⟨ε, hε, hsep⟩ := finite_vertical_separation (F b).roots.toFinset c
    (fun z hz => havoid b z (Multiset.mem_toFinset.mp hz))
  filter_upwards [Polynomial.eventually_rel_roots_norm_sub_lt
    (fun k hk => (hF k hk).continuousAt)
    (Filter.Eventually.of_forall hdeg) hε] with b' hb'
  exact (countP_realPart_eq_of_rel
    (fun z hz => hsep z (Multiset.mem_toFinset.mpr hz)) hb').symm

theorem rootCount_left_eq_on_connected {B : Type*} [TopologicalSpace B]
    [PreconnectedSpace B] {F : B → ℂ[X]} {d : ℕ}
    (hF : ∀ k ≤ d, Continuous (fun b => (F b).coeff k))
    (hdeg : ∀ b, (F b).degree = d) (c : ℝ)
    (havoid : ∀ b z, z ∈ (F b).roots → z.re ≠ c) (b₀ b₁ : B) :
    (F b₀).roots.countP (fun z => z.re < c) =
      (F b₁).roots.countP (fun z => z.re < c) :=
  (isLocallyConstant_rootCount_left hF hdeg c havoid).apply_eq_of_preconnectedSpace b₀ b₁

/-- A real interval longer than the sum of `n` interval lengths contains
a cut separated from all `n` centres. This replaces disk-boundary topology
in the quantitative matching argument. -/
theorem exists_cut_away_from_finite_centres {n : ℕ} (a : Fin n → ℝ)
    {u v ρ : ℝ} (hρ : 0 ≤ ρ) (hlength : 2 * n * ρ < v - u) :
    ∃ c ∈ Ioo u v, ∀ i, ρ < |c - a i| := by
  classical
  by_contra h
  push_neg at h
  have hsub : Ioo u v ⊆ ⋃ i, Metric.closedBall (a i) ρ := by
    intro c hc
    obtain ⟨i, hi⟩ := h c hc
    exact mem_iUnion.mpr ⟨i, by simpa only [Metric.mem_closedBall, Real.dist_eq] using hi⟩
  have hμ := (measure_mono hsub).trans
    (measure_iUnion_fintype_le volume (fun i => Metric.closedBall (a i) ρ))
  simp only [Real.volume_Ioo, Real.volume_closedBall, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hμ
  have hnn : 0 ≤ (2 : ℝ) * n * ρ := by positivity
  have hsum : (n : ℝ≥0∞) * ENNReal.ofReal (2 * ρ) = ENNReal.ofReal (2 * n * ρ) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [hsum] at hμ
  exact (not_le_of_gt hlength) ((ENNReal.ofReal_le_ofReal_iff hnn).mp hμ)

end EllipsoidVerification
