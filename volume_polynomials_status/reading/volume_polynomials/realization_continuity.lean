module
public import VolumePolynomials.Definitions
public import VolumePolynomials.BodyTopology
public import VolumePolynomials.BodyContinuity
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# Closed realization relation and compact bounded coefficient locus

These statements concern the actual volume function of arbitrary compact convex
bodies. Polynomial existence is not assumed. The finite-dimensional space of
homogeneous coefficients embeds as a closed subspace of all functions on the
nonnegative orthant; this avoids assuming a coefficient-extraction formula.
-/

noncomputable section
open Set MeasureTheory Finset Topology
open scoped Pointwise BigOperators

namespace VolumePolynomials

abbrev NonnegativeWeights (n : ℕ) := {t : Fin n → ℝ // ∀ i, 0 ≤ t i}

def evaluationEmbedding (n d : ℕ) :
    Coefficients n d →ₗ[ℝ] (NonnegativeWeights n → ℝ) where
  toFun c t := evaluate c t.1
  map_add' c e := by
    funext t
    simp [evaluate, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext t
    simp [evaluate, Finset.mul_sum, mul_assoc]

theorem evaluationEmbedding_injective (n d : ℕ) :
    Function.Injective (evaluationEmbedding n d) := by
  intro c e h
  apply coefficients_eq_of_evaluate_nonneg
  intro t ht
  exact congrFun h ⟨t, ht⟩

theorem isClosedEmbedding_evaluation (n d : ℕ) :
    IsClosedEmbedding (evaluationEmbedding n d) :=
  LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (evaluationEmbedding_injective n d))

theorem continuous_evaluate {n d : ℕ} (t : Fin n → ℝ) :
    Continuous (fun c : Coefficients n d => evaluate c t) := by
  unfold evaluate
  fun_prop

theorem continuous_weightedSum {n d : ℕ} (t : Fin n → ℝ) :
    Continuous (fun K : Fin n → Body d => weightedSum K t) := by
  unfold weightedSum
  fun_prop

theorem continuous_bodyVolume (d : ℕ) : Continuous (bodyVolume (d := d)) :=
  continuous_convexBody_realMeasure (volume : Measure (Space d))

theorem continuous_volumeFunction {n d : ℕ} (t : Fin n → ℝ) :
    Continuous (fun K : Fin n → Body d => volumeFunction K t) :=
  (continuous_bodyVolume d).comp (continuous_weightedSum t)

def volumeEvaluation {n d : ℕ} (K : Fin n → Body d) : NonnegativeWeights n → ℝ :=
  fun t => volumeFunction K t.1

theorem continuous_volumeEvaluation (n d : ℕ) :
    Continuous (volumeEvaluation (n := n) (d := d)) := by
  apply continuous_pi
  intro t
  exact continuous_volumeFunction t.1

theorem realizes_iff_evaluation_eq {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} : Realizes K c ↔ evaluationEmbedding n d c = volumeEvaluation K := by
  constructor
  · intro h
    funext t
    exact h t.1 t.2
  · intro h t ht
    exact congrFun h ⟨t, ht⟩

theorem isClosed_realizes (n d : ℕ) :
    IsClosed {p : (Fin n → Body d) × Coefficients n d | Realizes p.1 p.2} := by
  simp_rw [realizes_iff_evaluation_eq]
  exact isClosed_eq ((isClosedEmbedding_evaluation n d).continuous.comp continuous_snd)
    ((continuous_volumeEvaluation n d).comp continuous_fst)

/-- Existence of a homogeneous volume polynomial passes to every Hausdorff limit
of tuples for which it has already been proved. The argument uses the closed
finite-dimensional evaluation range, so no coefficient convergence or mixed-volume
formula is assumed. -/
theorem exists_realizes_of_tendsto {n d : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Fin n → Body d} {L : ι → Fin n → Body d}
    (hL : Filter.Tendsto L l (𝓝 K))
    (hpoly : ∀ᶠ j in l, ∃ c : Coefficients n d, Realizes (L j) c) :
    ∃ c : Coefficients n d, Realizes K c := by
  have hlim : Filter.Tendsto (fun j => volumeEvaluation (L j)) l (𝓝 (volumeEvaluation K)) :=
    (continuous_volumeEvaluation n d).continuousAt.tendsto.comp hL
  have hmem : volumeEvaluation K ∈ Set.range (evaluationEmbedding n d) := by
    apply (isClosedEmbedding_evaluation n d).isClosed_range.mem_of_tendsto hlim
    filter_upwards [hpoly] with j hj
    obtain ⟨c, hc⟩ := hj
    exact ⟨c, realizes_iff_evaluation_eq.mp hc⟩
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, realizes_iff_evaluation_eq.mpr hc⟩

/-- The set of tuples whose actual volume function is a homogeneous degree-`d`
polynomial is closed. This is an existence statement, not merely uniqueness of
coefficient vectors attached to a tuple. -/
theorem isClosed_tuples_with_volume_polynomial (n d : ℕ) :
    IsClosed {K : Fin n → Body d | ∃ c : Coefficients n d, Realizes K c} := by
  have heq : {K : Fin n → Body d | ∃ c : Coefficients n d, Realizes K c} =
      volumeEvaluation ⁻¹' Set.range (evaluationEmbedding n d) := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_range, realizes_iff_evaluation_eq]
  rw [heq]
  exact (isClosedEmbedding_evaluation n d).isClosed_range.preimage
    (continuous_volumeEvaluation n d)

def boundedTuples (n d : ℕ) (C : Set (Space d)) : Set (Fin n → Body d) :=
  {K | ∀ i, (0 : Space d) ∈ K i ∧ (K i : Set (Space d)) ⊆ C}

theorem isCompact_boundedTuples (n d : ℕ) {C : Set (Space d)} (hC : IsCompact C) :
    IsCompact (boundedTuples n d C) := by
  have h := isCompact_univ_pi (fun _ : Fin n => isCompact_bodies_in_compact hC)
  simpa [Set.pi, boundedTuples] using h

def boundedVolumeLocus (n d : ℕ) (C : Set (Space d)) : Set (Coefficients n d) :=
  {c | ∃ K ∈ boundedTuples n d C, Realizes K c}

theorem boundedVolumeLocus_eq_preimage (n d : ℕ) (C : Set (Space d)) :
    boundedVolumeLocus n d C =
      evaluationEmbedding n d ⁻¹' (volumeEvaluation '' boundedTuples n d C) := by
  ext c
  constructor
  · rintro ⟨K, hK, hc⟩
    exact ⟨K, hK, (realizes_iff_evaluation_eq.mp hc).symm⟩
  · rintro ⟨K, hK, hc⟩
    exact ⟨K, hK, realizes_iff_evaluation_eq.mpr hc.symm⟩

/-- Compactness of the paper's bounded coefficient model, formulated using the
literal geometric realization relation. Lower-dimensional bodies are included. -/
theorem isCompact_boundedVolumeLocus (n d : ℕ) {C : Set (Space d)} (hC : IsCompact C) :
    IsCompact (boundedVolumeLocus n d C) := by
  rw [boundedVolumeLocus_eq_preimage]
  exact (isClosedEmbedding_evaluation n d).isCompact_preimage
    ((isCompact_boundedTuples n d hC).image (continuous_volumeEvaluation n d))

theorem boundedVolumeLocus_subset (n d : ℕ) (C : Set (Space d)) :
    boundedVolumeLocus n d C ⊆ VolumeLocus n d := by
  rintro c ⟨K, _, hK⟩
  exact ⟨K, hK⟩

end VolumePolynomials
