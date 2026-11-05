module
import verification.internal.checkpoint
import verification.internal.extract
public import consolidated.pair_pin_progress01
import all consolidated.pair_pin_progress01
public import consolidated.pair_pin_progress02
import all consolidated.pair_pin_progress02
public import consolidated.rigidity_combined02
import all consolidated.rigidity_combined02
public import consolidated.rigidity_combined03
import all consolidated.rigidity_combined03
public import consolidated.rigidity_combined04
import all consolidated.rigidity_combined04
public import consolidated.rigidity_combined05
import all consolidated.rigidity_combined05
public import consolidated.rigidity_combined06
import all consolidated.rigidity_combined06
public import consolidated.rigidity_combined07
import all consolidated.rigidity_combined07
public import consolidated.rigidity_combined_prepared
import all consolidated.rigidity_combined_prepared
public import consolidated.rigidity_foundations01
import all consolidated.rigidity_foundations01
public import consolidated.rigidity_foundations02
import all consolidated.rigidity_foundations02
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import consolidated.rigidity_main_recovery01
import all consolidated.rigidity_main_recovery01
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityPriorityExpectation.lean -/







@[expose] public section

/-!
# Independent continuous priorities give the literal expectation

The sample space is a finite product of real probability spaces. The last
coordinate is the extra marker. Every other coordinate is retained exactly
when its real priority is strictly smaller than the marker's priority.

For any common atomless marginal law, the actual supported-space dimension
has expectation `precedingMean`. Ties have measure zero by splitting one
coordinate from the product and using the nullity of singleton sections.
Integrability follows from the finite measurable order chambers. Finally,
permutation invariance of the product law and the finite orbit-sum identity
give the expectation, without assuming the ordering law in advance.

The final specialization is the product of Lebesgue measure restricted to
the unit interval, whose total mass is one. It is the independent uniform
priority formulation of Lemma 2.1.
-/

noncomputable section
namespace Papers.Rigidity.SupportedCode

open MeasureTheory
open scoped Classical BigOperators

/-- The literal iid product law for the coordinates and extra marker. -/
abbrev priorityMeasure (n : ℕ) (μ : Measure ℝ) : Measure (Fin (n + 1) → ℝ) :=
  Measure.pi fun _ => μ

/-- Distinct coordinate labels receive unequal priorities almost surely.
The conclusion is derived from the product measure and null singletons. -/
theorem priority_coordinates_ae_ne (n : ℕ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ∀ᵐ x ∂priorityMeasure n μ, x i ≠ x j := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij.symm
  have hmeas : MeasurableSet {z : ℝ × (Fin n → ℝ) | z.1 ≠ z.2 k} := by
    have heq : {z : ℝ × (Fin n → ℝ) | z.1 ≠ z.2 k} =
        {z : ℝ × (Fin n → ℝ) | z.1 = z.2 k}ᶜ := by
      ext z
      rfl
    rw [heq]
    exact (isClosed_eq (f := fun z : ℝ × (Fin n → ℝ) => z.1)
      (g := fun z => z.2 k) continuous_fst
      ((continuous_apply k).comp continuous_snd)).measurableSet.compl
  have hprod : ∀ᵐ z : ℝ × (Fin n → ℝ)
      ∂μ.prod (Measure.pi fun _ : Fin n => μ), z.1 ≠ z.2 k := by
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    exact ae_of_all μ fun a =>
      (Measure.ae_eval_ne (fun _ : Fin n => μ) k a).mono fun _ h => h.symm
  have h := (measurePreserving_piFinSuccAbove (α := fun _ : Fin (n + 1) => ℝ)
    (fun _ : Fin (n + 1) => μ) i).quasiMeasurePreserving.ae hprod
  exact h

/-- Every coordinate and the marker have distinct priorities almost surely. -/
theorem ae_injective_priorities (n : ℕ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ x ∂priorityMeasure n μ, Function.Injective x := by
  have hpairs : ∀ᵐ x ∂priorityMeasure n μ,
      ∀ i j : Fin (n + 1), i ≠ j → x i ≠ x j := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact ae_of_all _ fun _ h => False.elim (h hij)
    · exact (priority_coordinates_ae_ne n μ i j hij).mono fun _ h _ => h
  filter_upwards [hpairs] with x hx
  intro i j heq
  by_contra hij
  exact hx i j hij heq

/-- A finite order chamber is a finite intersection of measurable strict
comparisons and their complements. -/
theorem measurableSet_priorityOrderMatches {m : ℕ}
    (σ : Equiv.Perm (Fin m)) :
    MeasurableSet {x : Fin m → ℝ | priorityOrderMatches x σ} := by
  simp only [priorityOrderMatches, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  have hlt : MeasurableSet {x : Fin m → ℝ | x i < x j} :=
    measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  by_cases hij : σ.symm i < σ.symm j
  · simpa only [hij, true_iff] using hlt
  · have heq : {x : Fin m → ℝ | ¬x i < x j} =
        {x : Fin m → ℝ | x i < x j}ᶜ := by
      ext x
      rfl
    simpa only [hij, false_iff, heq] using hlt.compl

variable {K : Type*} [Field K]

/-- Integrability is proved for the literal priority-supported dimension,
including its stipulated value on tied outcomes. -/
theorem integrable_priorityDimension {n : ℕ}
    (W : Submodule K (Fin n → K)) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    Integrable (priorityDimension W) (priorityMeasure n μ) := by
  have hsum : Integrable (fun x : Fin (n + 1) → ℝ =>
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        if priorityOrderMatches x σ then
          (Module.finrank K (precedingCode W σ) : ℝ) else 0) (priorityMeasure n μ) := by
    apply integrable_finsetSum Finset.univ
    intro σ _
    have hmeas : Measurable (fun x : Fin (n + 1) → ℝ =>
        if priorityOrderMatches x σ then
          (Module.finrank K (precedingCode W σ) : ℝ) else 0) :=
      Measurable.ite (measurableSet_priorityOrderMatches σ)
        measurable_const measurable_const
    apply (integrable_const (μ := priorityMeasure n μ)
      (Module.finrank K (precedingCode W σ) : ℝ)).mono hmeas.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      by_cases hx : priorityOrderMatches x σ <;> simp [hx]
  apply hsum.congr
  filter_upwards [ae_injective_priorities n μ] with x hx
  exact (priorityDimension_eq_chamber_sum W x hx).symm

/-- Relabeling coordinate priorities as a genuine measurable equivalence. -/
def relabelPriorities {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ) τ.symm

@[simp] theorem relabelPriorities_apply {m : ℕ}
    (τ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) :
    relabelPriorities τ x = x ∘ τ := by
  funext i
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin m => ℝ)
    τ.symm x (τ i)
  simpa only [relabelPriorities, Equiv.symm_apply_apply, Function.comp_apply] using h

theorem relabelPriorities_measurePreserving {n : ℕ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (τ : Equiv.Perm (Fin (n + 1))) :
    MeasurePreserving (relabelPriorities τ) (priorityMeasure n μ) (priorityMeasure n μ) :=
  measurePreserving_piCongrLeft (α := fun _ : Fin (n + 1) => ℝ)
    (fun _ : Fin (n + 1) => μ) τ.symm

/-- Every common atomless real probability law yields the same exact
expectation. Independence is represented by the literal product measure. -/
theorem integral_priorityDimension_eq_precedingMean {n : ℕ}
    (W : Submodule K (Fin n → K)) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    (∫ x, priorityDimension W x ∂priorityMeasure n μ) = precedingMean W := by
  let P := priorityMeasure n μ
  let F : ℝ := ∑ σ : Equiv.Perm (Fin (n + 1)),
    (Module.finrank K (precedingCode W σ) : ℝ)
  have hint := integrable_priorityDimension W μ
  have hrelint (τ : Equiv.Perm (Fin (n + 1))) :
      Integrable (fun x => priorityDimension W (x ∘ τ)) P := by
    simpa only [Function.comp_def, relabelPriorities_apply] using
      (relabelPriorities_measurePreserving μ τ).integrable_comp_of_integrable hint
  have hrel (τ : Equiv.Perm (Fin (n + 1))) :
      (∫ x, priorityDimension W (x ∘ τ) ∂P) = ∫ x, priorityDimension W x ∂P := by
    simpa only [relabelPriorities_apply] using
      (relabelPriorities_measurePreserving μ τ).integral_comp' (priorityDimension W)
  have hsum :
      (∫ x, ∑ τ : Equiv.Perm (Fin (n + 1)), priorityDimension W (x ∘ τ) ∂P) = F := by
    calc
      _ = ∫ _ : Fin (n + 1) → ℝ, F ∂P := by
        apply integral_congr_ae
        filter_upwards [ae_injective_priorities n μ] with x hx
        exact sum_priorityDimension_relabel W x hx
      _ = F := by simp [P]
  rw [integral_finsetSum Finset.univ (fun τ _ => hrelint τ)] at hsum
  simp only [hrel, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_perm, Fintype.card_fin] at hsum
  have hfac : ((n + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (n + 1))
  change (∫ x, priorityDimension W x ∂P) = F / (n + 1).factorial
  apply (eq_div_iff hfac).mpr
  simpa only [mul_comm] using hsum

/-- The continuous uniform probability law on the closed unit interval. -/
def uniformPriorityLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance uniformPriorityLaw_isProbability : IsProbabilityMeasure uniformPriorityLaw :=
  ⟨by simp [uniformPriorityLaw]⟩

instance uniformPriorityLaw_nullSingleton : NullSingletonClass uniformPriorityLaw := by
  unfold uniformPriorityLaw
  infer_instance

/-- Exact equality between the paper's iid uniform-priority expectation
and the uniform finite-order mean used throughout the graph proof. -/
theorem integral_uniform_priorityDimension_eq_precedingMean {n : ℕ}
    (W : Submodule K (Fin n → K)) :
    (∫ x, priorityDimension W x ∂priorityMeasure n uniformPriorityLaw) = precedingMean W :=
  integral_priorityDimension_eq_precedingMean W uniformPriorityLaw

/-- Lemma 2.1 in its literal independent continuous uniform-priority form. -/
theorem uniform_priority_expectation_le_bound {n s : ℕ}
    (W : Submodule K (Fin n → K)) (hs : 1 ≤ s) (hmin : MinimumSupport W s) :
    (∫ x, priorityDimension W x ∂priorityMeasure n uniformPriorityLaw) ≤
      bound s (Module.finrank K W) := by
  rw [integral_uniform_priorityDimension_eq_precedingMean]
  exact precedingMean_le_bound W hs hmin

/-- The sharpness assertion of Lemma 2.1 for the literal iid uniform
priorities, for every rank and positive support threshold over every
infinite field. The evaluation-code witness is the previously constructed
code, and the expectation is transported by the proved integral identity. -/
theorem exists_code_attaining_uniform_priority_bound [Infinite K]
    (r s : ℕ) (hs : 1 ≤ s) :
    ∃ W : Submodule K (Fin (r + s - 1) → K),
      Module.finrank K W = r ∧ MinimumSupport W s ∧
        (∫ x, priorityDimension W x ∂priorityMeasure (r + s - 1) uniformPriorityLaw) =
          bound s r := by
  obtain ⟨W, hrank, hmin, hmean⟩ := exists_code_attaining_bound (K := K) r s hs
  refine ⟨W, hrank, hmin, ?_⟩
  rw [integral_uniform_priorityDimension_eq_precedingMean]
  exact hmean

end Papers.Rigidity.SupportedCode

end
end
end BundleSource0001


/- Final endpoint audits; all local proof bodies must be available. -/
set_option maxHeartbeats 0
#print axioms Papers.Rigidity.pairPin_defect_theorem
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.pairPin_defect_theorem to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_pairPin_defect_theorem.json"
#print axioms Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_PairPinGraph_defect_theorem_at_algebraicallyGeneric_pins.json"
#print axioms Papers.Rigidity.QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_QuantitativeHeight_genericIncidencePrime_height_ge_active_add_sparse.json"
#print axioms Papers.Rigidity.NullHeight.coefficientMinimalPrime_height_eq_edgeCard
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.NullHeight.coefficientMinimalPrime_height_eq_edgeCard to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_NullHeight_coefficientMinimalPrime_height_eq_edgeCard.json"
#print axioms Papers.Rigidity.PairPinGraph.genericPinRank_eq_genericMotionMatrix_rank
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.PairPinGraph.genericPinRank_eq_genericMotionMatrix_rank to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_PairPinGraph_genericPinRank_eq_genericMotionMatrix_rank.json"
#print axioms Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_PairPinGraph_defect_at_maximal_rank_pins.json"
#print axioms Papers.Rigidity.minimalCounterexample_false
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.minimalCounterexample_false to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_minimalCounterexample_false.json"
#print axioms Papers.Rigidity.theorem_one_one
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.theorem_one_one to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_theorem_one_one.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_rigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_rigid to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_rigid.json"
#print axioms Papers.Rigidity.corollary_one_two_rigid_subgraph_cover
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.corollary_one_two_rigid_subgraph_cover to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_corollary_one_two_rigid_subgraph_cover.json"
#print axioms Papers.Rigidity.corollary_one_two_rigid_cluster_completion
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.corollary_one_two_rigid_cluster_completion to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_corollary_one_two_rigid_cluster_completion.json"
#print axioms Papers.Rigidity.sixConnected_rigidSubgraphCovered_rigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_rigidSubgraphCovered_rigid to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_sixConnected_rigidSubgraphCovered_rigid.json"
#print axioms Papers.Rigidity.rigidCluster_completion_sixConnected_rigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.rigidCluster_completion_sixConnected_rigid to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_rigidCluster_completion_sixConnected_rigid.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_locallyDistanceRigid.json"
#print axioms Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_sixConnected_rigidSubgraphCovered_locallyDistanceRigid.json"
#print axioms Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_rigidCluster_completion_sixConnected_locallyDistanceRigid.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_motionKernel_eq_globalTwists
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_motionKernel_eq_globalTwists to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_motionKernel_eq_globalTwists.json"
#print axioms Papers.Rigidity.fiveConnected_k4Covered_flexible_exists
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.fiveConnected_k4Covered_flexible_exists to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_fiveConnected_k4Covered_flexible_exists.json"
#print axioms Papers.Rigidity.SupportedCode.exists_code_attaining_bound
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.SupportedCode.exists_code_attaining_bound to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_SupportedCode_exists_code_attaining_bound.json"
#print axioms Papers.Rigidity.BodyLoads.duplicate_loads_prefix_identity
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.BodyLoads.duplicate_loads_prefix_identity to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_BodyLoads_duplicate_loads_prefix_identity.json"
#print axioms Papers.Rigidity.generic_alternating_space_center_defined_over_coefficients
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.generic_alternating_space_center_defined_over_coefficients to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_generic_alternating_space_center_defined_over_coefficients.json"
#print axioms Papers.Rigidity.BodyLoads.TwoBodyPin.lemma_three_seven
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.BodyLoads.TwoBodyPin.lemma_three_seven to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_BodyLoads_TwoBodyPin_lemma_three_seven.json"
#print axioms Papers.Rigidity.SupportedCode.sum_priorityDimension_relabel
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.SupportedCode.sum_priorityDimension_relabel to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_SupportedCode_sum_priorityDimension_relabel.json"
#print axioms Papers.Rigidity.BarJoint.localRigidity_iff_rank_at_algebraicallyGeneric
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.BarJoint.localRigidity_iff_rank_at_algebraicallyGeneric to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_BarJoint_localRigidity_iff_rank_at_algebraicallyGeneric.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_rigidityRank_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_rigidityRank_of_algebraicIndependent to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_rigidityRank_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.SupportedCode.integral_priorityDimension_eq_precedingMean
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.SupportedCode.integral_priorityDimension_eq_precedingMean to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_SupportedCode_integral_priorityDimension_eq_precedingMean.json"
#print axioms Papers.Rigidity.SupportedCode.uniform_priority_expectation_le_bound
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.SupportedCode.uniform_priority_expectation_le_bound to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_SupportedCode_uniform_priority_expectation_le_bound.json"
#print axioms Papers.Rigidity.SupportedCode.exists_code_attaining_uniform_priority_bound
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.SupportedCode.exists_code_attaining_uniform_priority_bound to ".lake/reports/audit/priority_expectation/endpoint_audits/Papers_Rigidity_SupportedCode_exists_code_attaining_uniform_priority_bound.json"
