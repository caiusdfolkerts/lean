import Characterizations.SocleCharacterization

/-! # Actual generators attaining every minimum along a nested chain -/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every minimal projected generator lifts to a minimal generator at every
larger retained set. This statement does not assume exchange. -/
theorem localize_nested_lift (B : Family V) {U W : Finset V} (hWU : W ⊆ U)
    {b : Exponent V} (hb : b ∈ localize B W) :
    ∃ c ∈ localize B U, project W c = b := by
  obtain ⟨a, ha, hab⟩ := localize_member hb
  obtain ⟨c, hc, hca⟩ := localize_below (U := U) ha
  refine ⟨c, hc, ?_⟩
  have hcb : project W c ≤ b := by
    have h := project_mono W hca
    rwa [project_project hWU, hab] at h
  have hcW : project W c ∈ B.image (project W) := by
    obtain ⟨z, hz, rfl⟩ := localize_member hc
    exact Finset.mem_image.mpr ⟨z, hz, (project_project hWU z).symm⟩
  exact (mem_minimalFamily.mp hb).2 _ hcW hcb

theorem localize_univ_of_antichain {B : Family V} (hB : Antichain B) :
    localize B Finset.univ = B := by
  have he : project (Finset.univ : Finset V) = id := funext project_univ
  simpa [localize, he] using minimalFamily_eq hB

/-- Simultaneous attainment along an arbitrary increasing chain, by a literal
minimal generator of the localization at its last term. -/
theorem localize_chain_minimum {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) (U : ℕ → Finset V) (hU : Monotone U) (n : ℕ) :
    ∃ b ∈ localize B (U n), ∀ j ≤ n, subsetSum b (U j) = lowerRank B (U j) := by
  induction n with
  | zero =>
    obtain ⟨b, hb⟩ := localize_nonempty hB (U 0)
    refine ⟨b, hb, ?_⟩
    intro j hj
    have he : j = 0 := by omega
    subst j
    rw [← degree_project, localize_supported hb]
    exact localize_degree hB hl hb
  | succ n ih =>
    obtain ⟨b, hb, hmin⟩ := ih
    obtain ⟨c, hc, he⟩ := localize_nested_lift B (hU (Nat.le_succ n)) hb
    refine ⟨c, hc, ?_⟩
    intro j hj
    by_cases hlast : j = n + 1
    · subst j
      rw [← degree_project, localize_supported hc]
      exact localize_degree hB hl hc
    · have hjn : j ≤ n := by omega
      rw [← subsetSum_project (hU hjn) c, he]
      exact hmin j hjn

/-- The greedy-chain assertion in the proof of Theorem 2.11. -/
theorem generator_chain_minimum {B : Family V} (hB : B.Nonempty) (ha : Antichain B)
    (hl : LocallyEquigenerated B) (U : ℕ → Finset V) (hU : Monotone U)
    (n : ℕ) (hn : U n = Finset.univ) :
    ∃ b ∈ B, ∀ j ≤ n, subsetSum b (U j) = lowerRank B (U j) := by
  obtain ⟨b, hb, hmin⟩ := localize_chain_minimum hB hl U hU n
  rw [hn, localize_univ_of_antichain ha] at hb
  exact ⟨b, hb, hmin⟩

end Characterizations
