import CommAlg.Simplicial.Chains

/-! # Chain-level deletion/contraction and nonzero homology

Every predicate below refers to actual exterior chains, their actual boundary, and the actual
existence of a filling chain. These lemmas supply the full homological induction for matroids.
-/

noncomputable section

namespace CommAlg.Simplicial

variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]

/-- Every closed augmented chain in this degree is the boundary of a chain in the next degree. -/
def ExactIn (K : Finset V → Prop) (i : ℕ) : Prop :=
  ∀ z : Ambient V k, z ∈ Chains K i → boundary z = 0 →
    ∃ y : Ambient V k, y ∈ Chains K (i + 1) ∧ boundary y = z

/-- An actual closed chain whose homology class does not vanish. -/
def NonzeroHomology (K : Finset V → Prop) (i : ℕ) : Prop :=
  ∃ z : Ambient V k, z ∈ Chains K i ∧ boundary z = 0 ∧
    ∀ y : Ambient V k, y ∈ Chains K (i + 1) → boundary y ≠ z

lemma nonzeroHomology_iff_not_exactIn (K : Finset V → Prop) (i : ℕ) :
    NonzeroHomology (k := k) K i ↔ ¬ExactIn (k := k) K i := by
  classical
  simp only [NonzeroHomology, ExactIn, not_forall, not_exists, not_and]
  tauto

lemma chains_eq_bot_of_no_face {K : Finset V → Prop} {i : ℕ}
    (h : ∀ s, K s → s.card ≠ i) : Chains (k := k) K i = ⊥ := by
  apply le_antisymm _ bot_le
  rw [Chains, Submodule.span_le]
  rintro z ⟨s, ⟨hs, hc⟩, rfl⟩
  exact (h s hs hc).elim

lemma exactIn_of_no_face {K : Finset V → Prop} {i : ℕ}
    (h : ∀ s, K s → s.card ≠ i) : ExactIn (k := k) K i := by
  intro z hz hcycle
  rw [chains_eq_bot_of_no_face h, Submodule.mem_bot] at hz
  subst z
  exact ⟨0, Submodule.zero_mem _, map_zero _⟩

lemma creation_mem_of_cone {K : Finset V → Prop} (e : V)
    (hc : ∀ s, K s → K (insert e s)) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains K i) : creation e z ∈ Chains K (i + 1) := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    rw [creation_basis]
    split_ifs with he
    · exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      exact basis_mem (hc s hs) (by simp [he, hcard])
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) K (i + 1)))
  | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

lemma exactIn_of_cone {K : Finset V → Prop} (e : V)
    (hc : ∀ s, K s → K (insert e s)) (i : ℕ) : ExactIn (k := k) K i := by
  intro z hz hcycle
  refine ⟨creation e z, creation_mem_of_cone e hc hz, ?_⟩
  simp only [boundary_creation, hcycle, map_zero, sub_zero]

lemma exactIn_zero_of_vertex {K : Finset V → Prop} (e : V) (he : K {e}) :
    ExactIn (k := k) K 0 := by
  intro z hz hcycle
  have hc : creation e z ∈ Chains K 1 := by
    clear hcycle
    induction hz using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
      obtain rfl : s = ∅ := Finset.card_eq_zero.mp hcard
      rw [creation_basis]
      simp only [Finset.notMem_empty, ↓reduceIte, Finset.insert_empty]
      exact Submodule.smul_mem _ _ (basis_mem he (Finset.card_singleton _))
    | zero => simpa using (Submodule.zero_mem (Chains (k := k) K 1))
    | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
    | smul r a ha ih => simpa using Submodule.smul_mem _ r ih
  refine ⟨creation e z, hc, ?_⟩
  simp only [boundary_creation, hcycle, map_zero, sub_zero]

lemma nonzeroHomology_zero_of_only_empty [Nontrivial k] {K : Finset V → Prop}
    (he : K ∅) (hK : ∀ s, K s → s = ∅) : NonzeroHomology (k := k) K 0 := by
  refine ⟨basis ∅, basis_mem he rfl, ?_, ?_⟩
  · exact boundary_zero_degree_zero (basis_mem he rfl)
  · intro y hy hyb
    have hn : ∀ s, K s → s.card ≠ 1 := by
      intro s hs
      rw [hK s hs]
      simp
    rw [chains_eq_bot_of_no_face hn, Submodule.mem_bot] at hy
    subst y
    have hb : basis (k := k) (∅ : Finset V) ≠ 0 := Module.Basis.ne_zero _ _
    exact hb (by simpa using hyb.symm)

/-- The exactness half of deletion/contraction, proved by filling explicit chains. -/
lemma exactIn_of_deletion_link {K : Finset V → Prop} (hK : Downward K) (e : V) (i : ℕ)
    (hdel : ExactIn (k := k) (deletion K e) (i + 1))
    (hlink : ExactIn (k := k) (link K e) i) : ExactIn (k := k) K (i + 1) := by
  intro z hz hcycle
  have hw := contraction_mem e hz
  have hwcycle : boundary (contraction e z) = 0 := by
    have h := contraction_boundary e z
    rw [hcycle, map_zero, eq_neg_iff_add_eq_zero, zero_add] at h
    exact h
  obtain ⟨v, hv, hvb⟩ := hlink _ hw hwcycle
  let z' := z + boundary (creation e v)
  have hz' : z' ∈ Chains K (i + 1) :=
    Submodule.add_mem _ hz (boundary_mem hK (creation_mem_link e hv))
  have hvcon : contraction e v = 0 :=
    contraction_zero_of_deletion e (link_le_deletion hK e _ hv)
  have hz'con : contraction e z' = 0 := by
    dsimp only [z']
    rw [map_add, contraction_boundary, contraction_creation, hvcon, map_zero, sub_zero, hvb]
    exact add_neg_cancel _
  have hz'del := mem_deletion_of_contraction_zero e hz' hz'con
  have hz'cycle : boundary z' = 0 := by
    simp only [z', map_add, hcycle, boundary_boundary, add_zero]
  obtain ⟨y, hy, hyb⟩ := hdel z' hz'del hz'cycle
  refine ⟨y - creation e v,
    Submodule.sub_mem _ (chains_mono (fun s hs => hs.1) _ hy) (creation_mem_link e hv), ?_⟩
  rw [map_sub, hyb]
  exact add_sub_cancel_right z _

/-- Nonzero link homology produces nonzero homology one degree higher, whenever every chain in
that degree of the deletion can be filled. The proof constructs the cycle explicitly. -/
lemma nonzeroHomology_of_link {K : Finset V → Prop} (hK : Downward K) (e : V) (i : ℕ)
    (hdel : ExactIn (k := k) (deletion K e) i)
    (hlink : NonzeroHomology (k := k) (link K e) i) :
    NonzeroHomology (k := k) K (i + 1) := by
  obtain ⟨w, hw, hwcycle, hwnonboundary⟩ := hlink
  obtain ⟨y, hy, hyb⟩ := hdel w (link_le_deletion hK e i hw) hwcycle
  refine ⟨creation e w - y,
    Submodule.sub_mem _ (creation_mem_link e hw) (chains_mono (fun s hs => hs.1) _ hy), ?_, ?_⟩
  · rw [map_sub, boundary_creation, hwcycle, map_zero, sub_zero, hyb, sub_self]
  · intro q hq hqb
    have hwcon := contraction_zero_of_deletion e (link_le_deletion hK e i hw)
    have hycon := contraction_zero_of_deletion e hy
    have h := congrArg (contraction e) hqb
    rw [contraction_boundary, map_sub, contraction_creation, hwcon, map_zero, sub_zero,
      hycon, sub_zero] at h
    exact hwnonboundary (-contraction e q)
      (Submodule.neg_mem _ (contraction_mem e hq)) (by simpa only [map_neg] using h)

end CommAlg.Simplicial
