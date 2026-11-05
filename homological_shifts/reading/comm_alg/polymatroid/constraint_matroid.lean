import CommAlg.Polymatroid.RankIdeal

/-! # Matroids defined by possibly nonmonotone submodular constraints

This is the constraint-matroid lemma used by the homological rank formula.
Monotonicity of the constraint function is deliberately not assumed.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def SubmodularNat (q : Finset V → ℕ) : Prop :=
  ∀ U W, q (U ∪ W) + q (U ∩ W) ≤ q U + q W

def ConstraintFeasible (q : Finset V → ℕ) (I : Finset V) : Prop :=
  ∀ U, (I ∩ U).card ≤ q U

def ConstraintTight (q : Finset V → ℕ) (I U : Finset V) : Prop :=
  (I ∩ U).card = q U

theorem card_inter_modular (I U W : Finset V) :
    (I ∩ (U ∪ W)).card + (I ∩ (U ∩ W)).card = (I ∩ U).card + (I ∩ W).card := by
  have hu : I ∩ (U ∪ W) = (I ∩ U) ∪ (I ∩ W) := by ext x; simp; tauto
  have hi : I ∩ (U ∩ W) = (I ∩ U) ∩ (I ∩ W) := by ext x; simp; tauto
  rw [hu, hi]
  exact Finset.card_union_add_card_inter _ _

theorem constraint_tight_union_inter {q : Finset V → ℕ} (hq : SubmodularNat q)
    {I U W : Finset V} (hI : ConstraintFeasible q I)
    (hU : ConstraintTight q I U) (hW : ConstraintTight q I W) :
    ConstraintTight q I (U ∪ W) ∧ ConstraintTight q I (U ∩ W) := by
  have hm := card_inter_modular I U W
  have hs := hq U W
  have hfU := hI (U ∪ W)
  have hfI := hI (U ∩ W)
  unfold ConstraintTight at *
  omega

theorem constraintFeasible_empty (q : Finset V → ℕ) : ConstraintFeasible q ∅ := by
  intro U; simp

theorem ConstraintFeasible.subset {q : Finset V → ℕ} {I J : Finset V}
    (hJ : ConstraintFeasible q J) (hIJ : I ⊆ J) : ConstraintFeasible q I := by
  intro U
  exact (Finset.card_le_card (fun x hx => Finset.mem_inter.mpr
    ⟨hIJ (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩)).trans (hJ U)

theorem constraint_failed_insert {q : Finset V → ℕ} {I : Finset V}
    (hI : ConstraintFeasible q I) {e : V} (he : e ∉ I)
    (hbad : ¬ ConstraintFeasible q (insert e I)) :
    ∃ U, ConstraintTight q I U ∧ e ∈ U := by
  simp only [ConstraintFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have heU : e ∈ U := by
    by_contra hn
    have hi : insert e I ∩ U = I ∩ U := by ext x; simp; aesop
    rw [hi] at hU
    exact (not_lt_of_ge (hI U)) hU
  have hi : insert e I ∩ U = insert e (I ∩ U) := by ext x; simp; aesop
  have he' : e ∉ I ∩ U := fun h => he (Finset.mem_inter.mp h).1
  rw [hi, Finset.card_insert_of_notMem he'] at hU
  exact ⟨U, Nat.le_antisymm (hI U) (by omega), heU⟩

theorem constraint_tight_cover {q : Finset V → ℕ} (hq : SubmodularNat q) (hq0 : q ∅ = 0)
    {I : Finset V} (hI : ConstraintFeasible q I) (D : Finset V)
    (h : ∀ e ∈ D, ∃ U, ConstraintTight q I U ∧ e ∈ U) :
    ∃ U, ConstraintTight q I U ∧ D ⊆ U := by
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp [ConstraintTight, hq0], Finset.empty_subset _⟩
  | @insert e D he ih =>
    obtain ⟨U, hU, hDU⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hW, heW⟩ := h e (Finset.mem_insert_self _ _)
    exact ⟨U ∪ W, (constraint_tight_union_inter hq hI hU hW).1,
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ heW,
        hDU.trans Finset.subset_union_left⟩⟩

theorem constraint_augment {q : Finset V → ℕ} (hq : SubmodularNat q) (hq0 : q ∅ = 0)
    {I J : Finset V} (hI : ConstraintFeasible q I) (hJ : ConstraintFeasible q J)
    (hcard : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ ConstraintFeasible q (insert e I) := by
  by_contra hn
  push_neg at hn
  obtain ⟨U, hU, hcover⟩ := constraint_tight_cover hq hq0 hI (J \ I) (by
    intro e he
    obtain ⟨heJ, heI⟩ := Finset.mem_sdiff.mp he
    exact constraint_failed_insert hI heI (hn e heJ heI))
  have hout : J \ U ⊆ I \ U := by
    intro e he
    obtain ⟨heJ, heU⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_sdiff.mpr ⟨?_, heU⟩
    by_contra heI
    exact heU (hcover (Finset.mem_sdiff.mpr ⟨heJ, heI⟩))
  have hc := Finset.card_le_card hout
  have hj := hJ U
  have hci := Finset.card_inter_add_card_sdiff I U
  have hcj := Finset.card_inter_add_card_sdiff J U
  unfold ConstraintTight at hU
  omega

def constraintMatroid (q : Finset V → ℕ) (hq : SubmodularNat q) (hq0 : q ∅ = 0)
    (T : Finset V) : Matroid V :=
  (IndepMatroid.ofFinset (T : Set V)
    (fun I => I ⊆ T ∧ ConstraintFeasible q I)
    ⟨Finset.empty_subset _, constraintFeasible_empty q⟩
    (fun _ _ hJ hIJ => ⟨hIJ.trans hJ.1, hJ.2.subset hIJ⟩)
    (by
      intro I J hI hJ hcard
      obtain ⟨e, heJ, heI, he⟩ := constraint_augment hq hq0 hI.2 hJ.2 hcard
      exact ⟨e, heJ, heI, Finset.insert_subset_iff.mpr ⟨hJ.1 heJ, hI.1⟩, he⟩)
    (fun _ hI => hI.1)).matroid

@[simp] theorem constraintMatroid_ground (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T : Finset V) :
    (constraintMatroid q hq hq0 T).E = (T : Set V) := rfl

@[simp] theorem constraintMatroid_indep (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T I : Finset V) :
    (constraintMatroid q hq hq0 T).Indep (I : Set V) ↔ I ⊆ T ∧ ConstraintFeasible q I := by
  change (∀ J : Finset V, (J : Set V) ⊆ (I : Set V) → J ⊆ T ∧ ConstraintFeasible q J) ↔ _
  constructor
  · exact fun h => h I Set.Subset.rfl
  · intro h J hJI
    exact ⟨hJI.trans h.1, h.2.subset hJI⟩

theorem constraint_card_le {q : Finset V → ℕ} {I R : Finset V}
    (hI : ConstraintFeasible q I) (hIR : I ⊆ R) (U : Finset V) :
    I.card ≤ q U + (R \ U).card := by
  have hc := Finset.card_le_card (Finset.sdiff_subset_sdiff hIR (le_refl U))
  have hi := hI U
  have he := Finset.card_inter_add_card_sdiff I U
  omega

/-- A maximal feasible subset has a tight-set certificate of its exact size. -/
theorem constraint_maximal_certificate {q : Finset V → ℕ} (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (R : Finset V) :
    ∃ I U, I ⊆ R ∧ ConstraintFeasible q I ∧
      I.card = q U + (R \ U).card ∧
      ∀ J, J ⊆ R → ConstraintFeasible q J → J.card ≤ I.card := by
  let C := R.powerset.filter (ConstraintFeasible q)
  have hC : C.Nonempty := ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), constraintFeasible_empty q⟩⟩
  obtain ⟨I, hIC, hmax⟩ := C.exists_maximal hC
  obtain ⟨hIR, hI⟩ : I ⊆ R ∧ ConstraintFeasible q I := by
    simpa only [C, Finset.mem_filter, Finset.mem_powerset] using hIC
  have hblocked : ∀ e ∈ R \ I, ∃ U, ConstraintTight q I U ∧ e ∈ U := by
    intro e he
    obtain ⟨heR, heI⟩ := Finset.mem_sdiff.mp he
    apply constraint_failed_insert hI heI
    intro hgood
    have hiC : insert e I ∈ C := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨heR, hIR⟩), hgood⟩
    exact heI (hmax hiC (Finset.subset_insert _ _) (Finset.mem_insert_self _ _))
  obtain ⟨U, hU, hcover⟩ := constraint_tight_cover hq hq0 hI (R \ I) hblocked
  have hout : R \ U = I \ U := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨heR, heU⟩ := Finset.mem_sdiff.mp he
      refine Finset.mem_sdiff.mpr ⟨?_, heU⟩
      by_contra heI
      exact heU (hcover (Finset.mem_sdiff.mpr ⟨heR, heI⟩))
    · exact Finset.sdiff_subset_sdiff hIR (le_refl U)
  have hcard : I.card = q U + (R \ U).card := by
    rw [hout]
    have hc := Finset.card_inter_add_card_sdiff I U
    unfold ConstraintTight at hU
    omega
  exact ⟨I, U, hIR, hI, hcard, fun J hJR hJ => hcard ▸ constraint_card_le hJ hJR U⟩

def finiteSet (S : Set V) : Finset V := Finset.univ.filter (· ∈ S)

@[simp] theorem mem_finiteSet (S : Set V) (x : V) : x ∈ finiteSet S ↔ x ∈ S := by
  simp [finiteSet]

theorem coe_finiteSet (S : Set V) : (finiteSet S : Set V) = S := by ext x; simp

/-- The minimum formula is witnessed by an actual subset, and is the rank of
the actual Mathlib matroid, not an unproved combinatorial surrogate. -/
theorem constraint_rank_certificate (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T R : Finset V) (hRT : R ⊆ T) :
    ∃ U, (constraintMatroid q hq hq0 T).eRk (R : Set V) =
        ((q U + (R \ U).card : ℕ) : ℕ∞) ∧
      ∀ W, q U + (R \ U).card ≤ q W + (R \ W).card := by
  obtain ⟨I, U, hIR, hI, hcard, hmax⟩ := constraint_maximal_certificate hq hq0 R
  let M := constraintMatroid q hq hq0 T
  have hi : M.Indep (I : Set V) := (constraintMatroid_indep q hq hq0 T I).mpr
    ⟨hIR.trans hRT, hI⟩
  have he : M.eRk (R : Set V) = I.card := by
    apply le_antisymm
    · apply Matroid.eRk_le_iff.mpr
      intro J hJR hJ
      let JF := finiteSet J
      have hJF : M.Indep (JF : Set V) := by rwa [coe_finiteSet]
      have hJF' := (constraintMatroid_indep q hq hq0 T JF).mp hJF
      have hJFR : JF ⊆ R := by intro x hx; exact hJR ((mem_finiteSet J x).mp hx)
      have hc := hmax JF hJFR hJF'.2
      have hjc : J.encard = JF.card := by
        rw [← coe_finiteSet J, Set.encard_coe_eq_coe_finsetCard]
      rw [hjc]
      exact_mod_cast hc
    · simpa only [Set.encard_coe_eq_coe_finsetCard] using hi.encard_le_eRk_of_subset hIR
  refine ⟨U, he.trans (congrArg Nat.cast hcard), ?_⟩
  intro W
  rw [← hcard]
  exact constraint_card_le hI hIR W

end CommAlg.Polymatroid
