import CommAlg.Polymatroid.ConstraintMatroid

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

instance constraintMatroid_finite (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T : Finset V) : (constraintMatroid q hq hq0 T).Finite :=
  ⟨by rw [constraintMatroid_ground]; exact T.finite_toSet⟩

theorem constraint_rank_le (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T R : Finset V) (hRT : R ⊆ T) (U : Finset V) :
    (constraintMatroid q hq hq0 T).eRk (R : Set V) ≤
      ((q U + (R \ U).card : ℕ) : ℕ∞) := by
  obtain ⟨W, hW, hmin⟩ := constraint_rank_certificate q hq hq0 T R hRT
  rw [hW]
  exact_mod_cast hmin U

theorem le_constraint_rank (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T R : Finset V) (hRT : R ⊆ T) (n : ℕ) :
    (n : ℕ∞) ≤ (constraintMatroid q hq hq0 T).eRk (R : Set V) ↔
      ∀ U, n ≤ q U + (R \ U).card := by
  obtain ⟨W, hW, hmin⟩ := constraint_rank_certificate q hq hq0 T R hRT
  rw [hW]
  constructor
  · intro h U
    exact (show n ≤ q W + (R \ W).card by exact_mod_cast h).trans (hmin U)
  · intro h
    exact_mod_cast h W

/-- Every element outside a minimizing set is an actual coloop. -/
theorem constraint_isColoop_of_minimizer (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T U : Finset V)
    (hmin : (constraintMatroid q hq hq0 T).eRk (T : Set V) =
      ((q U + (T \ U).card : ℕ) : ℕ∞)) {e : V} (he : e ∈ T \ U) :
    (constraintMatroid q hq hq0 T).IsColoop e := by
  let M := constraintMatroid q hq hq0 T
  apply Matroid.isColoop_iff_forall_mem_isBase.mpr
  intro J hJ
  by_contra heJ
  let JF := finiteSet J
  have hJF : M.Indep (JF : Set V) := by
    rw [coe_finiteSet]
    exact hJ.indep
  obtain ⟨hJT, hfeas⟩ := (constraintMatroid_indep q hq hq0 T JF).mp hJF
  have hcard : JF.card = q U + (T \ U).card := by
    have hc := hJ.encard_eq_eRank
    have hjc : J.encard = (JF.card : ℕ∞) := by
      rw [← coe_finiteSet J, Set.encard_coe_eq_coe_finsetCard]
    rw [hjc, ← M.eRk_ground] at hc
    change (JF.card : ℕ∞) = M.eRk (T : Set V) at hc
    rw [hmin] at hc
    exact_mod_cast hc
  have hss : JF \ U ⊂ T \ U := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset_sdiff hJT (le_refl U), ?_⟩
    intro heq
    have hm : e ∈ JF \ U := by rwa [heq]
    exact heJ ((mem_finiteSet J e).mp (Finset.mem_sdiff.mp hm).1)
  have hc := Finset.card_lt_card hss
  have hf := hfeas U
  have heq := Finset.card_inter_add_card_sdiff JF U
  omega

end CommAlg.Polymatroid
