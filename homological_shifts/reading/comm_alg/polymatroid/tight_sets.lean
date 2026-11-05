import CommAlg.Polymatroid.Localization

/-! # Supermodular lower inequalities force the full exchange axiom -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def LowerFeasible (r : Finset V → ℕ) (a : Exponent V) : Prop :=
  ∀ U, r U ≤ subsetSum a U

def Tight (r : Finset V → ℕ) (a : Exponent V) (U : Finset V) : Prop :=
  subsetSum a U = r U

theorem tight_union_inter {r : Finset V → ℕ} (hr : Supermodular r)
    {a : Exponent V} (ha : LowerFeasible r a) {U W : Finset V}
    (hU : Tight r a U) (hW : Tight r a W) :
    Tight r a (U ∪ W) ∧ Tight r a (U ∩ W) := by
  have hsum := subsetSum_union_inter a U W
  have hsuper := hr U W
  have hfeasU := ha (U ∪ W)
  have hfeasW := ha (U ∩ W)
  unfold Tight at *
  omega

theorem subsetSum_exchange (a : Exponent V) (i j : V) (hi : 0 < a i) (U : Finset V) :
    subsetSum (exchange a i j) U + (if i ∈ U then 1 else 0) =
      subsetSum a U + (if j ∈ U then 1 else 0) := by
  have hle : Finsupp.single i 1 ≤ a := by
    intro h
    by_cases hh : h = i
    · subst h
      simpa using (show 1 ≤ a i by omega)
    · simp [Finsupp.single_apply, hh, Ne.symm hh]
  have he : exchange a i j + Finsupp.single i 1 = a + Finsupp.single j 1 := by
    unfold exchange
    rw [add_right_comm, tsub_add_cancel_of_le hle]
  have hs := congrArg (fun b : Exponent V => subsetSum b U) he
  simpa [subsetSum, Finset.sum_add_distrib, Finsupp.single_apply] using hs

theorem failed_exchange_tight {r : Finset V → ℕ} {a : Exponent V}
    (ha : LowerFeasible r a) {i j : V} (hi : 0 < a i)
    (hbad : ¬ LowerFeasible r (exchange a i j)) :
    ∃ U, Tight r a U ∧ i ∈ U ∧ j ∉ U := by
  simp only [LowerFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have hfeas := ha U
  have hs := subsetSum_exchange a i j hi U
  have hiU : i ∈ U := by
    by_contra h
    rw [if_neg h] at hs
    split_ifs at hs <;> omega
  have hjU : j ∉ U := by
    intro h
    rw [if_pos hiU, if_pos h] at hs
    omega
  refine ⟨U, ?_, hiU, hjU⟩
  rw [if_pos hiU, if_neg hjU] at hs
  unfold Tight
  omega

theorem tight_avoiding {r : Finset V → ℕ} (hr : Supermodular r)
    {a : Exponent V} (ha : LowerFeasible r a) (i : V)
    (D : Finset V) (hD : D.Nonempty)
    (h : ∀ j ∈ D, ∃ U, Tight r a U ∧ i ∈ U ∧ j ∉ U) :
    ∃ C, Tight r a C ∧ i ∈ C ∧ ∀ j ∈ D, j ∉ C := by
  induction hD using Finset.Nonempty.cons_induction with
  | singleton j =>
    obtain ⟨U, hU, hi, hj⟩ := h j (Finset.mem_singleton_self _)
    exact ⟨U, hU, hi, by simpa using hj⟩
  | cons j D hj hD ih =>
    obtain ⟨C, hC, hiC, havoid⟩ := ih (fun q hq => h q (Finset.mem_cons.mpr (Or.inr hq)))
    obtain ⟨U, hU, hiU, hjU⟩ := h j (Finset.mem_cons.mpr (Or.inl rfl))
    refine ⟨C ∩ U, (tight_union_inter hr ha hC hU).2, Finset.mem_inter.mpr ⟨hiC, hiU⟩, ?_⟩
    intro q hq hqin
    rcases Finset.mem_cons.mp hq with rfl | hq
    · exact hjU (Finset.mem_inter.mp hqin).2
    · exact havoid q hq (Finset.mem_inter.mp hqin).1

/-- Full prescribed-donor exchange for all integer points of a fixed degree
satisfying supermodular lower inequalities. -/
theorem feasible_exchange {r : Finset V → ℕ} (hr : Supermodular r)
    {a b : Exponent V} (ha : LowerFeasible r a) (hb : LowerFeasible r b)
    (hdeg : a.degree = b.degree) {i : V} (hi : b i < a i) :
    ∃ j, a j < b j ∧ LowerFeasible r (exchange a i j) := by
  by_contra hbad
  push_neg at hbad
  let D : Finset V := Finset.univ.filter (fun j => a j < b j)
  have hD : D.Nonempty := by
    obtain ⟨j, hj⟩ := exists_surplus hdeg hi
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨C, hC, hiC, havoid⟩ := tight_avoiding hr ha i D hD (by
    intro j hj
    exact failed_exchange_tight ha (by omega) (hbad j (Finset.mem_filter.mp hj).2))
  have hle : ∀ j ∈ C, b j ≤ a j := by
    intro j hj
    by_contra h
    have hD' : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ j, by omega⟩
    exact havoid j hD' hj
  have hlt : subsetSum b C < subsetSum a C :=
    Finset.sum_lt_sum hle ⟨i, hiC, hi⟩
  have hfeas := hb C
  unfold Tight at hC
  omega

/-- Lemma 2.6, stated for a genuine monomial exponent ideal. -/
theorem polymatroidal_of_lower_inequalities {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) {r : Finset V → ℕ} (hr : Supermodular r)
    (hrep : ∀ a, Contains B a ↔ LowerFeasible r a) : IsPolymatroidal B := by
  refine ⟨⟨d, hB⟩, ?_⟩
  intro a ha b hb i hi
  obtain ⟨j, hj, hex⟩ := feasible_exchange hr
    ((hrep a).mp ⟨a, ha, le_rfl⟩) ((hrep b).mp ⟨b, hb, le_rfl⟩)
    ((hB a ha).trans (hB b hb).symm) hi
  exact ⟨j, hj, (hB.mem_iff_contains ((exchange_degree a i j (by omega)).trans (hB a ha))).mpr
    ((hrep _).mpr hex)⟩

end CommAlg.Polymatroid
