import Characterizations.BoundedFamilies

/-! # The exact final-pair obstruction (Lemma 5.1) -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def onesOn (S : Finset V) : Exponent V := ∑ i ∈ S, Finsupp.single i 1

@[simp] theorem onesOn_apply (S : Finset V) (i : V) :
    onesOn S i = if i ∈ S then 1 else 0 := by
  simp [onesOn, Finsupp.finsetSum_apply, Finsupp.single_apply]

@[simp] theorem onesOn_degree (S : Finset V) : (onesOn S).degree = S.card := by
  simp [onesOn, map_sum]

def pairCap (i j : V) : Finset V := univ \ {i, j}
def pairHole (j : V) : Exponent V := onesOn (univ.erase j)
def pairFamily (i j : V) : Family V :=
  deletedBounded (Fintype.card V - 1) (pairCap i j) (pairHole j)

@[simp] theorem mem_pairCap (i j x : V) : x ∈ pairCap i j ↔ x ≠ i ∧ x ≠ j := by
  simp [pairCap, and_comm]

@[simp] theorem pairHole_apply (j x : V) : pairHole j x = if x = j then 0 else 1 := by
  simp [pairHole, eq_comm]

@[simp] theorem pairHole_degree (j : V) : (pairHole j).degree = Fintype.card V - 1 := by
  simp [pairHole]

theorem pairFamily_equigenerated (i j : V) :
    Equigenerated (pairFamily i j) (Fintype.card V - 1) :=
  deletedBounded_equigenerated _ _ _

theorem pairFamily_sat (i j : V) (x : V) (hx : x ∈ pairCap i j) : pairHole j x = 1 := by
  simp [((mem_pairCap _ _ _).mp hx).2]

theorem pairFamily_last_failure {i j : V} (hij : i ≠ j) {a b : Exponent V}
    (ha : a ∈ pairFamily i j) (hb : b ∈ pairFamily i j) {p : V} (hp : a p < b p)
    (hbad : ∀ q, b q < a q → exchange b p q ∉ pairFamily i j) :
    p = j ∧ (∀ x, b x < a x ↔ x = i) ∧ b = pairHole i := by
  obtain ⟨q, huniq, hpq, hpW, hqW, hhq, he, hbEq⟩ :=
    deletedBounded_failed_exchange (pairFamily_sat i j) ha hb hp hbad
  have hqij : q = i ∨ q = j := by
    by_contra hn
    exact hqW ((mem_pairCap _ _ _).mpr ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩)
  have hqj : q ≠ j := by intro he; subst q; simp at hhq
  have hqi : q = i := hqij.resolve_right hqj
  subst q
  have hpij : p = i ∨ p = j := by
    by_contra hn
    exact hpW ((mem_pairCap _ _ _).mpr ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩)
  have hpj : p = j := hpij.resolve_left hpq
  subst p
  refine ⟨rfl, huniq, hbEq.trans ?_⟩
  ext x
  simp only [exchange_apply, pairHole_apply]
  by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp [hxi, hxj, hij] <;> omega

theorem pairFamily_linearQuotients_of_not_final {k : Type*} [CommSemiring k]
    {i j : V} (hij : i ≠ j) (o : VariableOrder V) (hnot : ¬ FinalPair o i j) :
    HasLinearQuotients k (pairFamily i j) (variableRevlex o) := by
  apply linearQuotients_of_witness
  intro a ha b hb hab
  obtain ⟨p, hp, he⟩ := hab
  by_cases hex : ∃ q, b q < a q ∧ exchange b p q ∈ pairFamily i j
  · obtain ⟨q, hq, hmem⟩ := hex
    have hpq : p ≠ q := by intro h; subst q; omega
    have hqp : o q < o p := by
      rcases lt_trichotomy (o q) (o p) with h | h | h
      · exact h
      · exact (hpq (o.injective h).symm).elim
      · have hh := he q h; omega
    exact ⟨_, hmem, variableRevlex_exchange o b hqp (by omega), q,
      exchange_sub_self b hpq, hq⟩
  · have hbad : ∀ q, b q < a q → exchange b p q ∉ pairFamily i j := by
      simpa only [not_exists, not_and] using hex
    obtain ⟨hpj, huniq, hbEq⟩ := pairFamily_last_failure hij ha hb hp hbad
    subst p
    have hai : b i < a i := (huniq i).mpr rfl
    have hijOrder : o i < o j := by
      rcases lt_trichotomy (o i) (o j) with h | h | h
      · exact h
      · exact (hij (o.injective h)).elim
      · have hh := he i h; omega
    have ht : ∃ t, t ≠ i ∧ t ≠ j ∧ o i < o t := by
      by_contra ht
      apply hnot
      refine ⟨hijOrder, ?_⟩
      intro t hti htj
      have hn : ¬ o i < o t := fun h => ht ⟨t, hti, htj, h⟩
      exact lt_of_le_of_ne (le_of_not_gt hn) (fun h => hti (o.injective h))
    obtain ⟨t, hti, htj, hit⟩ := ht
    have hbt : b t = 1 := by simp [hbEq, hti]
    have hmem : exchange b t i ∈ pairFamily i j := by
      apply (mem_deletedBounded _ _ _ _).mpr
      refine ⟨?_, (exchange_degree b t i (by omega)).trans
        (pairFamily_equigenerated i j b hb), ?_⟩
      · intro hh
        have hhj := congrArg (fun a : Exponent V => a j) hh
        simp [exchange_apply, hbEq, htj.symm, hij.symm] at hhj
      · intro x hx
        obtain ⟨hxi, hxj⟩ := (mem_pairCap _ _ _).mp hx
        simp only [exchange_apply, if_neg hxi, Nat.add_zero]
        have hbx : b x = 1 := by simp [hbEq, hxi]
        rw [hbx]
        split_ifs <;> omega
    exact ⟨_, hmem, variableRevlex_exchange o b hit (by omega), i,
      exchange_sub_self b hti, hai⟩

theorem pairFamily_counter_generators {i j v : V} (hij : i ≠ j)
    (hv : v ∈ pairCap i j) :
    pairHole i ∈ pairFamily i j ∧ exchange (pairHole j) v i ∈ pairFamily i j := by
  obtain ⟨hvi, hvj⟩ := (mem_pairCap _ _ _).mp hv
  constructor
  · apply (mem_deletedBounded _ _ _ _).mpr
    refine ⟨?_, pairHole_degree i, ?_⟩
    · intro he
      have hi := congrArg (fun a : Exponent V => a i) he
      simp [hij] at hi
    · intro x hx
      simp only [pairHole_apply]
      split_ifs <;> omega
  · apply (mem_deletedBounded _ _ _ _).mpr
    refine ⟨exchange_ne hvi (by simp [hvj]),
      (exchange_degree _ v i (by simp [hvj])).trans (pairHole_degree j), ?_⟩
    intro x hx
    obtain ⟨hxi, hxj⟩ := (mem_pairCap _ _ _).mp hx
    simp only [exchange_apply, if_neg hxi, Nat.add_zero, pairHole_apply, if_neg hxj]
    split_ifs <;> omega

theorem pairFamily_not_linearQuotients_final {k : Type*} [CommSemiring k] [Nontrivial k]
    {i j : V} (hij : i ≠ j) (hcard : 3 ≤ Fintype.card V)
    (o : VariableOrder V) (hfinal : FinalPair o i j) :
    ¬ HasLinearQuotients k (pairFamily i j) (variableRevlex o) := by
  intro hL
  have hWcard : (pairCap i j).card = Fintype.card V - 2 := by
    rw [pairCap, card_sdiff_of_subset (subset_univ _)]
    simp [hij]
  obtain ⟨v, hv⟩ : (pairCap i j).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hvi, hvj⟩ := (mem_pairCap _ _ _).mp hv
  obtain ⟨hb, ha⟩ := pairFamily_counter_generators hij hv
  let a := exchange (pairHole j) v i
  let b := pairHole i
  have hdef (x : V) : b x < a x ↔ x = i := by
    simp only [a, b, exchange_apply, pairHole_apply]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> by_cases hxv : x = v <;>
      simp_all [eq_comm] <;> omega
  have hab : variableRevlex o a b := by
    refine ⟨j, ?_, fun x hx => (hfinal.no_after x hx).elim⟩
    simp [a, b, exchange_apply, hvj.symm, hij.symm]
  obtain ⟨w, hw, hwb, z, hwz, haz⟩ := witness_of_linearQuotients
    (pairFamily_equigenerated i j).antichain (variableRevlex_irrefl o) hL a ha b hb hab
  have hzi : z = i := (hdef z).mp haz
  subst z
  obtain ⟨t, hit, ht, hew⟩ := witness_is_exchange (pairFamily_equigenerated i j) hw hb hwz
  have horder := (variableRevlex_exchange_iff o b hit.symm ht).mp (hew ▸ hwb)
  have htj : t = j := by
    by_contra htj
    exact (not_lt_of_gt (hfinal.2 t hit.symm htj)) horder
  have hwh : w = pairHole j := by
    rw [hew, htj]
    ext x
    simp only [b, exchange_apply, pairHole_apply]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [eq_comm]
  exact ((mem_deletedBounded _ _ _ _).mp hw).1 hwh

/-- Exact failure signature of Lemma 5.1. -/
theorem pairFamily_linearQuotients_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    {i j : V} (hij : i ≠ j) (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) :
    HasLinearQuotients k (pairFamily i j) (variableRevlex o) ↔ ¬ FinalPair o i j := by
  exact ⟨fun h hf => pairFamily_not_linearQuotients_final hij hcard o hf h,
    pairFamily_linearQuotients_of_not_final hij o⟩

theorem pairFamily_not_polymatroidal {i j : V} (hij : i ≠ j)
    (hcard : 3 ≤ Fintype.card V) : ¬ IsPolymatroidal (pairFamily i j) := by
  intro h
  obtain ⟨o, ho⟩ := exists_finalPair i j hij
  exact pairFamily_not_linearQuotients_final (k := ℚ) hij hcard o ho
    (polymatroidal_variable_linearQuotients h.2 o)

end Characterizations
