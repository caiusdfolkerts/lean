import Characterizations.PairIsolator

/-! # The exact pointed-triple obstruction (Lemma 5.2) -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def tripleCap (i q z : V) : Finset V := univ \ {i, q, z}
def tripleCondition (i q z : V) (a : Exponent V) : Prop :=
  0 < a z ∨ (0 < a i ∧ 0 < a q)
def tripleFamily (i q z : V) : Family V :=
  (boundedFamily (Fintype.card V - 2) (tripleCap i q z)).filter (tripleCondition i q z)
def tripleBase (i q : V) : Exponent V := onesOn (univ \ {i, q})

@[simp] theorem mem_tripleCap (i q z x : V) :
    x ∈ tripleCap i q z ↔ x ≠ i ∧ x ≠ q ∧ x ≠ z := by simp [tripleCap]
@[simp] theorem mem_tripleFamily (i q z : V) (a : Exponent V) :
    a ∈ tripleFamily i q z ↔ a ∈ boundedFamily (Fintype.card V - 2) (tripleCap i q z) ∧
      tripleCondition i q z a := by simp [tripleFamily]
@[simp] theorem tripleBase_apply (i q x : V) :
    tripleBase i q x = if x = i ∨ x = q then 0 else 1 := by
  by_cases hxi : x = i <;> by_cases hxq : x = q <;> simp [tripleBase, hxi, hxq]
@[simp] theorem tripleBase_degree {i q : V} (hiq : i ≠ q) :
    (tripleBase i q).degree = Fintype.card V - 2 := by
  rw [tripleBase, onesOn_degree, card_sdiff_of_subset (subset_univ _)]
  simp [hiq]

theorem tripleFamily_equigenerated (i q z : V) :
    Equigenerated (tripleFamily i q z) (Fintype.card V - 2) :=
  fun _ ha => ((mem_boundedFamily _ _ _).mp ((mem_tripleFamily _ _ _ _).mp ha).1).1

theorem condition_receive_z (i q z p : V) (b : Exponent V) :
    tripleCondition i q z (exchange b p z) := by
  left
  simp only [exchange_apply, ite_true]
  omega

theorem condition_keep_z {i q z p r : V} {b : Exponent V}
    (hz : 0 < b z) (hpz : p ≠ z) : tripleCondition i q z (exchange b p r) := by
  left
  simp only [exchange_apply, if_neg hpz.symm, Nat.sub_zero]
  omega

theorem condition_large_z {i q z p r : V} {b : Exponent V}
    (hz : 2 ≤ b z) : tripleCondition i q z (exchange b p r) := by
  left
  simp only [exchange_apply]
  split_ifs <;> omega

theorem condition_keep_both {i q z p r : V} {b : Exponent V}
    (hi : 0 < b i) (hq : 0 < b q)
    (hpi : p ≠ i ∨ 2 ≤ b i) (hpq : p ≠ q ∨ 2 ≤ b q) :
    tripleCondition i q z (exchange b p r) := by
  right
  simp only [exchange_apply]
  constructor
  · rcases hpi with h | h
    · rw [if_neg h.symm]; omega
    · split_ifs <;> omega
  · rcases hpq with h | h
    · rw [if_neg h.symm]; omega
    · split_ifs <;> omega

/-- The non-convex condition has only one type of prescribed-exchange failure. -/
theorem condition_failed_exchange {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    {a b : Exponent V} (ha : tripleCondition i q z a) (hb : tripleCondition i q z b)
    {p : V} (hp : a p < b p) (hr : ∃ r, b r < a r)
    (hbad : ∀ r, b r < a r → ¬ tripleCondition i q z (exchange b p r)) :
    p = z ∧ b z = 1 ∧ b i = 0 ∧ b q = 0 ∧ 0 < a i ∧ 0 < a q := by
  obtain ⟨r, hr⟩ := hr
  have hbz : 0 < b z := by
    by_contra hn
    have hbz : b z = 0 := by omega
    obtain ⟨hbi, hbq⟩ : 0 < b i ∧ 0 < b q := by simpa [tripleCondition, hbz] using hb
    have hpiq : p = i ∨ p = q := by
      by_contra hn
      have hpi : p ≠ i := fun h => hn (Or.inl h)
      have hpq : p ≠ q := fun h => hn (Or.inr h)
      exact hbad r hr (condition_keep_both hbi hbq (Or.inl hpi) (Or.inl hpq))
    rcases hpiq with hpi | hpq
    · subst p
      have hbi1 : b i = 1 := by
        by_contra hn
        exact hbad r hr (condition_keep_both hbi hbq (Or.inr (by omega)) (Or.inl hiq))
      have hai : a i = 0 := by omega
      have haz : 0 < a z := by simpa [tripleCondition, hai] using ha
      exact hbad z (by omega) (condition_receive_z i q z i b)
    · subst p
      have hbq1 : b q = 1 := by
        by_contra hn
        exact hbad r hr (condition_keep_both hbi hbq (Or.inl hiq.symm) (Or.inr (by omega)))
      have haq : a q = 0 := by omega
      have haz : 0 < a z := by simpa [tripleCondition, haq] using ha
      exact hbad z (by omega) (condition_receive_z i q z q b)
  have hpz : p = z := by
    by_contra hn
    exact hbad r hr (condition_keep_z hbz hn)
  subst p
  have hbz1 : b z = 1 := by
    by_contra hn
    exact hbad r hr (condition_large_z (by omega))
  have haz : a z = 0 := by omega
  obtain ⟨hai, haq⟩ : 0 < a i ∧ 0 < a q := by simpa [tripleCondition, haz] using ha
  have hbi : b i = 0 := by
    by_contra hn
    by_cases hq : 0 < b q
    · exact hbad r hr (condition_keep_both (by omega) hq (Or.inl hiz.symm) (Or.inl hqz.symm))
    · apply hbad q (by omega)
      right
      constructor
      · simp [exchange_apply, hiz, hiq] <;> omega
      · simp [exchange_apply, hqz] <;> omega
  have hbq : b q = 0 := by
    by_contra hn
    apply hbad i (by omega)
    right
    constructor
    · simp [exchange_apply, hiz] <;> omega
    · simp [exchange_apply, hqz, hiq.symm] <;> omega
  exact ⟨rfl, hbz1, hbi, hbq, hai, haq⟩

theorem tripleFamily_failed_exchange {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    {a b : Exponent V} (ha : a ∈ tripleFamily i q z) (hb : b ∈ tripleFamily i q z)
    {p : V} (hp : a p < b p)
    (hbad : ∀ r, b r < a r → exchange b p r ∉ tripleFamily i q z) :
    p = z ∧ b = tripleBase i q ∧ (∀ x, b x < a x ↔ x = i ∨ x = q) := by
  obtain ⟨hab, hac⟩ := (mem_tripleFamily _ _ _ _).mp ha
  obtain ⟨hbb, hbc⟩ := (mem_tripleFamily _ _ _ _).mp hb
  obtain ⟨had, hacap⟩ := (mem_boundedFamily _ _ _).mp hab
  obtain ⟨hbd, hbcap⟩ := (mem_boundedFamily _ _ _).mp hbb
  have hbadc r (hr : b r < a r) : ¬ tripleCondition i q z (exchange b p r) := by
    intro hc
    exact hbad r hr ((mem_tripleFamily _ _ _ _).mpr ⟨boundedFamily_exchange hab hbb hp hr, hc⟩)
  obtain ⟨hpz, hbz, hbi, hbq, hai, haq⟩ := condition_failed_exchange hiq hiz hqz hac hbc hp
    (exists_surplus (hbd.trans had.symm) hp) hbadc
  have hbeq : b = tripleBase i q := by
    apply eq_of_le_of_degree_eq
    · intro x
      by_cases hxi : x = i
      · subst x; simp [hbi]
      by_cases hxq : x = q
      · subst x; simp [hbq]
      by_cases hxz : x = z
      · subst x; simp [tripleBase_apply, hiz.symm, hqz.symm, hbz]
      · simpa [tripleBase_apply, hxi, hxq] using hbcap x ((mem_tripleCap _ _ _ _).mpr ⟨hxi, hxq, hxz⟩)
    · exact hbd.trans (tripleBase_degree hiq).symm
  refine ⟨hpz, hbeq, fun x => ?_⟩
  constructor
  · intro hx
    by_contra hn
    have hxi : x ≠ i := fun h => hn (Or.inl h)
    have hxq : x ≠ q := fun h => hn (Or.inr h)
    by_cases hxz : x = z
    · subst x; subst p; omega
    · have hh := hacap x ((mem_tripleCap _ _ _ _).mpr ⟨hxi, hxq, hxz⟩)
      have hbxx : b x = 1 := by simp [hbeq, hxi, hxq]
      omega
  · rintro (rfl | rfl) <;> omega


theorem tripleBase_mem {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z) :
    tripleBase i q ∈ tripleFamily i q z := by
  apply (mem_tripleFamily _ _ _ _).mpr
  refine ⟨(mem_boundedFamily _ _ _).mpr ⟨tripleBase_degree hiq, ?_⟩, Or.inl ?_⟩
  · intro x hx
    simp only [tripleBase_apply]
    split_ifs <;> omega
  · simp [hiz.symm, hqz.symm]

theorem tripleBase_exchange_cap {i q z t r : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (ht : t ∈ tripleCap i q z) (hr : r = i ∨ r = q) :
    exchange (tripleBase i q) t r ∈ tripleFamily i q z := by
  obtain ⟨hti, htq, htz⟩ := (mem_tripleCap _ _ _ _).mp ht
  have hbt : tripleBase i q t = 1 := by simp [hti, htq]
  apply (mem_tripleFamily _ _ _ _).mpr
  refine ⟨(mem_boundedFamily _ _ _).mpr ⟨(exchange_degree _ _ _ (by omega)).trans
    (tripleBase_degree hiq), ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨hxi, hxq, hxz⟩ := (mem_tripleCap _ _ _ _).mp hx
    have hxr : x ≠ r := by rcases hr with rfl | rfl <;> assumption
    simp only [exchange_apply, if_neg hxr, Nat.add_zero]
    have hbx : tripleBase i q x = 1 := by simp [hxi, hxq]
    rw [hbx]
    split_ifs <;> omega
  · exact condition_keep_z (by simp [hiz.symm, hqz.symm]) htz

theorem tripleFamily_linearQuotients_of_not_final {k : Type*} [CommSemiring k]
    {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (o : VariableOrder V) (hnot : ¬ FinalTriple o i q z) :
    HasLinearQuotients k (tripleFamily i q z) (variableRevlex o) := by
  apply linearQuotients_of_witness
  intro a ha b hb hab
  obtain ⟨p, hp, hafter⟩ := hab
  by_cases hex : ∃ r, b r < a r ∧ exchange b p r ∈ tripleFamily i q z
  · obtain ⟨r, hr, hm⟩ := hex
    have hpr : p ≠ r := by intro h; subst r; omega
    have hrp : o r < o p := by
      rcases lt_trichotomy (o r) (o p) with h | h | h
      · exact h
      · exact (hpr (o.injective h).symm).elim
      · have hh := hafter r h; omega
    exact ⟨_, hm, variableRevlex_exchange o b hrp (by omega), r, exchange_sub_self b hpr, hr⟩
  · have hbad : ∀ r, b r < a r → exchange b p r ∉ tripleFamily i q z := by
      simpa only [not_exists, not_and] using hex
    obtain ⟨hpz, hbeq, hdef⟩ := tripleFamily_failed_exchange hiq hiz hqz ha hb hp hbad
    subst p
    have hir : b i < a i := (hdef i).mpr (Or.inl rfl)
    have hqr : b q < a q := (hdef q).mpr (Or.inr rfl)
    have hizord : o i < o z := by
      rcases lt_trichotomy (o i) (o z) with h | h | h
      · exact h
      · exact (hiz (o.injective h)).elim
      · have hh := hafter i h; omega
    have hqzord : o q < o z := by
      rcases lt_trichotomy (o q) (o z) with h | h | h
      · exact h
      · exact (hqz (o.injective h)).elim
      · have hh := hafter q h; omega
    have ht : ∃ t ∈ tripleCap i q z, o i < o t ∨ o q < o t := by
      by_contra hn
      apply hnot
      refine ⟨hizord, hqzord, ?_⟩
      intro t hti htq htz
      have htC : t ∈ tripleCap i q z := (mem_tripleCap _ _ _ _).mpr ⟨hti, htq, htz⟩
      constructor
      · exact lt_of_le_of_ne (le_of_not_gt (fun h => hn ⟨t, htC, Or.inl h⟩))
          (fun h => hti (o.injective h))
      · exact lt_of_le_of_ne (le_of_not_gt (fun h => hn ⟨t, htC, Or.inr h⟩))
          (fun h => htq (o.injective h))
    obtain ⟨t, ht, htr⟩ := ht
    obtain ⟨hti, htq, htz⟩ := (mem_tripleCap _ _ _ _).mp ht
    have hbt : b t = 1 := by simp [hbeq, hti, htq]
    rcases htr with hit | hqt
    · exact ⟨_, hbeq ▸ tripleBase_exchange_cap hiq hiz hqz ht (Or.inl rfl),
        variableRevlex_exchange o b hit (by omega), i, exchange_sub_self b hti, hir⟩
    · exact ⟨_, hbeq ▸ tripleBase_exchange_cap hiq hiz hqz ht (Or.inr rfl),
        variableRevlex_exchange o b hqt (by omega), q, exchange_sub_self b htq, hqr⟩

theorem tripleFamily_counter_target {i q z v : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (hv : v ∈ tripleCap i q z) : tripleBase z v ∈ tripleFamily i q z := by
  obtain ⟨hvi, hvq, hvz⟩ := (mem_tripleCap _ _ _ _).mp hv
  apply (mem_tripleFamily _ _ _ _).mpr
  refine ⟨(mem_boundedFamily _ _ _).mpr ⟨tripleBase_degree hvz.symm, ?_⟩, Or.inr ?_⟩
  · intro x hx
    simp only [tripleBase_apply]
    split_ifs <;> omega
  · simp [hiz, hqz, hvi.symm, hvq.symm]

theorem tripleFamily_not_linearQuotients_final {k : Type*} [CommSemiring k] [Nontrivial k]
    {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (hcard : 4 ≤ Fintype.card V) (o : VariableOrder V) (hfinal : FinalTriple o i q z) :
    ¬ HasLinearQuotients k (tripleFamily i q z) (variableRevlex o) := by
  intro hL
  have hCcard : (tripleCap i q z).card = Fintype.card V - 3 := by
    rw [tripleCap, card_sdiff_of_subset (subset_univ _)]
    simp [hiq, hiz, hqz]
  obtain ⟨v, hv⟩ : (tripleCap i q z).Nonempty := card_pos.mp (by omega)
  obtain ⟨hvi, hvq, hvz⟩ := (mem_tripleCap _ _ _ _).mp hv
  let a := tripleBase z v
  let b := tripleBase i q
  have ha : a ∈ tripleFamily i q z := tripleFamily_counter_target hiq hiz hqz hv
  have hb : b ∈ tripleFamily i q z := tripleBase_mem hiq hiz hqz
  have hdef (x : V) : b x < a x ↔ x = i ∨ x = q := by
    simp only [a, b, tripleBase_apply]
    by_cases hxi : x = i <;> by_cases hxq : x = q <;>
      by_cases hxz : x = z <;> by_cases hxv : x = v <;> simp_all [eq_comm]
  have hab : variableRevlex o a b := by
    refine ⟨z, ?_, fun x hx => (hfinal.no_after x hx).elim⟩
    simp [a, b, hiz.symm, hqz.symm]
  obtain ⟨w, hw, hwb, r, hwr, har⟩ := witness_of_linearQuotients
    (tripleFamily_equigenerated i q z).antichain (variableRevlex_irrefl o) hL a ha b hb hab
  obtain ⟨t, hrt, ht, hew⟩ := witness_is_exchange (tripleFamily_equigenerated i q z) hw hb hwr
  have hr : r = i ∨ r = q := (hdef r).mp har
  have horder := (variableRevlex_exchange_iff o b hrt.symm ht).mp (hew ▸ hwb)
  have hti : t ≠ i := by intro he; subst t; simp [b] at ht
  have htq : t ≠ q := by intro he; subst t; simp [b] at ht
  have htz : t = z := by
    by_contra hn
    have hbefore := hfinal.2.2 t hti htq hn
    rcases hr with rfl | rfl
    · exact (not_lt_of_gt hbefore.1) horder
    · exact (not_lt_of_gt hbefore.2) horder
  have hc := ((mem_tripleFamily _ _ _ _).mp hw).2
  rw [hew, htz] at hc
  rcases hr with rfl | rfl
  · simpa [tripleCondition, b, exchange_apply, hiz, hqz, hiq, hiq.symm,
      hiz.symm, hqz.symm] using hc
  · simpa [tripleCondition, b, exchange_apply, hiz, hqz, hiq, hiq.symm,
      hiz.symm, hqz.symm] using hc

/-- Exact failure signature of Lemma 5.2. -/
theorem tripleFamily_linearQuotients_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (hcard : 4 ≤ Fintype.card V) (o : VariableOrder V) :
    HasLinearQuotients k (tripleFamily i q z) (variableRevlex o) ↔ ¬ FinalTriple o i q z :=
  ⟨fun h hf => tripleFamily_not_linearQuotients_final hiq hiz hqz hcard o hf h,
    tripleFamily_linearQuotients_of_not_final hiq hiz hqz o⟩

theorem tripleFamily_not_polymatroidal {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (hcard : 4 ≤ Fintype.card V) : ¬ IsPolymatroidal (tripleFamily i q z) := by
  intro h
  obtain ⟨o, ho⟩ := exists_finalTriple i q z hiq hiz hqz
  exact tripleFamily_not_linearQuotients_final (k := ℚ) hiq hiz hqz hcard o ho
    (polymatroidal_variable_linearQuotients h.2 o)

end Characterizations
