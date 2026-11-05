import Characterizations.PureDegree

/-! # Capped Veronese families and deletion of one generator -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def boundedFamily (d : ℕ) (W : Finset V) : Family V :=
  (Finsupp.finite_of_degree_eq (σ := V) d).toFinset.filter (fun a => ∀ i ∈ W, a i ≤ 1)

@[simp] theorem mem_boundedFamily (d : ℕ) (W : Finset V) (a : Exponent V) :
    a ∈ boundedFamily d W ↔ a.degree = d ∧ ∀ i ∈ W, a i ≤ 1 := by
  simp [boundedFamily]

def deletedBounded (d : ℕ) (W : Finset V) (h : Exponent V) : Family V :=
  (boundedFamily d W).erase h

@[simp] theorem mem_deletedBounded (d : ℕ) (W : Finset V) (h a : Exponent V) :
    a ∈ deletedBounded d W h ↔ a ≠ h ∧ a.degree = d ∧ ∀ i ∈ W, a i ≤ 1 := by
  simp [deletedBounded]

theorem boundedFamily_equigenerated (d : ℕ) (W : Finset V) :
    Equigenerated (boundedFamily d W) d := fun a ha => ((mem_boundedFamily _ _ _).mp ha).1

theorem deletedBounded_equigenerated (d : ℕ) (W : Finset V) (h : Exponent V) :
    Equigenerated (deletedBounded d W h) d := fun a ha => ((mem_deletedBounded _ _ _ _).mp ha).2.1

theorem boundedFamily_exchange {d : ℕ} {W : Finset V} {a b : Exponent V}
    (ha : a ∈ boundedFamily d W) (hb : b ∈ boundedFamily d W)
    {p q : V} (hp : a p < b p) (hq : b q < a q) :
    exchange b p q ∈ boundedFamily d W := by
  obtain ⟨had, hac⟩ := (mem_boundedFamily _ _ _).mp ha
  obtain ⟨hbd, hbc⟩ := (mem_boundedFamily _ _ _).mp hb
  have hpq : p ≠ q := by intro h; subst q; omega
  apply (mem_boundedFamily _ _ _).mpr
  refine ⟨(exchange_degree b p q (by omega)).trans hbd, ?_⟩
  intro x hx
  have hbx := hbc x hx
  by_cases hxq : x = q
  · subst x
    have haq := hac q hx
    simp only [exchange_apply, if_neg hpq.symm, ite_true, Nat.sub_zero]
    omega
  · simp only [exchange_apply, if_neg hxq, Nat.add_zero]
    split_ifs <;> omega

theorem exchange_sub_self (b : Exponent V) {p q : V} (hpq : p ≠ q) :
    exchange b p q - b = Finsupp.single q 1 := by
  ext x
  simp only [Finsupp.tsub_apply, exchange_apply, Finsupp.single_apply]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;> simp_all [eq_comm] <;> omega

theorem exchange_receiver_injective (b : Exponent V) (p : V) :
    Function.Injective (exchange b p) := by
  intro i j he
  by_contra hij
  have hh := congrArg (fun a : Exponent V => a i) he
  simp only [exchange_apply, ite_true, if_neg hij] at hh
  omega

theorem exchange_eq_of_unique_receiver {a b : Exponent V} {p q : V}
    (hdeg : a.degree = b.degree) (hp : a p < b p)
    (hq : a q = b q + 1) (hunique : ∀ i, b i < a i → i = q) :
    a = exchange b p q := by
  have hpq : p ≠ q := by intro he; subst q; omega
  apply eq_of_le_of_degree_eq
  · intro x
    by_cases hxp : x = p
    · subst x
      simp only [exchange_apply, ite_true, if_neg hpq, Nat.add_zero]
      omega
    by_cases hxq : x = q
    · subst x
      simp only [exchange_apply, if_neg hpq.symm, ite_true, Nat.sub_zero]
      exact hq.le
    have hx : a x ≤ b x := by
      by_contra hx
      exact hxq (hunique x (by omega))
    simpa [exchange_apply, hxp, hxq] using hx
  · exact hdeg.trans (exchange_degree b p q (by omega)).symm

/-- Any failed prescribed exchange after one deletion has one receiving
coordinate, and both donor and receiver lie outside the saturated caps. -/
theorem deletedBounded_failed_exchange {d : ℕ} {W : Finset V} {h a b : Exponent V}
    (hsat : ∀ i ∈ W, h i = 1)
    (ha : a ∈ deletedBounded d W h) (hb : b ∈ deletedBounded d W h)
    {p : V} (hp : a p < b p)
    (hbad : ∀ q, b q < a q → exchange b p q ∉ deletedBounded d W h) :
    ∃ q, (∀ i, b i < a i ↔ i = q) ∧ p ≠ q ∧ p ∉ W ∧ q ∉ W ∧
      0 < h q ∧ exchange b p q = h ∧ b = exchange h q p := by
  obtain ⟨han, had, hac⟩ := (mem_deletedBounded _ _ _ _).mp ha
  obtain ⟨hbn, hbd, hbc⟩ := (mem_deletedBounded _ _ _ _).mp hb
  obtain ⟨q, hq⟩ := exists_surplus (hbd.trans had.symm) hp
  have hpq : p ≠ q := by intro he; subst q; omega
  have heq (i : V) (hi : b i < a i) : exchange b p i = h := by
    have hfull := boundedFamily_exchange ((mem_boundedFamily _ _ _).mpr ⟨had, hac⟩)
      ((mem_boundedFamily _ _ _).mpr ⟨hbd, hbc⟩) hp hi
    by_contra he
    exact hbad i hi (mem_erase.mpr ⟨he, hfull⟩)
  have huniq (i : V) (hi : b i < a i) : i = q :=
    exchange_receiver_injective b p ((heq i hi).trans (heq q hq).symm)
  have hpW : p ∉ W := by
    intro hpW
    have hh := congrArg (fun a : Exponent V => a p) (heq q hq)
    have hbp := hbc p hpW
    simp only [exchange_apply, ite_true, if_neg hpq, Nat.add_zero, hsat p hpW] at hh
    omega
  have hhq : h q = b q + 1 := by
    have hh := congrArg (fun a : Exponent V => a q) (heq q hq)
    simpa only [exchange_apply, if_neg hpq.symm, ite_true, Nat.sub_zero] using hh.symm
  have hqW : q ∉ W := by
    intro hqW
    have haq := hac q hqW
    have he : a q = b q + 1 := by omega
    exact han ((exchange_eq_of_unique_receiver (had.trans hbd.symm) hp he huniq).trans (heq q hq))
  refine ⟨q, fun i => ⟨huniq i, fun he => he ▸ hq⟩, hpq, hpW, hqW,
    by omega, heq q hq, ?_⟩
  rw [← heq q hq, exchange_inverse hpq (by omega)]

/-- Lemma 4.6 in a slightly stronger form: the removed exponent can be
arbitrary off the capped coordinates. -/
theorem deletedBounded_linearQuotients_last {k : Type*} [CommSemiring k]
    (d : ℕ) (W : Finset V) (h : Exponent V) (hsat : ∀ i ∈ W, h i = 1)
    (o : VariableOrder V) (w : V) (hw : w ∈ W) (hlast : LastVariable o w) :
    HasLinearQuotients k (deletedBounded d W h) (variableRevlex o) := by
  apply linearQuotients_of_witness
  intro a ha b hb hab
  obtain ⟨han, had, hac⟩ := (mem_deletedBounded _ _ _ _).mp ha
  obtain ⟨hbn, hbd, hbc⟩ := (mem_deletedBounded _ _ _ _).mp hb
  obtain ⟨p, hp, hafter⟩ := hab
  obtain ⟨q, hq⟩ := exists_surplus (hbd.trans had.symm) hp
  have hpq : p ≠ q := by intro he; subst q; omega
  have hqp : o q < o p := by
    rcases lt_trichotomy (o q) (o p) with h | h | h
    · exact h
    · exact (hpq (o.injective h).symm).elim
    · have hh := hafter q h
      omega
  have hfull := boundedFamily_exchange ((mem_boundedFamily _ _ _).mpr ⟨had, hac⟩)
    ((mem_boundedFamily _ _ _).mpr ⟨hbd, hbc⟩) hp hq
  by_cases he : exchange b p q = h
  · have hpw : p ≠ w := by
      intro hpw
      subst p
      have hh := congrArg (fun a : Exponent V => a w) he
      have hbw := hbc w hw
      simp only [exchange_apply, ite_true, if_neg hpq, Nat.add_zero, hsat w hw] at hh
      omega
    have hqw : q ≠ w := by
      intro hqw
      subst q
      exact (not_lt_of_gt (hlast p hpw)) hqp
    have hbw : b w = 1 := by
      have hh := congrArg (fun a : Exponent V => a w) he
      simpa only [exchange_apply, if_neg hpw.symm, if_neg hqw.symm,
        Nat.sub_zero, Nat.add_zero, hsat w hw] using hh
    have hnew : exchange b w q ∈ boundedFamily d W := by
      apply (mem_boundedFamily _ _ _).mpr
      refine ⟨(exchange_degree b w q (by omega)).trans hbd, ?_⟩
      intro x hx
      have hbx := hbc x hx
      by_cases hxq : x = q
      · subst x
        have haq := hac q hx
        simp only [exchange_apply, if_neg hqw, ite_true, Nat.sub_zero]
        omega
      · simp only [exchange_apply, if_neg hxq, Nat.add_zero]
        split_ifs <;> omega
    have hne : exchange b w q ≠ h := by
      intro hew
      have hh := congrArg (fun a : Exponent V => a w) hew
      simp [hbw, hqw.symm, hsat w hw] at hh
    exact ⟨exchange b w q, mem_erase.mpr ⟨hne, hnew⟩,
      variableRevlex_exchange o b (hlast q hqw) (by omega), q,
      exchange_sub_self b hqw.symm, hq⟩
  · exact ⟨exchange b p q, mem_erase.mpr ⟨he, hfull⟩,
      variableRevlex_exchange o b hqp (by omega), q, exchange_sub_self b hpq, hq⟩

end Characterizations
