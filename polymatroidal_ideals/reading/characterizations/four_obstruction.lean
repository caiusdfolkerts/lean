import Characterizations.WitnessPaths

/-! # The four-coordinate exchange obstruction -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def SingletonExchange (B : Family V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ i,
    (∀ h, b h < a h ↔ h = i) → ∀ j, a j < b j → exchange b j i ∈ B

theorem exchange_mem_donor_pos {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    {c : Exponent V} (hc : c ∈ B) {i j : V} (hex : exchange c i j ∈ B) : 0 < c i := by
  by_contra hi
  have hz : c i = 0 := by omega
  have hsub : c - Finsupp.single i 1 = c := by
    ext x
    by_cases hx : x = i
    · subst x; simp [hz]
    · simp [Finsupp.single_apply, hx, Ne.symm hx]
  have hd := hB (exchange c i j) hex
  simp only [exchange, hsub, map_add, Finsupp.degree_single, hB c hc] at hd
  omega

theorem two_exchanges_unique_receiver (c : Exponent V) {p i j : V}
    (hpi : p ≠ i) (hpj : p ≠ j) (hij : i ≠ j) (h : V) :
    c h < exchange (exchange c p i) j i h ↔ h = i := by
  simp only [exchange_apply]
  by_cases hhp : h = p <;> by_cases hhi : h = i <;> by_cases hhj : h = j <;>
    simp_all [eq_comm] <;> omega

theorem two_exchanges_against_receiver_swap (c : Exponent V) {p q i j : V}
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hip : i ≠ p) (hij : i ≠ j) (hiq : i ≠ q) (hq : 0 < c q) (h : V) :
    exchange c q i h < exchange (exchange c p q) j i h ↔ h = q := by
  simp only [exchange_apply]
  by_cases hhp : h = p <;> by_cases hhq : h = q <;>
    by_cases hhi : h = i <;> by_cases hhj : h = j <;> simp_all [eq_comm] <;> omega

theorem two_exchanges_commute (c : Exponent V) {p q i j : V}
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hip : i ≠ p) (hij : i ≠ j) :
    exchange (exchange c p q) j i = exchange (exchange c p i) j q := by
  ext h
  simp only [exchange_apply]
  by_cases hhp : h = p <;> by_cases hhq : h = q <;>
    by_cases hhi : h = i <;> by_cases hhj : h = j <;> simp_all [eq_comm] <;> omega

/-- Lemma 3.5, with all nonnegativity obligations explicit and discharged.
The two additional missing swaps are actual exponent-vector nonmembership. -/
theorem four_coordinate_obstruction {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (hconn : BoxConnected B) (hsingle : SingletonExchange B)
    (hfail : ¬ ExchangeAxiom B) :
    ∃ c u : Exponent V, c ∈ B ∧ u ∈ B ∧
      ∃ p q i j : V, p ≠ q ∧ p ≠ j ∧ q ≠ j ∧ i ≠ p ∧ i ≠ j ∧ i ≠ q ∧
        0 < c p ∧ 0 < c j ∧ u = exchange (exchange c p q) j i ∧
        exchange c j i ∉ B ∧ exchange c j q ∉ B ∧
        exchange c q i ∉ B ∧ exchange c i q ∉ B := by
  obtain ⟨c, u, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij, hp, hj, he, hni, hnq⟩ :=
    failed_exchange_configuration hconn hfail
  subst u
  have hjdrop : exchange (exchange c p q) j i j < c j := by
    simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, if_neg hij.symm,
      ite_true, Nat.sub_zero, Nat.add_zero]
    omega
  have hiq : i ≠ q := by
    intro he
    subst q
    exact hni (hsingle _ hu c hc i (two_exchanges_unique_receiver c hpq hpj hij) j hjdrop)
  have hnoSwap (p q i j : V) (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
      (hip : i ≠ p) (hij : i ≠ j) (hiq : i ≠ q) (hj : 0 < c j)
      (hu : exchange (exchange c p q) j i ∈ B)
      (hni : exchange c j i ∉ B) : exchange c q i ∉ B := by
    intro hv
    have hq := exchange_mem_donor_pos hB hc hv
    have hdrop : exchange (exchange c p q) j i j < exchange c q i j := by
      simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, if_neg hij.symm,
        ite_true, Nat.sub_zero, Nat.add_zero]
      omega
    have hh := hsingle _ hu _ hv q
      (two_exchanges_against_receiver_swap c hpq hpj hqj hip hij hiq hq) j hdrop
    rw [two_exchanges_cancel c hiq.symm hqj hij hq] at hh
    exact hni hh
  have hqi := hnoSwap p q i j hpq hpj hqj hip hij hiq hj hu hni
  have hiq' := hnoSwap p i q j hip.symm hpj hij hpq.symm hqj hiq.symm hj
    (by rwa [← two_exchanges_commute c hpq hpj hqj hip hij]) hnq
  exact ⟨c, _, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij, hiq,
    hp, hj, rfl, hni, hnq, hqi, hiq'⟩

end Characterizations
