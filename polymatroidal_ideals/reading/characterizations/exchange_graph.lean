import CommAlg.Polymatroid.Exponents
import Mathlib.Logic.Relation

/-! # Unit-exchange paths in coordinate boxes

All vertices are actual nonnegative integer exponent vectors. A box path is
the ordinary finite reflexive-transitive closure of unit exchanges inside the
specified family and coordinate box.
-/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def UnitStep (a b : Exponent V) : Prop :=
  ∃ i j, i ≠ j ∧ 0 < a i ∧ b = exchange a i j

theorem UnitStep.symm {a b : Exponent V} (h : UnitStep a b) : UnitStep b a := by
  obtain ⟨i, j, hij, hi, rfl⟩ := h
  refine ⟨j, i, hij.symm, ?_, (exchange_inverse hij hi).symm⟩
  simp only [exchange_apply, if_neg hij.symm, ite_true]
  omega

def BoxStep (B : Family V) (C a b : Exponent V) : Prop :=
  a ∈ B ∧ b ∈ B ∧ a ≤ C ∧ b ≤ C ∧ UnitStep a b

def BoxConnected (B : Family V) : Prop :=
  ∀ C a, a ∈ B → a ≤ C → ∀ b, b ∈ B → b ≤ C →
    Relation.ReflTransGen (BoxStep B C) a b

def l1Distance (a b : Exponent V) : ℕ := (a - b).degree + (b - a).degree

def DonorGood (B : Family V) (C : Exponent V) (j : V) (a : Exponent V) : Prop :=
  ∃ i, i ≠ j ∧ 0 < a j ∧ exchange a j i ∈ B ∧ exchange a j i ≤ C

theorem step_preserves_top_coordinate {B : Family V} {C a b : Exponent V} {j : V}
    (hab : BoxStep B C a b) (haj : a j = C j) (hbad : ¬ DonorGood B C j a) :
    b j = C j := by
  obtain ⟨ha, hb, haC, hbC, p, q, hpq, hp, rfl⟩ := hab
  have hpj : p ≠ j := by
    intro he
    subst p
    exact hbad ⟨q, hpq.symm, hp, hb, hbC⟩
  have hqj : q ≠ j := by
    intro he
    subst q
    have hh := hbC j
    simp only [exchange_apply, if_neg hpj.symm, ite_true] at hh
    omega
  simpa only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, Nat.sub_zero,
    Nat.add_zero] using haj

theorem first_good_boundary {B : Family V} {C a b : Exponent V} {j : V}
    (hpath : Relation.ReflTransGen (BoxStep B C) a b)
    (haj : a j = C j) (hbad : ¬ DonorGood B C j a) (hbj : b j < C j) :
    ∃ c c', BoxStep B C c c' ∧ c j = C j ∧
      ¬ DonorGood B C j c ∧ DonorGood B C j c' := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => omega
  | @head a c hac hcb ih =>
    by_cases hc : DonorGood B C j c
    · exact ⟨a, c, hac, haj, hbad, hc⟩
    · exact ih (step_preserves_top_coordinate hac haj hbad) hc

theorem two_exchanges_cancel (c : Exponent V) {p q j : V}
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j) (hp : 0 < c p) :
    exchange (exchange c p q) j p = exchange c j q := by
  ext x
  simp only [exchange_apply]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;> by_cases hxj : x = j <;>
    simp_all <;> omega

theorem two_exchanges_distance (c : Exponent V) {p q i j : V}
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hip : i ≠ p) (hij : i ≠ j) (hp : 0 < c p) (hj : 0 < c j) :
    l1Distance c (exchange (exchange c p q) j i) = 4 := by
  have hsub : c - exchange (exchange c p q) j i =
      Finsupp.single p 1 + Finsupp.single j 1 := by
    ext x
    simp only [Finsupp.tsub_apply, exchange_apply, Finsupp.add_apply, Finsupp.single_apply]
    by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [eq_comm] <;> omega
  have hsub' : exchange (exchange c p q) j i - c =
      Finsupp.single q 1 + Finsupp.single i 1 := by
    ext x
    simp only [Finsupp.tsub_apply, exchange_apply, Finsupp.add_apply, Finsupp.single_apply]
    by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [eq_comm] <;> omega
  simp [l1Distance, hsub, hsub']

theorem exchange_le_of_two_exchanges {C c : Exponent V} {p q i j : V}
    (hc : c ≤ C) (hu : exchange (exchange c p q) j i ≤ C)
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hip : i ≠ p) (hij : i ≠ j) :
    exchange c j i ≤ C ∧ exchange c j q ≤ C := by
  constructor <;> intro x
  all_goals
    have hcx := hc x
    have hux := hu x
    simp only [exchange_apply] at hux ⊢
    by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [eq_comm] <;> omega

/-- The exact configuration found at the first vertex where the prescribed
donor can be decreased. The two receiving coordinates may initially coincide. -/
theorem failed_exchange_configuration {B : Family V} (hconn : BoxConnected B)
    (hfail : ¬ ExchangeAxiom B) :
    ∃ c u : Exponent V, c ∈ B ∧ u ∈ B ∧
      ∃ p q i j : V, p ≠ q ∧ p ≠ j ∧ q ≠ j ∧ i ≠ p ∧ i ≠ j ∧
        0 < c p ∧ 0 < c j ∧ u = exchange (exchange c p q) j i ∧
        exchange c j i ∉ B ∧ exchange c j q ∉ B := by
  classical
  simp only [ExchangeAxiom, not_forall] at hfail
  obtain ⟨b, hb, a, ha, j, haj, hnone⟩ := hfail
  simp only [not_exists, not_and] at hnone
  let C := a ⊔ b
  have hbj : b j = C j := by simp only [C, Finsupp.sup_apply]; omega
  have hajC : a j < C j := by rw [← hbj]; exact haj
  have hbad : ¬ DonorGood B C j b := by
    rintro ⟨i, hij, hj, hex, heC⟩
    have hi := heC i
    simp only [exchange_apply, if_neg hij, ite_true, C, Finsupp.sup_apply] at hi
    exact hnone i (by omega) hex
  obtain ⟨c, c', hstep, hcj, hbadc, hgood⟩ :=
    first_good_boundary (hconn C b hb le_sup_right a ha le_sup_left) hbj hbad hajC
  obtain ⟨hc, hc', hcC, hc'C, p, q, hpq, hp, he⟩ := hstep
  subst c'
  have hpj : p ≠ j := by
    intro he
    subst p
    exact hbadc ⟨q, hpq.symm, hp, hc', hc'C⟩
  have hqj : q ≠ j := by
    intro he
    subst q
    have hh := hc'C j
    simp only [exchange_apply, if_neg hpj.symm, ite_true] at hh
    omega
  obtain ⟨i, hij, hj', hu, huC⟩ := hgood
  have hj : 0 < c j := by
    simpa only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm,
      Nat.sub_zero, Nat.add_zero] using hj'
  have hip : i ≠ p := by
    intro he
    subst i
    rw [two_exchanges_cancel c hpq hpj hqj hp] at hu huC
    exact hbadc ⟨q, hqj, hj, hu, huC⟩
  obtain ⟨hiC, hqC⟩ := exchange_le_of_two_exchanges hcC huC hpq hpj hqj hip hij
  exact ⟨c, exchange (exchange c p q) j i, hc, hu, p, q, i, j,
    hpq, hpj, hqj, hip, hij, hp, hj, rfl,
    fun h => hbadc ⟨i, hij, hj, h, hiC⟩,
    fun h => hbadc ⟨q, hqj, hj, h, hqC⟩⟩

/-- Lemma 3.2: failure of exchange is witnessed at ℓ₁-distance exactly four. -/
theorem failed_exchange_distance_four {B : Family V} (hconn : BoxConnected B)
    (hfail : ¬ ExchangeAxiom B) :
    ∃ c u : Exponent V, c ∈ B ∧ u ∈ B ∧ l1Distance c u = 4 ∧
      ∃ j, u j < c j ∧ ∀ i, c i < u i → exchange c j i ∉ B := by
  obtain ⟨c, u, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij,
    hp, hj, rfl, hni, hnq⟩ := failed_exchange_configuration hconn hfail
  refine ⟨c, _, hc, hu, two_exchanges_distance c hpq hpj hqj hip hij hp hj, j, ?_, ?_⟩
  · simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm,
      if_neg hij.symm, ite_true, Nat.sub_zero, Nat.add_zero]
    omega
  · intro x hx
    by_cases hxi : x = i
    · simpa [hxi] using hni
    by_cases hxq : x = q
    · simpa [hxq] using hnq
    simp only [exchange_apply, if_neg hxi, if_neg hxq, Nat.add_zero] at hx
    split_ifs at hx <;> omega

end Characterizations
