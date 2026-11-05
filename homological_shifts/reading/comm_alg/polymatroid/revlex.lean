import CommAlg.Polymatroid.RankGreedy

/-! # Reverse lexicographic exchange and the colon variables

The strict comparison records the largest differing variable. This convention
orders equigenerated monomials in decreasing reverse lexicographic order.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

def RevlexBefore (a b : Exponent V) : Prop :=
  ∃ i, a i < b i ∧ ∀ j, i < j → a j = b j

theorem revlexBefore_irrefl (a : Exponent V) : ¬ RevlexBefore a a := by
  rintro ⟨i, hi, _⟩
  exact (lt_irrefl _ hi)

theorem revlexBefore_trans {a b c : Exponent V}
    (hab : RevlexBefore a b) (hbc : RevlexBefore b c) : RevlexBefore a c := by
  obtain ⟨i, hi, he⟩ := hab
  obtain ⟨j, hj, hf⟩ := hbc
  rcases lt_trichotomy i j with hij | rfl | hji
  · refine ⟨j, ?_, fun x hx => (he x (hij.trans hx)).trans (hf x hx)⟩
    rw [he j hij]
    exact hj
  · exact ⟨i, hi.trans hj, fun x hx => (he x hx).trans (hf x hx)⟩
  · refine ⟨i, ?_, fun x hx => (he x hx).trans (hf x (hji.trans hx))⟩
    rw [← hf i hji]
    exact hi

theorem revlexBefore_asymm {a b : Exponent V} (hab : RevlexBefore a b) :
    ¬ RevlexBefore b a := fun hba => revlexBefore_irrefl a (revlexBefore_trans hab hba)

theorem revlexBefore_total {a b : Exponent V} (hab : a ≠ b) :
    RevlexBefore a b ∨ RevlexBefore b a := by
  let D := univ.filter (fun i => a i ≠ b i)
  have hD : D.Nonempty := by
    by_contra h
    apply hab
    ext i
    by_contra hi
    exact h ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  let i := D.max' hD
  have hi : a i ≠ b i := (mem_filter.mp (D.max'_mem hD)).2
  have he : ∀ j, i < j → a j = b j := by
    intro j hij
    by_contra hj
    have hjD : j ∈ D := mem_filter.mpr ⟨mem_univ j, hj⟩
    exact (not_lt_of_ge (D.le_max' j hjD)) hij
  rcases lt_or_gt_of_ne hi with h | h
  · exact Or.inl ⟨i, h, he⟩
  · exact Or.inr ⟨i, h, fun j hj => (he j hj).symm⟩

def revlexBeforeFamily (B : Family V) (b : Exponent V) : Family V :=
  B.filter (fun a => RevlexBefore a b)

@[simp] theorem mem_revlexBeforeFamily (B : Family V) (a b : Exponent V) :
    a ∈ revlexBeforeFamily B b ↔ a ∈ B ∧ RevlexBefore a b := by
  simp [revlexBeforeFamily]

def revlexColonVariables (B : Family V) (b : Exponent V) : Finset V :=
  univ.filter (fun j => ∃ i, j < i ∧ 0 < b i ∧ exchange b i j ∈ B)

@[simp] theorem mem_revlexColonVariables (B : Family V) (b : Exponent V) (j : V) :
    j ∈ revlexColonVariables B b ↔
      ∃ i, j < i ∧ 0 < b i ∧ exchange b i j ∈ B := by
  simp [revlexColonVariables]

theorem exchange_revlexBefore (b : Exponent V) {i j : V}
    (hji : j < i) (hi : 0 < b i) : RevlexBefore (exchange b i j) b := by
  refine ⟨i, ?_, ?_⟩
  · simp only [exchange_apply, ite_true, if_neg (ne_of_gt hji)]
    omega
  · intro x hix
    simp [exchange_apply, ne_of_gt hix, ne_of_gt (hji.trans hix)]

/-- A preceding generator supplies a colon variable which divides its quotient
by the gcd with the current generator. -/
theorem revlex_exchange {B : Family V} (hB : ExchangeAxiom B)
    {a b : Exponent V} (ha : a ∈ B) (hb : b ∈ B) (hab : RevlexBefore a b) :
    ∃ j ∈ revlexColonVariables B b, b j < a j := by
  obtain ⟨i, hi, he⟩ := hab
  obtain ⟨j, hj, hex⟩ := hB b hb a ha i hi
  have hji : j < i := by
    rcases lt_trichotomy j i with h | rfl | h
    · exact h
    · omega
    · have := he j h
      omega
  exact ⟨j, (mem_revlexColonVariables B b j).mpr ⟨i, hji, by omega, hex⟩, hj⟩

/-- Exact divisibility criterion for the preceding generators, before passing
to polynomial ideals. -/
theorem contains_revlexBefore_add_iff {B : Family V} (hB : ExchangeAxiom B)
    {b : Exponent V} (hb : b ∈ B) (a : Exponent V) :
    Contains (revlexBeforeFamily B b) (a + b) ↔
      ∃ j ∈ revlexColonVariables B b, 0 < a j := by
  constructor
  · rintro ⟨c, hc, hca⟩
    obtain ⟨hcB, hcb⟩ := (mem_revlexBeforeFamily B c b).mp hc
    obtain ⟨j, hj, hbj⟩ := revlex_exchange hB hcB hb hcb
    refine ⟨j, hj, ?_⟩
    have hle := hca j
    simp only [Finsupp.add_apply] at hle
    omega
  · rintro ⟨j, hj, haj⟩
    obtain ⟨i, hji, hbi, hex⟩ := (mem_revlexColonVariables B b j).mp hj
    refine ⟨exchange b i j, (mem_revlexBeforeFamily B _ b).mpr
      ⟨hex, exchange_revlexBefore b hji hbi⟩, ?_⟩
    intro x
    simp only [exchange_apply, Finsupp.add_apply]
    by_cases hxj : x = j
    · subst x
      simp only [if_neg (ne_of_lt hji), ite_true]
      omega
    · simp only [if_neg hxj]
      split <;> omega

end CommAlg.Polymatroid
