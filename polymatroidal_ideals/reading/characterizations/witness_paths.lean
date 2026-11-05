import Characterizations.Quotients

/-! # Linear-quotient witnesses connect every coordinate box -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem preceding_card_lt {B : Family V} {r : GeneratorOrder V}
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    {a b : Exponent V} (ha : a ∈ B) (hab : r a b) :
    (preceding B r a).card < (preceding B r b).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxB, hxa⟩ := (mem_preceding _ _ _ _).mp hx
    exact (mem_preceding _ _ _ _).mpr ⟨hxB, htrans hxa hab⟩
  · intro he
    have haa : a ∈ preceding B r a := he ▸ (mem_preceding _ _ _ _).mpr ⟨ha, hab⟩
    exact hirr a ((mem_preceding _ _ _ _).mp haa).2

theorem witness_le_sup {a b w : Exponent V} {i : V}
    (hwb : w - b = Finsupp.single i 1) (hai : b i < a i) : w ≤ a ⊔ b := by
  have hh := sub_single_le_add hwb
  intro x
  have hx := hh x
  by_cases hxi : x = i
  · subst x
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.sup_apply] at hx ⊢
    omega
  · simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg hxi,
      if_neg (Ne.symm hxi), Nat.add_zero, Finsupp.sup_apply] at hx ⊢
    omega

/-- A direct finite descent proof. It uses the literal colon witness and so
works without assuming the desired exchange axiom. -/
theorem boxConnected_of_witness {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a)
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a)
    (hW : QuotientWitness B r) : BoxConnected B := by
  intro C a ha haC b hb hbC
  generalize hm : (preceding B r a).card + (preceding B r b).card = m
  induction m using Nat.strong_induction_on generalizing a b with
  | h m ih =>
    by_cases he : a = b
    · subst b
      exact Relation.ReflTransGen.refl
    rcases htotal a b he with hab | hba
    · obtain ⟨w, hw, hwb, i, hwi, hai⟩ := hW a ha b hb hab
      have hwC : w ≤ C := (witness_le_sup hwi hai).trans (sup_le haC hbC)
      obtain ⟨j, hij, hbj, hew⟩ := witness_is_exchange hB hw hb hwi
      have hlt := preceding_card_lt hirr htrans hw hwb
      have hpath := ih ((preceding B r a).card + (preceding B r w).card)
        (by omega) a ha haC w hw hwC rfl
      exact hpath.tail ⟨hw, hb, hwC, hbC, (show UnitStep b w from
        ⟨j, i, hij.symm, hbj, hew⟩).symm⟩
    · obtain ⟨w, hw, hwa, i, hwi, hbi⟩ := hW b hb a ha hba
      have hwC : w ≤ C := (witness_le_sup hwi hbi).trans (sup_le hbC haC)
      obtain ⟨j, hij, haj, hew⟩ := witness_is_exchange hB hw ha hwi
      have hlt := preceding_card_lt hirr htrans hw hwa
      have hpath := ih ((preceding B r w).card + (preceding B r b).card)
        (by omega) w hw hwC b hb hbC rfl
      exact hpath.head ⟨ha, hw, haC, hwC, j, i, hij.symm, haj, hew⟩

theorem boxConnected_of_linearQuotients {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) {r : GeneratorOrder V}
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a) (hL : HasLinearQuotients k B r) :
    BoxConnected B :=
  boxConnected_of_witness hB hirr htrans htotal
    (witness_of_linearQuotients hB.antichain hirr hL)

end Characterizations
