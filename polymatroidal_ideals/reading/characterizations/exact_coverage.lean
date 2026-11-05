import Characterizations.TripleIsolator

/-! # The exact universal coverage characterization in Theorem 5.3 -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def UniversalOrderTests (k : Type*) [CommSemiring k] (F : Set (VariableOrder V)) : Prop :=
  ∀ (B : Family V) (d : ℕ), Equigenerated B d →
    (∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) → IsPolymatroidal B

theorem exists_distinct_of_card_two (hcard : 2 ≤ Fintype.card V) : ∃ i j : V, i ≠ j := by
  let e := (Fintype.equivFin V).symm
  refine ⟨e ⟨0, by omega⟩, e ⟨1, by omega⟩, ?_⟩
  intro h
  have he := e.injective h
  exact (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val he)

/-- Both final-pattern conditions are necessary and sufficient, with the
quantification over every generator degree in the definition. -/
theorem universalOrderTests_iff_coverage {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : 4 ≤ Fintype.card V) (F : Set (VariableOrder V)) :
    UniversalOrderTests k F ↔ CoversFinalPairs F ∧ CoversFinalTriples F := by
  constructor
  · intro htest
    constructor
    · intro i j hij
      by_contra hn
      apply pairFamily_not_polymatroidal hij (by omega)
      apply htest _ _ (pairFamily_equigenerated i j)
      intro o ho
      exact pairFamily_linearQuotients_of_not_final hij o (fun hf => hn ⟨o, ho, hf⟩)
    · intro i q j hiq hij hqj
      by_contra hn
      apply tripleFamily_not_polymatroidal hiq hij hqj hcard
      apply htest _ _ (tripleFamily_equigenerated i q j)
      intro o ho
      exact tripleFamily_linearQuotients_of_not_final hiq hij hqj o (fun hf => hn ⟨o, ho, hf⟩)
  · rintro ⟨hpairs, htriples⟩ B d hB hL
    obtain ⟨i, j, hij⟩ := exists_distinct_of_card_two (V := V) (by omega)
    obtain ⟨o, ho, _⟩ := hpairs i j hij
    exact ⟨⟨d, hB⟩, exchange_of_order_coverage (k := k) hB F ⟨o, ho⟩ hpairs htriples hL⟩

end Characterizations
