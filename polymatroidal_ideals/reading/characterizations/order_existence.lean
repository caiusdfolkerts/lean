import Characterizations.VariableOrders
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Prod.Lex.Basic

/-! # Actual variable permutations with specified final patterns -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_order_refining (f : V → ℕ) :
    ∃ o : VariableOrder V, ∀ a b, f a < f b → o a < o b := by
  let e := Fintype.equivFin V
  let key : V → Lex (ℕ × Fin (Fintype.card V)) := fun a => toLex (f a, e a)
  have hk : Function.Injective key := by
    intro a b h
    exact e.injective (congrArg (fun z => (ofLex z).2) h)
  letI : LinearOrder V := LinearOrder.lift' key hk
  let o : V ≃o Fin (Fintype.card V) := (Fintype.orderIsoFinOfCardEq V rfl).symm
  refine ⟨o.toEquiv, ?_⟩
  intro a b hab
  apply o.strictMono
  change key a < key b
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)

theorem exists_finalPair (i j : V) (hij : i ≠ j) :
    ∃ o : VariableOrder V, FinalPair o i j := by
  let f : V → ℕ := fun h => if h = j then 2 else if h = i then 1 else 0
  obtain ⟨o, ho⟩ := exists_order_refining f
  refine ⟨o, ho i j (by simp [f, hij]), ?_⟩
  intro h hhi hhj
  apply ho
  simp [f, hhi, hhj, hij]

theorem exists_finalTriple (i q j : V) (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) :
    ∃ o : VariableOrder V, FinalTriple o i q j := by
  let f : V → ℕ := fun h => if h = j then 2 else if h = i ∨ h = q then 1 else 0
  obtain ⟨o, ho⟩ := exists_order_refining f
  refine ⟨o, ho i j (by simp [f, hij]), ho q j (by simp [f, hqj]), ?_⟩
  intro h hhi hhq hhj
  constructor <;> apply ho <;> simp [f, hhi, hhq, hhj, hij, hqj]

/-- The complete universal reverse-lexicographic characterization, stated
with actual polynomial colon ideals over every nontrivial coefficient semiring. -/
theorem polymatroidal_iff_universal_revlex {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    IsPolymatroidal B ↔ ∀ o : VariableOrder V, HasLinearQuotients k B (variableRevlex o) := by
  constructor
  · intro h o
    exact polymatroidal_variable_linearQuotients h.2 o
  · intro h
    refine ⟨⟨d, hB⟩, ?_⟩
    apply exchange_of_order_coverage (k := k) hB Set.univ
      ⟨Fintype.equivFin V, Set.mem_univ _⟩
    · intro i j hij
      obtain ⟨o, ho⟩ := exists_finalPair i j hij
      exact ⟨o, Set.mem_univ _, ho⟩
    · intro i q j hiq hij hqj
      obtain ⟨o, ho⟩ := exists_finalTriple i q j hiq hij hqj
      exact ⟨o, Set.mem_univ _, ho⟩
    · intro o ho
      exact h o

end Characterizations
