import Characterizations.TermOrders.Arbitrary
import Characterizations.GradedRevlex
import Characterizations.OrderExistence

/-! # The full arbitrary-term-order characterization -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid TermOrders
universe u
variable {V : Type u} {k : Type*} [Fintype V] [DecidableEq V] [CommSemiring k] [Nontrivial k]

theorem polymatroidal_iff_all_termOrder_linearQuotients {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) : IsPolymatroidal B ↔
      ∀ m : MonomialOrder.{u,u} V, HasLinearQuotients k B (termBefore m) := by
  constructor
  · exact fun hp m => polymatroidal_termOrder_linearQuotients hp m
  · intro h
    apply (polymatroidal_iff_universal_revlex (k := k) hB).mpr
    intro o
    have hw := witness_of_linearQuotients hB.antichain
      (termBefore_irrefl (variableGradedRevlexOrder o)) (h (variableGradedRevlexOrder o))
    apply linearQuotients_of_witness
    intro a ha b hb hab
    have hdab : a.degree = b.degree := (hB a ha).trans (hB b hb).symm
    obtain ⟨w, hwB, hwb, i, hwi, hi⟩ := hw a ha b hb
      ((variableGradedRevlexOrder_decreasing_iff o a b hdab).mpr hab)
    exact ⟨w, hwB, (variableGradedRevlexOrder_decreasing_iff o w b
      ((hB w hwB).trans (hB b hb).symm)).mp hwb, i, hwi, hi⟩

end Characterizations
