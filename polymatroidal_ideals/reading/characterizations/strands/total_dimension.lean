import Characterizations.TotalTests
import CommAlg.KoszulComplex.InternalGrading
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Total Betti sums are dimensions of the actual total-degree derived-Tor submodules -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {k : Type u} [Field k]

lemma finrank_finset_sup_of_independent {ι M : Type*} [AddCommGroup M] [Module k M]
    (P : ι → Submodule k M) [∀ a, FiniteDimensional k (P a)]
    (h : iSupIndep P) (s : Finset ι) :
    Module.finrank k ↥(s.sup P) = ∑ a ∈ s, Module.finrank k (P a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    have hd : Disjoint (P a) (s.sup P) := by
      rw [Finset.sup_eq_iSup]
      exact h.disjoint_biSup (y := (s : Set ι)) ha
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (P a) (s.sup P)
    rw [hd.eq_bot, finrank_bot, add_zero, ih] at hh
    exact hh

variable {V : Type u} [Fintype V] [LinearOrder V]

theorem totalDegreeTor_eq_finset_sup (B : Family V) (i j : ℕ) :
    totalDegreeTor (k := k) B i j =
      ((Finsupp.finite_of_degree_eq (σ := V) j).toFinset).sup
        (fun a => gradedTor (k := k) B a i) := by
  rw [Finset.sup_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact le_iSup_of_le a (le_iSup_of_le (by simpa using ha) le_rfl)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact le_iSup_of_le a (le_iSup_of_le (by simpa using ha) le_rfl)

theorem totalDegreeTor_finite (B : Family V) (i j : ℕ) :
    FiniteDimensional k (totalDegreeTor (k := k) B i j) := by
  rw [totalDegreeTor_eq_finset_sup]
  infer_instance

/-- The usual total-degree numerical Betti number, with its dimension meaning
proved from the independent internal multigrading of genuine derived Tor. -/
theorem finrank_totalDegreeTor (B : Family V) (i j : ℕ) :
    Module.finrank k (totalDegreeTor (k := k) B i j) =
      totalBettiNumber (k := k) B i j := by
  rw [totalDegreeTor_eq_finset_sup]
  exact finrank_finset_sup_of_independent (fun a => gradedTor (k := k) B a i)
    (gradedTor_independent B i) _

end Characterizations.Strands
