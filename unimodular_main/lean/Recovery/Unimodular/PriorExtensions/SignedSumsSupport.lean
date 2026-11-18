/- Binary coefficient cycles are exactly finite-support zero-sum cycles.
The cancellation rule is literal symmetric difference of the support sets. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsBinary
public import Mathlib.Data.Finset.SymmDiff
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators symmDiff
namespace Unimodular.SignedSums.Binary

theorem value_zero_or_one (z : F) : z = 0 ∨ z = 1 := by
  fin_cases z <;> simp

def support {E : Type*} [Fintype E] [DecidableEq E] (x : E → F) : Finset E :=
  Finset.univ.filter (fun e => x e ≠ 0)

@[simp] theorem mem_support {E : Type*} [Fintype E] [DecidableEq E]
    (x : E → F) (e : E) : e ∈ support x ↔ x e ≠ 0 := by simp [support]

/-- No arbitrary weights remain: every supported coefficient is exactly one. -/
theorem cycle_iff_support_sum {E M : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup M] [Module F M] (U : E → M) (x : E → F) :
    Cycle U x ↔ ∑ e ∈ support x, U e = 0 := by
  have he : (∑ e, x e • U e) = ∑ e ∈ support x, U e := by
    simp only [support, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    rcases value_zero_or_one (x e) with h | h <;> simp [h]
  exact Eq.to_iff (congrArg (fun v : M => v = 0) he)

theorem support_add {E : Type*} [Fintype E] [DecidableEq E] (x y : E → F) :
    support (x + y) = support x ∆ support y := by
  ext e
  rcases value_zero_or_one (x e) with hx | hx <;>
    rcases value_zero_or_one (y e) with hy | hy <;>
    simp [support, Pi.add_apply, hx, hy, Finset.mem_symmDiff, ZModModule.add_self]

/-- In the common ground-label space the matched port subsets cancel, and
only the prescribed surviving output subset remains. -/
theorem matched_support_symmDiff {T L R : Type*} [Fintype T] [Fintype L] [Fintype R]
    [DecidableEq T] [DecidableEq L] [DecidableEq R]
    (z : T → F) (x : L → F) (y : R → F) :
    support (Sum.elim z (Sum.elim x 0)) ∆ support (Sum.elim z (Sum.elim 0 y)) =
      (support (Sum.elim x y)).image (Sum.inr : L ⊕ R → T ⊕ (L ⊕ R)) := by
  rw [← support_add]
  ext e
  cases e with
  | inl t => simp [support, Pi.add_apply, ZModModule.add_self]
  | inr s =>
      cases s with
      | inl l => simp [support, Pi.add_apply, Finset.mem_image]
      | inr r => simp [support, Pi.add_apply, Finset.mem_image]

end Unimodular.SignedSums.Binary
#print axioms Unimodular.SignedSums.Binary.cycle_iff_support_sum
#print axioms Unimodular.SignedSums.Binary.support_add
#print axioms Unimodular.SignedSums.Binary.matched_support_symmDiff
