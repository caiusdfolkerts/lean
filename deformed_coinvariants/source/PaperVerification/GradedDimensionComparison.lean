module

public import PaperVerification.FermionFiniteGrading
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Passing from all homogeneous dimensions to the total dimension

The two coefficient fields may differ. Both vector spaces are actual finite
internally graded spaces; finiteness supplies their finite supports. No common
cutoff or a priori equality of the supports is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.GradedHilbert

variable {K L M N : Type*} [Field K] [Field L]
  [AddCommGroup M] [AddCommGroup N] [Module K M] [Module L N]
  [Module.Finite K M] [Module.Finite L N]

theorem finrank_le_of_piece_finrank_le
    (G : TauCeti.InternalGrading K M ℕ) (H : TauCeti.InternalGrading L N ℕ)
    (h : ∀ d, Module.finrank K (G.piece d) ≤ Module.finrank L (H.piece d)) :
    Module.finrank K M ≤ Module.finrank L N := by
  classical
  have hsupport : ∀ d, G.piece d ≠ ⊥ → H.piece d ≠ ⊥ := by
    intro d hd hz
    have hdim := h d
    rw [hz, finrank_bot] at hdim
    exact hd (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hdim))
  let e : NonzeroDegree G → NonzeroDegree H :=
    fun d => ⟨d.val, hsupport d.val d.property⟩
  have he : Function.Injective e := by
    intro d d' heq
    apply Subtype.ext
    exact congrArg (fun x : NonzeroDegree H => x.val) heq
  rw [finrank_eq_sum_nonzero_pieces G, finrank_eq_sum_nonzero_pieces H]
  exact Finset.sum_le_sum_of_injOn e he.injOn
    (Finset.subset_univ _)
    (fun d _ => h d.val)
    (fun _ _ _ => Nat.zero_le _)

end PaperVerification.GradedHilbert
