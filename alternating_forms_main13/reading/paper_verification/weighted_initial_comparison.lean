module

public import PaperVerification.WeightedInitialDimension

/-!
# A prime candidate and the actual initial ideal

This is the dimension deduction used after a concrete initial containment
has been proved.  It concludes equality of ideals, not merely equality or
inequality of dimensions.  The containment is kept as an explicit intermediate
hypothesis; no paper theorem is claimed by this generic lemma alone.
-/

@[expose] public section
set_option autoImplicit false

namespace PaperVerification.WeightedInitialFiber

variable {K σ : Type*} [Field K] [Finite σ]
local notation "P" => MvPolynomial σ K

theorem initial_eq_of_prime_candidate (I C : Ideal P) [C.IsPrime]
    (w : σ → ℕ) (d : ℕ) (hcontain : C ≤ initialIdeal I w)
    (hCdim : ringKrullDim (P ⧸ C)=d) (hIdim : (d : WithBot ℕ∞)≤ringKrullDim (P ⧸ I)) :
    initialIdeal I w=C := by
  by_contra hne
  have hlt : C < initialIdeal I w := lt_of_le_of_ne hcontain (Ne.symm hne)
  have hdrop := TauCeti.ringKrullDim_quotient_add_one_le_of_lt hlt
  have hlower : (d : WithBot ℕ∞)≤ringKrullDim (P ⧸ initialIdeal I w) :=
    hIdim.trans (dimension_le_initial_dimension I w)
  rw [hCdim] at hdrop
  have hbad : (d : WithBot ℕ∞)+1≤d := (add_le_add_left hlower 1).trans hdrop
  have hn : d+1≤d := by exact_mod_cast hbad
  exact Nat.not_succ_le_self d hn

end PaperVerification.WeightedInitialFiber
