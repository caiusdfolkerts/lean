import CommAlg.Polymatroid.Exponents

/-! # Integral polymatroid rank functions

The fields are precisely normalization, monotonicity and submodularity of an
ordinary nonnegative integer-valued function on subsets.  No exchange or
homological conclusion is included in the definition.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [DecidableEq V]

structure RankFunction (V : Type*) [DecidableEq V] where
  toFun : Finset V → ℕ
  empty : toFun ∅ = 0
  monotone : Monotone toFun
  submodular : ∀ A B, toFun (A ∪ B) + toFun (A ∩ B) ≤ toFun A + toFun B

instance : CoeFun (RankFunction V) (fun _ => Finset V → ℕ) := ⟨RankFunction.toFun⟩

@[simp] theorem RankFunction.map_empty (g : RankFunction V) : g ∅ = 0 := g.empty

def RankFunction.Active (g : RankFunction V) : Prop :=
  ∀ A, A.Nonempty → 1 ≤ g A

/-- Additive formulation of the inequality between all marginal increments. -/
def RankFunction.Dominates (u g : RankFunction V) : Prop :=
  ∀ A B, A ⊆ B → g B + u A ≤ u B + g A

theorem RankFunction.le_of_dominates {u g : RankFunction V}
    (h : u.Dominates g) (A : Finset V) : g A ≤ u A := by
  simpa using h ∅ A (empty_subset A)

theorem RankFunction.mixed_submodular {u g : RankFunction V}
    (h : u.Dominates g) (A B : Finset V) :
    g (A ∪ B) + u (A ∩ B) ≤ g A + u B := by
  have hg := g.submodular A B
  have hi := h (A ∩ B) B inter_subset_right
  omega

def RankFunction.add (g u : RankFunction V) : RankFunction V where
  toFun A := g A + u A
  empty := by simp
  monotone := fun A B h => Nat.add_le_add (g.monotone h) (u.monotone h)
  submodular A B := by
    have hg := g.submodular A B
    have hu := u.submodular A B
    omega

def RankFunction.scale (s : ℕ) (g : RankFunction V) : RankFunction V where
  toFun A := s * g A
  empty := by simp
  monotone := fun A B h => Nat.mul_le_mul_left s (g.monotone h)
  submodular A B := by
    simpa only [Nat.mul_add] using Nat.mul_le_mul_left s (g.submodular A B)

end CommAlg.Polymatroid
