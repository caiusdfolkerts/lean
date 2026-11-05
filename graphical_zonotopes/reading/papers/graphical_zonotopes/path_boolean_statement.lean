module

public import Papers.GraphicalZonotopes.PathPaperStatement

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators

/-- The indicator of a triple is the product of its three membership bits,
even if some of the displayed vertices coincide. -/
theorem setMonomial_three_membershipBits {V : Type*} [DecidableEq V]
    (a b c : V) (S : Finset V) :
    setMonomial {a,b,c} S =
      membershipBit S a * membershipBit S b * membershipBit S c := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;>
    simp [setMonomial,membershipBit,Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb,hc]

/-- The analogous exact identity for the four-vertex term. -/
theorem setMonomial_four_membershipBits {V : Type*} [DecidableEq V]
    (a b c d : V) (S : Finset V) :
    setMonomial {a,b,c,d} S =
      membershipBit S a * membershipBit S b * membershipBit S c * membershipBit S d := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    by_cases hc : c ∈ S <;> by_cases hd : d ∈ S <;>
    simp [setMonomial,membershipBit,Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb,hc,hd]

namespace Path

/-- The displayed Boolean-product formula preceding equation (3.1), with
the paper's labels 1,...,n represented by the zero-based labels of Fin n. -/
def booleanFormula (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  (∑ i : Fin (n-2), integerBit S (i.val : ℤ) *
    integerBit S ((i.val : ℤ)+1) * integerBit S ((i.val : ℤ)+2)) +
  (∑ i : Fin (n-3), integerBit S (i.val : ℤ) *
    integerBit S ((i.val : ℤ)+2) * integerBit S ((i.val : ℤ)+3)) -
  (∑ i : Fin (n-3), integerBit S (i.val : ℤ) *
    integerBit S ((i.val : ℤ)+1) * integerBit S ((i.val : ℤ)+2) *
      integerBit S ((i.val : ℤ)+3))

/-- The original coefficient construction and the paper's membership-bit
polynomial agree at every subset and every path length. -/
theorem setFunction_eq_booleanFormula (n : ℕ) : setFunction n = booleanFormula n := by
  funext S
  have h012 (i : Fin (n-2)) :
      setMonomial (window n i.val {0,1,2}) S =
        integerBit S (i.val : ℤ) * integerBit S ((i.val : ℤ)+1) *
          integerBit S ((i.val : ℤ)+2) := by
    rw [window_triple_eq
      (window_index_bound (n := n) (p := 2) i (by decide : 0 ≤ 2))
      (window_index_bound (n := n) (p := 2) i (by decide : 1 ≤ 2))
      (window_index_bound (n := n) (p := 2) i (by decide : 2 ≤ 2)),
      setMonomial_three_membershipBits]
    simp only [membershipBit_vertex,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  have h023 (i : Fin (n-3)) :
      setMonomial (window n i.val {0,2,3}) S =
        integerBit S (i.val : ℤ) * integerBit S ((i.val : ℤ)+2) *
          integerBit S ((i.val : ℤ)+3) := by
    rw [window_triple_eq
      (window_index_bound (n := n) (p := 3) i (by decide : 0 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 2 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 3 ≤ 3)),
      setMonomial_three_membershipBits]
    simp only [membershipBit_vertex,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  have h0123 (i : Fin (n-3)) :
      setMonomial (window n i.val {0,1,2,3}) S =
        integerBit S (i.val : ℤ) * integerBit S ((i.val : ℤ)+1) *
          integerBit S ((i.val : ℤ)+2) * integerBit S ((i.val : ℤ)+3) := by
    rw [window_quad_eq
      (window_index_bound (n := n) (p := 3) i (by decide : 0 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 1 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 2 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 3 ≤ 3)),
      setMonomial_four_membershipBits]
    simp only [membershipBit_vertex,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  have he := congrFun (setFunction_expansion n) S
  simpa only [Pi.add_apply,Pi.sub_apply,Finset.sum_apply,h012,h023,h0123,
    booleanFormula] using he

/-- The complete defining equations using ordinary finite sums and the
literal membership-bit polynomial. -/
theorem polytope_boolean_defining_equations {n : ℕ} (hn : 4 ≤ n) :
    polytope n = {x : Fin n → ℝ | (∑ i, x i) = (n : ℝ)-2 ∧
      ∀ S : Finset (Fin n), booleanFormula n S ≤ ∑ i ∈ S, x i} := by
  rw [polytope_defining_equations_sums hn,setFunction_eq_booleanFormula]

end Path
end GraphicalZonotopes
