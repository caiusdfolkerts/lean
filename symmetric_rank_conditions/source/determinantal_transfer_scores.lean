module
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 600000

/-!
# The score-preserving part of Bruns's determinant transfer

The score is computed from the actual list of minor sizes.  The theorem
below is Bruns, Lemma 1.5, in a presentation that separates the factors
below `t` from those at least `t`.  It does not impose a bound on the
matrix size, number of factors, minor sizes, or power exponent.

These score identities supply the numerical invariants used by the
minor-product reduction and score-to-majorization arguments.
-/

namespace FourPapers.Symmetric.DeterminantalTransfer

/-- The usual determinantal size score `γ_j`; truncated subtraction gives
zero contribution from a minor smaller than `j`. -/
def gamma (sizes : List ℕ) (j : ℕ) : ℕ :=
  (sizes.map (fun a => a + 1 - j)).sum

@[simp] theorem gamma_nil (j : ℕ) : gamma [] j = 0 := rfl

@[simp] theorem gamma_cons (a : ℕ) (L : List ℕ) (j : ℕ) :
    gamma (a :: L) j = (a + 1 - j) + gamma L j := rfl

@[simp] theorem gamma_append (L H : List ℕ) (j : ℕ) :
    gamma (L ++ H) j = gamma L j + gamma H j := by
  simp only [gamma, List.map_append, List.sum_append]

theorem gamma_eq_zero_of_le (L : List ℕ) {u j : ℕ}
    (hL : ∀ a ∈ L, a ≤ u) (hj : u < j) : gamma L j = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      have ha := hL a (by simp)
      have htail := ih (fun b hb => hL b (by simp [hb]))
      rw [gamma_cons, htail]
      omega

/-- Above a common lower bound on all minor sizes, every size contributes
the same affine change when the score threshold is shifted. -/
theorem gamma_affine_below_sizes (H : List ℕ) {t j : ℕ}
    (hH : ∀ a ∈ H, t ≤ a) (hj : j ≤ t + 1) :
    gamma H j = gamma H (t + 1) + H.length * (t + 1 - j) := by
  induction H with
  | nil => simp
  | cons a H ih =>
      have ha := hH a (by simp)
      have hi := ih (fun b hb => hH b (by simp [hb]))
      have he : a + 1 - j = (a + 1 - (t + 1)) + (t + 1 - j) := by omega
      rw [gamma_cons, gamma_cons, hi, he, List.length_cons, Nat.add_mul, one_mul]
      omega

/-- Moving one unit from a factor strictly above `t` to a largest factor
strictly below `t` preserves every lower bound defining the candidate
integral closure of `I_t^s`.  The list `L` contains the remaining smaller
factors and `H` the factors at least `t`.

The zero-size factor is permitted.  It represents the unit minor when
there is no smaller factor, as in Bruns's reduction argument. -/
theorem transfer_preserves_power_scores {u v t s : ℕ}
    (L H : List ℕ) (hu : u < t) (hv : t < v)
    (hL : ∀ a ∈ L, a ≤ u) (hH : ∀ a ∈ H, t ≤ a)
    (hscore : ∀ j, 1 ≤ j → j ≤ t →
      (t + 1 - j) * s ≤ gamma ((u :: L) ++ (v :: H)) j) :
    ∀ j, 1 ≤ j → j ≤ t →
      (t + 1 - j) * s ≤ gamma (((u + 1) :: L) ++ ((v - 1) :: H)) j := by
  intro j hj hjt
  by_cases hju : j ≤ u + 1
  · have he : gamma (((u + 1) :: L) ++ ((v - 1) :: H)) j =
        gamma ((u :: L) ++ (v :: H)) j := by
      simp only [gamma_append, gamma_cons]
      omega
    rw [he]
    exact hscore j hj hjt
  · have htransfer : gamma (((u + 1) :: L) ++ ((v - 1) :: H)) j + 1 =
        gamma ((u :: L) ++ (v :: H)) j := by
      simp only [gamma_append, gamma_cons]
      omega
    have hold := hscore j hj hjt
    by_contra hnew
    have htight : gamma ((u :: L) ++ (v :: H)) j = (t + 1 - j) * s := by
      omega
    have hsmall : ∀ a ∈ u :: L, a ≤ u := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact le_rfl
      · exact hL a ha
    have hlarge : ∀ a ∈ v :: H, t ≤ a := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hv.le
      · exact hH a ha
    let E := gamma (v :: H) (t + 1)
    let N := (v :: H).length
    let q := t + 1 - j
    have hE : 0 < E := by
      dsimp only [E]
      rw [gamma_cons]
      omega
    have hq : 0 < q := by dsimp only [q]; omega
    have hnow : gamma ((u :: L) ++ (v :: H)) j = E + N * q := by
      rw [gamma_append, gamma_eq_zero_of_le _ hsmall (by omega), zero_add]
      exact gamma_affine_below_sizes _ hlarge (by omega)
    have hprev : gamma ((u :: L) ++ (v :: H)) (j - 1) = E + N * (q + 1) := by
      rw [gamma_append, gamma_eq_zero_of_le _ hsmall (by omega), zero_add]
      rw [gamma_affine_below_sizes _ hlarge (by omega)]
      have hqprev : t + 1 - (j - 1) = q + 1 := by dsimp only [q]; omega
      rw [hqprev]
    have hp := hscore (j - 1) (by omega) (by omega)
    rw [hprev] at hp
    have hqprev : t + 1 - (j - 1) = q + 1 := by dsimp only [q]; omega
    rw [hqprev] at hp
    rw [hnow] at htight
    change E + N * q = q * s at htight
    have hN : s ≤ N := by nlinarith
    have hmul := Nat.mul_le_mul_left q hN
    nlinarith

/-- Repetition of a literal product scales all size scores exactly.  This
is the arithmetic input when clearing denominators in a rational convex
combination of determinantal product shapes. -/
theorem gamma_repeat_flatten (L : List ℕ) (q j : ℕ) :
    gamma ((List.replicate q L).flatten) j = q * gamma L j := by
  induction q with
  | zero => simp
  | succ q ih =>
      simp only [List.replicate_succ, List.flatten_cons, gamma_append, ih,
        Nat.add_mul, one_mul]
      omega

end FourPapers.Symmetric.DeterminantalTransfer

#print axioms FourPapers.Symmetric.DeterminantalTransfer.transfer_preserves_power_scores
