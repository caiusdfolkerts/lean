module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

/-!
# The coefficient inequalities in the binary realization theorem

The inequalities are exactly (A.1), including all separated-index
inequalities. They are equivalent to nonnegative adjacent log-concavity
with no internal zeros. In particular, no positivity assumption is silently
added in the passage to decreasing ratios.
-/

namespace VolumePolynomials.BinarySequences

def Criterion (d : ℕ) (a : ℕ → ℝ) : Prop :=
  (∀ i ≤ d, 0 ≤ a i) ∧
    ∀ i j : ℕ, 1 ≤ i → i ≤ j → j < d → a (i - 1) * a (j + 1) ≤ a i * a j

def NoInternalZeros (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ i j k : ℕ, i ≤ j → j ≤ k → k ≤ d → 0 < a i → 0 < a k → 0 < a j

theorem Criterion.adjacent {d : ℕ} {a : ℕ → ℝ} (h : Criterion d a)
    {i : ℕ} (hi : 1 ≤ i) (hid : i < d) :
    a (i - 1) * a (i + 1) ≤ a i ^ 2 := by
  first
  | simpa only [pow_two] using h.2 i i hi le_rfl hid

/-- A zero to the left of a positive coefficient forces every earlier
coefficient to vanish. This uses the separated-index inequalities. -/
theorem Criterion.zero_propagates_left {d : ℕ} {a : ℕ → ℝ}
    (h : Criterion d a) {r : ℕ} (hrd : r ≤ d) (hr : 0 < a r) :
    ∀ i : ℕ, i < r → a i = 0 → ∀ l ≤ i, a l = 0 := by
  first
  | intro i
    induction i with
    | zero =>
        intro _ hi l hl
        have hl0 : l = 0 := by omega
        simpa only [hl0] using hi
    | succ i ih =>
        intro hir hi l hl
        by_cases heq : l = i + 1
        · simpa only [heq] using hi
        · have hpred : a i = 0 := by
            first
            | have hineq := h.2 (i + 1) (r - 1) (by omega) (by omega) (by omega)
              have hrid : r - 1 + 1 = r := by omega
              simp only [Nat.add_sub_cancel, hrid, hi, zero_mul] at hineq
              have hnonneg := h.1 i (by omega)
              have hle : a i ≤ 0 := nonpos_of_mul_nonpos_left hineq hr
              exact le_antisymm hle hnonneg
          exact ih (by omega) hpred l (by omega)

theorem Criterion.noInternalZeros {d : ℕ} {a : ℕ → ℝ} (h : Criterion d a) :
    NoInternalZeros d a := by
  first
  | intro i j k hij hjk hkd hi hk
    by_contra hj
    have hj0 : a j = 0 := le_antisymm (le_of_not_gt hj) (h.1 j (hjk.trans hkd))
    have hjlt : j < k := by
      first
      | apply lt_of_le_of_ne hjk
        intro heq
        subst j
        exact hk.ne' hj0
    have hi0 := h.zero_propagates_left hkd hk j hjlt hj0 i hij
    exact hi.ne' hi0

theorem adjacent_ratio_le {a : ℕ → ℝ} {i : ℕ}
    (ha : 0 < a i) (hb : 0 < a (i + 1))
    (hlog : a i * a (i + 2) ≤ a (i + 1) ^ 2) :
    a (i + 2) / a (i + 1) ≤ a (i + 1) / a i := by
  first
  | apply (div_le_div_iff₀ hb ha).mpr
    simpa only [pow_two, mul_comm] using hlog

/-- Adjacent log-concavity orders every pair of successive ratios inside a
positive interval. -/
theorem ratios_antitone_on_interval {a : ℕ → ℝ} {l r : ℕ}
    (hpos : ∀ i : ℕ, l ≤ i → i ≤ r → 0 < a i)
    (hlog : ∀ i : ℕ, l < i → i < r → a (i - 1) * a (i + 1) ≤ a i ^ 2) :
    ∀ i j : ℕ, l ≤ i → i ≤ j → j < r →
      a (j + 1) / a j ≤ a (i + 1) / a i := by
  first
  | intro i j hli hij hjr
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
        have hstep : a (j + 2) / a (j + 1) ≤ a (j + 1) / a j := by
          first
          | apply adjacent_ratio_le (hpos j (hli.trans hij) (by omega))
              (hpos (j + 1) (by omega) (by omega))
            simpa only [Nat.add_sub_cancel] using hlog (j + 1) (by omega) (by omega)
        exact hstep.trans (ih (by omega))

theorem criterion_iff {d : ℕ} {a : ℕ → ℝ} :
    Criterion d a ↔
      (∀ i ≤ d, 0 ≤ a i) ∧
      (∀ i : ℕ, 1 ≤ i → i < d → a (i - 1) * a (i + 1) ≤ a i ^ 2) ∧
      NoInternalZeros d a := by
  first
  | constructor
    · intro h
      exact ⟨h.1, fun _ hi hid => h.adjacent hi hid, h.noInternalZeros⟩
    · rintro ⟨hn, hlog, hnozero⟩
      refine ⟨hn, ?_⟩
      intro i j hi hij hjd
      by_cases hleft : a (i - 1) = 0
      · rw [hleft, zero_mul]
        exact mul_nonneg (hn i (by omega)) (hn j (by omega))
      by_cases hright : a (j + 1) = 0
      · rw [hright, mul_zero]
        exact mul_nonneg (hn i (by omega)) (hn j (by omega))
      have hleftpos : 0 < a (i - 1) :=
        lt_of_le_of_ne (hn (i - 1) (by omega)) (Ne.symm hleft)
      have hrightpos : 0 < a (j + 1) :=
        lt_of_le_of_ne (hn (j + 1) (by omega)) (Ne.symm hright)
      have hpos : ∀ k : ℕ, i - 1 ≤ k → k ≤ j + 1 → 0 < a k :=
        fun k hik hkj => hnozero (i - 1) k (j + 1) hik hkj (by omega) hleftpos hrightpos
      have hrat := ratios_antitone_on_interval hpos
        (fun k hik hkj => hlog k (by omega) (by omega))
        (i - 1) j le_rfl (by omega) (by omega)
      have hip : i - 1 + 1 = i := by omega
      rw [hip] at hrat
      have hx := (div_le_div_iff₀ (hpos j (by omega) (by omega)) hleftpos).mp hrat
      simpa only [mul_comm] using hx

end VolumePolynomials.BinarySequences
