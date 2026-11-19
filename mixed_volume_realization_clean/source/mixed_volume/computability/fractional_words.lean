/- A separated rational fractional encoding of arbitrary binary words. -/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

@[expose] public section

namespace MixedVolume.FractionalWords

def digit : Bool → ℚ
  | false => 1
  | true => 2

/-- Base-four fractional digits one and two. Their separation prevents the
trailing-digit ambiguity that an unrestricted positional code would have. -/
def value : List Bool → ℚ
  | [] => 0
  | b :: w => (digit b + value w) / 4

def scale (w : List Bool) : ℚ := (1 / 4) ^ w.length

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (b : Bool) (w : List Bool) :
    value (b :: w) = (digit b + value w) / 4 := rfl
@[simp] theorem scale_nil : scale [] = 1 := by simp [scale]
@[simp] theorem scale_cons (b : Bool) (w : List Bool) :
    scale (b :: w) = scale w / 4 := by simp [scale, pow_succ, div_eq_mul_inv]

theorem scale_pos (w : List Bool) : 0 < scale w := by unfold scale; positivity
theorem scale_le_one (w : List Bool) : scale w ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem value_bounds (w : List Bool) : 0 ≤ value w ∧ value w ≤ 2 / 3 := by
  induction w with
  | nil => norm_num
  | cons b w ih =>
    cases b <;> simp only [value_cons, digit] <;> constructor <;> linarith [ih.1, ih.2]

theorem value_cons_lower (b : Bool) (w : List Bool) : 1 / 4 ≤ value (b :: w) := by
  cases b <;> simp only [value_cons, digit] <;> linarith [(value_bounds w).1]

theorem scale_append (u v : List Bool) : scale (u ++ v) = scale u * scale v := by
  simp [scale, pow_add]

theorem value_append (u v : List Bool) :
    value (u ++ v) = value u + scale u * value v := by
  induction u with
  | nil => simp
  | cons b u ih =>
    simp only [List.cons_append, value_cons, scale_cons, ih]
    ring

/-- A uniform, asymmetric separation bound valid for all finite words,
including words of unequal length and the empty word. -/
theorem separated {u v : List Bool} (huv : u ≠ v) :
    scale u / 4 ≤ |value u - value v| := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact False.elim (huv rfl)
    | cons b v =>
      simp only [scale_nil, value_nil, zero_sub, abs_neg]
      rw [abs_of_nonneg (value_bounds _).1]
      exact value_cons_lower b v
  | cons b u ih =>
    cases v with
    | nil =>
      simp only [value_nil, sub_zero, abs_of_nonneg (value_bounds _).1]
      have hs := scale_le_one (b :: u)
      have hv := value_cons_lower b u
      linarith
    | cons c v =>
      by_cases hbc : b = c
      · subst c
        have huv' : u ≠ v := by intro h; exact huv (congrArg (List.cons b) h)
        have h := ih huv'
        have he : value (b :: u) - value (b :: v) = (value u - value v) / 4 := by
          rw [value_cons, value_cons]
          ring
        rw [scale_cons, he, abs_div]
        rw [abs_of_pos (by norm_num : (0 : ℚ) < 4)]
        linarith
      · have hu := value_bounds u
        have hv := value_bounds v
        have hs := scale_le_one u
        have ha := le_abs_self (value (b :: u) - value (c :: v))
        have hb := neg_le_abs (value (b :: u) - value (c :: v))
        cases b <;> cases c <;> try contradiction
        all_goals simp only [value_cons, digit] at ha hb ⊢
        all_goals rw [scale_cons]
        all_goals linarith [hu.1, hu.2, hv.1, hv.2]

theorem value_injective : Function.Injective value := by
  intro u v h
  by_contra hne
  have hs := separated hne
  rw [h, sub_self, abs_zero] at hs
  exact (not_le_of_gt (div_pos (scale_pos u) (by norm_num))) hs

/-- The six-dimensional matrix representation will compute this exact score. -/
def score (u v : List Bool) : ℚ :=
  -(value u - value v) ^ 2 + scale u ^ 2 / 32

theorem score_pos_of_eq {u v : List Bool} (h : u = v) : 0 < score u v := by
  subst v
  simp only [score, sub_self, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_add]
  exact div_pos (sq_pos_of_pos (scale_pos u)) (by norm_num)

theorem score_neg_of_ne {u v : List Bool} (h : u ≠ v) : score u v < 0 := by
  have hg := separated h
  have hp := scale_pos u
  have hm := mul_nonneg (sub_nonneg.mpr hg) (show 0 ≤ |value u - value v| + scale u / 4 by positivity)
  have he : (|value u - value v| - scale u / 4) *
      (|value u - value v| + scale u / 4) =
      |value u - value v| ^ 2 - (scale u / 4) ^ 2 := by ring
  rw [he] at hm
  rw [sq_abs] at hm
  unfold score
  nlinarith [sq_pos_of_pos hp]

theorem score_pos_iff (u v : List Bool) : 0 < score u v ↔ u = v := by
  constructor
  · intro h
    by_contra hne
    exact (not_lt_of_ge (score_neg_of_ne hne).le) h
  · exact score_pos_of_eq

theorem score_nonneg_iff (u v : List Bool) : 0 ≤ score u v ↔ u = v := by
  constructor
  · intro h
    by_contra hne
    exact (not_lt_of_ge h) (score_neg_of_ne hne)
  · intro h
    exact (score_pos_of_eq h).le

end MixedVolume.FractionalWords
