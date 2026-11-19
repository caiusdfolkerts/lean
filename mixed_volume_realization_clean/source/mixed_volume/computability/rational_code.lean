/- Explicit rational input codes and their exact arithmetic semantics. -/
module

public import matrix_mortality.computability
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

set_option autoImplicit false

@[expose] public section

namespace MixedVolume.RationalCode

/-- Positive numerator part, negative numerator part, and denominator minus one.
Every code denotes a rational number; the denominator is always positive. -/
abbrev Code := ℕ × ℕ × ℕ

def denominator (c : Code) : ℕ := c.2.2 + 1
def eval (c : Code) : ℚ := ((c.1 : ℚ) - c.2.1) / denominator c
def nat (n : ℕ) : Code := (n, 0, 0)
def neg (c : Code) : Code := (c.2.1, c.1, c.2.2)
def add (c d : Code) : Code :=
  (c.1 * denominator d + d.1 * denominator c,
    c.2.1 * denominator d + d.2.1 * denominator c,
    denominator c * denominator d - 1)
def mul (c d : Code) : Code :=
  (c.1 * d.1 + c.2.1 * d.2.1,
    c.1 * d.2.1 + c.2.1 * d.1,
    denominator c * denominator d - 1)
def inv (c : Code) : Code :=
  if c.1 = c.2.1 then nat 0
  else if c.2.1 ≤ c.1 then (denominator c, 0, c.1 - c.2.1 - 1)
  else (0, denominator c, c.2.1 - c.1 - 1)
def abs (c : Code) : Code := if c.2.1 ≤ c.1 then c else neg c
def sub (c d : Code) : Code := add c (neg d)
def div (c d : Code) : Code := mul c (inv d)

theorem denominator_pos (c : Code) : 0 < denominator c := Nat.succ_pos _

theorem denominator_ne_zero (c : Code) : (denominator c : ℚ) ≠ 0 := by
  exact_mod_cast (denominator_pos c).ne'

@[simp] theorem eval_nat (n : ℕ) : eval (nat n) = n := by simp [eval, nat, denominator]
@[simp] theorem eval_neg (c : Code) : eval (neg c) = -eval c := by
  simp only [eval, neg, denominator]
  ring

theorem denominator_add (c d : Code) : denominator (add c d) = denominator c * denominator d := by
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.mul_pos (denominator_pos c) (denominator_pos d))))

theorem denominator_mul (c d : Code) : denominator (mul c d) = denominator c * denominator d := by
  exact denominator_add c d

@[simp] theorem eval_add (c d : Code) : eval (add c d) = eval c + eval d := by
  rw [eval, denominator_add]
  simp only [add, Nat.cast_add, Nat.cast_mul]
  unfold eval
  field_simp [denominator_ne_zero c, denominator_ne_zero d]
  ring

@[simp] theorem eval_mul (c d : Code) : eval (mul c d) = eval c * eval d := by
  rw [eval, denominator_mul]
  simp only [mul, Nat.cast_add, Nat.cast_mul]
  unfold eval
  ring

@[simp] theorem eval_inv (c : Code) : eval (inv c) = (eval c)⁻¹ := by
  by_cases heq : c.1 = c.2.1
  · simp [inv, heq, eval, nat, denominator]
  · by_cases hle : c.2.1 ≤ c.1
    · have hp : 1 ≤ c.1 - c.2.1 := Nat.one_le_iff_ne_zero.mpr
        (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hle (Ne.symm heq)))
      simp only [inv, if_neg heq, if_pos hle, eval, denominator,
        Nat.sub_add_cancel hp, Nat.cast_sub hle, Nat.cast_zero, sub_zero, inv_div]
    · have hlt : c.1 < c.2.1 := Nat.lt_of_not_ge hle
      have hp : 1 ≤ c.2.1 - c.1 := Nat.one_le_iff_ne_zero.mpr
        (Nat.sub_ne_zero_of_lt hlt)
      simp only [inv, if_neg heq, if_neg hle, eval, denominator,
        Nat.sub_add_cancel hp, Nat.cast_sub hlt.le, Nat.cast_zero, zero_sub, inv_div]
      rw [← neg_sub, div_neg, neg_div, neg_neg]

@[simp] theorem eval_abs (c : Code) : eval (abs c) = |eval c| := by
  by_cases h : c.2.1 ≤ c.1
  · rw [abs, if_pos h, abs_of_nonneg]
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast h)) (Nat.cast_nonneg _)
  · rw [abs, if_neg h, eval_neg, abs_of_nonpos]
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h)))) (Nat.cast_nonneg _)

@[simp] theorem eval_sub (c d : Code) : eval (sub c d) = eval c - eval d := by
  simp [sub, sub_eq_add_neg]
@[simp] theorem eval_div (c d : Code) : eval (div c d) = eval c / eval d := by
  simp [div, div_eq_mul_inv]

/-- The coding convention covers every rational input, not a restricted
number field or a bounded-denominator class. -/
theorem eval_surjective : Function.Surjective eval := by
  intro q
  have hd : q.den - 1 + 1 = q.den := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr q.den_nz)
  cases hn : q.num with
  | ofNat n =>
    refine ⟨(n, 0, q.den - 1), ?_⟩
    simpa only [eval, denominator, hd, Nat.cast_zero, sub_zero, hn, Int.ofNat_eq_natCast, Int.cast_natCast]
      using q.num_div_den
  | negSucc n =>
    refine ⟨(0, n + 1, q.den - 1), ?_⟩
    simpa only [eval, denominator, hd, Nat.cast_zero, zero_sub, hn,
      Int.cast_negSucc, Nat.cast_add, Nat.cast_one] using q.num_div_den

theorem denominator_primrec : Primrec denominator :=
  Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)

theorem nat_primrec : Primrec nat :=
  Primrec.pair Primrec.id (Primrec.pair (Primrec.const 0) (Primrec.const 0))

theorem neg_primrec : Primrec neg :=
  Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))

private theorem fst_pos : Primrec (fun p : Code × Code => p.1.1) := Primrec.fst.comp Primrec.fst
private theorem fst_neg : Primrec (fun p : Code × Code => p.1.2.1) :=
  (Primrec.fst.comp Primrec.snd).comp Primrec.fst
private theorem snd_pos : Primrec (fun p : Code × Code => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem snd_neg : Primrec (fun p : Code × Code => p.2.2.1) :=
  (Primrec.fst.comp Primrec.snd).comp Primrec.snd

theorem add_primrec : Primrec₂ add := by
  apply Primrec₂.mk
  exact Primrec.pair
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp fst_pos (denominator_primrec.comp Primrec.snd))
      (Primrec.nat_mul.comp snd_pos (denominator_primrec.comp Primrec.fst)))
    (Primrec.pair
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp fst_neg (denominator_primrec.comp Primrec.snd))
        (Primrec.nat_mul.comp snd_neg (denominator_primrec.comp Primrec.fst)))
      (Primrec.nat_sub.comp
        (Primrec.nat_mul.comp (denominator_primrec.comp Primrec.fst)
          (denominator_primrec.comp Primrec.snd)) (Primrec.const 1)))

theorem mul_primrec : Primrec₂ mul := by
  apply Primrec₂.mk
  exact Primrec.pair
    (Primrec.nat_add.comp (Primrec.nat_mul.comp fst_pos snd_pos)
      (Primrec.nat_mul.comp fst_neg snd_neg))
    (Primrec.pair
      (Primrec.nat_add.comp (Primrec.nat_mul.comp fst_pos snd_neg)
        (Primrec.nat_mul.comp fst_neg snd_pos))
      (Primrec.nat_sub.comp
        (Primrec.nat_mul.comp (denominator_primrec.comp Primrec.fst)
          (denominator_primrec.comp Primrec.snd)) (Primrec.const 1)))

theorem inv_primrec : Primrec inv := by
  have hn : Primrec (fun c : Code => c.2.1) := Primrec.fst.comp Primrec.snd
  apply Primrec.ite (Primrec.eq.comp Primrec.fst hn) (Primrec.const (nat 0))
  apply Primrec.ite (Primrec.nat_le.comp hn Primrec.fst)
  · exact Primrec.pair denominator_primrec (Primrec.pair (Primrec.const 0)
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.fst hn) (Primrec.const 1)))
  · exact Primrec.pair (Primrec.const 0) (Primrec.pair denominator_primrec
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp hn Primrec.fst) (Primrec.const 1)))

theorem abs_primrec : Primrec abs :=
  Primrec.ite (Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
    Primrec.id neg_primrec

theorem sub_primrec : Primrec₂ sub :=
  Primrec₂.mk (add_primrec.comp Primrec.fst (neg_primrec.comp Primrec.snd))
theorem div_primrec : Primrec₂ div :=
  Primrec₂.mk (mul_primrec.comp Primrec.fst (inv_primrec.comp Primrec.snd))

end MixedVolume.RationalCode
