module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false

/-!
# Executable elimination of rational linear inequalities

Fourier--Motzkin elimination is implemented by finite lists and rational
arithmetic. The correctness theorem quantifies over actual real solutions.
It includes inconsistent, empty, unbounded, and lower-dimensional systems;
no numerical tolerance or linear-programming oracle is used.
-/

open scoped BigOperators

namespace VolumePolynomials.RationalElimination

/-- A closed rational halfspace in a coordinate space. -/
structure Inequality (n : ℕ) where
  coefficient : Fin n → ℚ
  bound : ℚ
  deriving DecidableEq

namespace Inequality

def value {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (p.coefficient i : ℝ) * x i

def Holds {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) : Prop :=
  p.value x ≤ (p.bound : ℝ)

def tail {n : ℕ} (p : Inequality (n + 1)) : Inequality n :=
  ⟨fun i => p.coefficient i.castSucc, p.bound⟩

def last {n : ℕ} (p : Inequality (n + 1)) : ℚ := p.coefficient (Fin.last n)

/-- Eliminate the last variable between a negative and a positive coefficient.
Both original inequalities are multiplied by nonnegative rational scalars. -/
def combine {n : ℕ} (l u : Inequality (n + 1)) : Inequality n :=
  ⟨fun i => u.last * l.coefficient i.castSucc - l.last * u.coefficient i.castSucc,
    u.last * l.bound - l.last * u.bound⟩

theorem value_snoc {n : ℕ} (p : Inequality (n + 1)) (x : Fin n → ℝ) (t : ℝ) :
    p.value (Fin.snoc x t) = p.tail.value x + (p.last : ℝ) * t := by
  first
  | simp only [value, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    rfl

theorem combine_value {n : ℕ} (l u : Inequality (n + 1)) (x : Fin n → ℝ) :
    (combine l u).value x =
      (u.last : ℝ) * l.tail.value x - (l.last : ℝ) * u.tail.value x := by
  first
  | simp only [value, combine, tail, Rat.cast_sub, Rat.cast_mul, sub_mul,
      Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

theorem holds_tail_of_zero {n : ℕ} (p : Inequality (n + 1))
    (hp : p.last = 0) (x : Fin n → ℝ) (t : ℝ) :
    p.Holds (Fin.snoc x t) ↔ p.tail.Holds x := by
  first
  | simp only [Holds, value_snoc, hp, Rat.cast_zero, zero_mul, add_zero, tail]

noncomputable def lower {n : ℕ} (p : Inequality (n + 1)) (x : Fin n → ℝ) : ℝ :=
  (p.tail.value x - (p.bound : ℝ)) / (-(p.last : ℝ))

noncomputable def upper {n : ℕ} (p : Inequality (n + 1)) (x : Fin n → ℝ) : ℝ :=
  ((p.bound : ℝ) - p.tail.value x) / (p.last : ℝ)

theorem holds_snoc_of_negative {n : ℕ} (p : Inequality (n + 1))
    (hp : p.last < 0) (x : Fin n → ℝ) (t : ℝ) :
    p.Holds (Fin.snoc x t) ↔ p.lower x ≤ t := by
  first
  | have hp' : (p.last : ℝ) < 0 := by exact_mod_cast hp
    rw [Holds, value_snoc, lower, div_le_iff₀ (neg_pos.mpr hp')]
    constructor <;> intro h <;> nlinarith only [h]

theorem holds_snoc_of_positive {n : ℕ} (p : Inequality (n + 1))
    (hp : 0 < p.last) (x : Fin n → ℝ) (t : ℝ) :
    p.Holds (Fin.snoc x t) ↔ t ≤ p.upper x := by
  first
  | have hp' : 0 < (p.last : ℝ) := by exact_mod_cast hp
    rw [Holds, value_snoc, upper, le_div_iff₀ hp']
    constructor <;> intro h <;> nlinarith only [h]

theorem holds_combine_iff {n : ℕ} (l u : Inequality (n + 1))
    (hl : l.last < 0) (hu : 0 < u.last) (x : Fin n → ℝ) :
    (combine l u).Holds x ↔ l.lower x ≤ u.upper x := by
  first
  | have hl' : (l.last : ℝ) < 0 := by exact_mod_cast hl
    have hu' : 0 < (u.last : ℝ) := by exact_mod_cast hu
    rw [Holds, combine_value, lower, upper,
      div_le_div_iff₀ (neg_pos.mpr hl') hu']
    simp only [combine, Rat.cast_sub, Rat.cast_mul]
    constructor <;> intro h <;> nlinarith only [h]

end Inequality

def Satisfies {n : ℕ} (S : List (Inequality n)) (x : Fin n → ℝ) : Prop :=
  ∀ p ∈ S, p.Holds x

/-- One elimination step. This definition has no noncomputable operations. -/
def eliminate {n : ℕ} (S : List (Inequality (n + 1))) : List (Inequality n) :=
  ((S.filter fun p => p.last = 0).map Inequality.tail) ++
    (S.filter fun p => p.last < 0).flatMap (fun l =>
      (S.filter fun p => 0 < p.last).map (Inequality.combine l))

theorem mem_zeroFilter {n : ℕ} (S : List (Inequality (n + 1))) (p : Inequality (n + 1)) :
    p ∈ S.filter (fun q => q.last = 0) ↔ p ∈ S ∧ p.last = 0 := by simp

theorem mem_negativeFilter {n : ℕ} (S : List (Inequality (n + 1)))
    (p : Inequality (n + 1)) :
    p ∈ S.filter (fun q => q.last < 0) ↔ p ∈ S ∧ p.last < 0 := by simp

theorem mem_positiveFilter {n : ℕ} (S : List (Inequality (n + 1)))
    (p : Inequality (n + 1)) :
    p ∈ S.filter (fun q => 0 < q.last) ↔ p ∈ S ∧ 0 < p.last := by simp

theorem satisfies_eliminate_iff {n : ℕ} (S : List (Inequality (n + 1)))
    (x : Fin n → ℝ) :
    Satisfies (eliminate S) x ↔
      (∀ p ∈ S, p.last = 0 → p.tail.Holds x) ∧
      (∀ l ∈ S, l.last < 0 → ∀ u ∈ S, 0 < u.last → (Inequality.combine l u).Holds x) := by
  first
  | constructor
    · intro h
      constructor
      · intro p hp hzero
        apply h
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨p, (mem_zeroFilter S p).mpr ⟨hp, hzero⟩, rfl⟩
      · intro l hl hneg u hu hpos
        apply h
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨l, (mem_negativeFilter S l).mpr ⟨hl, hneg⟩,
          List.mem_map.mpr ⟨u, (mem_positiveFilter S u).mpr ⟨hu, hpos⟩, rfl⟩⟩
    · rintro ⟨hz, hp⟩ p hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨hq, hzero⟩ := (mem_zeroFilter S q).mp hq
        exact hz q hq hzero
      · obtain ⟨l, hl, hmem⟩ := List.mem_flatMap.mp hmem
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨hl, hneg⟩ := (mem_negativeFilter S l).mp hl
        obtain ⟨hu, hpos⟩ := (mem_positiveFilter S u).mp hu
        exact hp l hl hneg u hu hpos

/-- A finite family of lower and upper real bounds has a common point exactly
when every lower bound is at most every upper bound. Empty families are allowed. -/
theorem exists_between_finite_bounds (L U : Finset ℝ)
    (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : ℝ, (∀ l ∈ L, l ≤ t) ∧ ∀ u ∈ U, t ≤ u := by
  first
  | classical
    by_cases hL : L.Nonempty
    · refine ⟨L.max' hL, ?_, ?_⟩
      · intro l hl
        exact L.le_max' l hl
      · intro u hu
        exact L.max'_le hL u (fun l hl => h l hl u hu)
    · have hLe : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      by_cases hU : U.Nonempty
      · refine ⟨U.min' hU, ?_, ?_⟩
        · simp [hLe]
        · intro u hu
          exact U.min'_le u hu
      · have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
        exact ⟨0, by simp [hLe], by simp [hUe]⟩

/-- Exact Fourier--Motzkin correctness over the real numbers. -/
theorem eliminate_correct {n : ℕ} (S : List (Inequality (n + 1))) (x : Fin n → ℝ) :
    Satisfies (eliminate S) x ↔ ∃ t : ℝ, Satisfies S (Fin.snoc x t) := by
  first
  | classical
    rw [satisfies_eliminate_iff]
    constructor
    · rintro ⟨hz, hp⟩
      let L := ((S.filter fun p => p.last < 0).map (fun p => p.lower x)).toFinset
      let U := ((S.filter fun p => 0 < p.last).map (fun p => p.upper x)).toFinset
      have hlu : ∀ l ∈ L, ∀ u ∈ U, l ≤ u := by
        intro l hl u hu
        obtain ⟨p, hpS, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
        obtain ⟨q, hqS, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
        obtain ⟨hpS, hpneg⟩ := (mem_negativeFilter S p).mp hpS
        obtain ⟨hqS, hqpos⟩ := (mem_positiveFilter S q).mp hqS
        exact (Inequality.holds_combine_iff p q hpneg hqpos x).mp
          (hp p hpS hpneg q hqS hqpos)
      obtain ⟨t, htL, htU⟩ := exists_between_finite_bounds L U hlu
      refine ⟨t, fun p hpS => ?_⟩
      rcases lt_trichotomy p.last 0 with hneg | hzero | hpos
      · apply (p.holds_snoc_of_negative hneg x t).mpr
        exact htL _ (List.mem_toFinset.mpr
          (List.mem_map.mpr ⟨p, (mem_negativeFilter S p).mpr ⟨hpS, hneg⟩, rfl⟩))
      · exact (p.holds_tail_of_zero hzero x t).mpr (hz p hpS hzero)
      · apply (p.holds_snoc_of_positive hpos x t).mpr
        exact htU _ (List.mem_toFinset.mpr
          (List.mem_map.mpr ⟨p, (mem_positiveFilter S p).mpr ⟨hpS, hpos⟩, rfl⟩))
    · rintro ⟨t, ht⟩
      constructor
      · intro p hp hzero
        exact (p.holds_tail_of_zero hzero x t).mp (ht p hp)
      · intro l hl hneg u hu hpos
        apply (Inequality.holds_combine_iff l u hneg hpos x).mpr
        exact ((l.holds_snoc_of_negative hneg x t).mp (ht l hl)).trans
          ((u.holds_snoc_of_positive hpos x t).mp (ht u hu))

/-- Eliminate a prescribed suffix of variables. The number of operations is
finite for every input; exponential growth does not affect computability. -/
def eliminateSuffix (n : ℕ) : (m : ℕ) → List (Inequality (n + m)) → List (Inequality n)
  | 0, S => S
  | m + 1, S => eliminateSuffix n m (eliminate S)

theorem eliminateSuffix_correct (n m : ℕ) (S : List (Inequality (n + m)))
    (x : Fin n → ℝ) :
    Satisfies (eliminateSuffix n m S) x ↔
      ∃ w : Fin m → ℝ, Satisfies S (Fin.append x w) := by
  first
  | induction m with
    | zero =>
        simp only [eliminateSuffix]
        constructor
        · intro h
          exact ⟨Fin.elim0, by simpa using h⟩
        · rintro ⟨w, hw⟩
          have hw0 : w = Fin.elim0 := by funext i; exact Fin.elim0 i
          simpa only [hw0, Fin.append_elim0, Fin.cast_refl, Function.comp_id] using hw
    | succ m ih =>
        rw [eliminateSuffix, ih]
        constructor
        · rintro ⟨w, hw⟩
          obtain ⟨t, ht⟩ := (eliminate_correct S (Fin.append x w)).mp hw
          exact ⟨Fin.snoc w t, by simpa only [Fin.append_snoc] using ht⟩
        · rintro ⟨w, hw⟩
          refine ⟨Fin.init w, (eliminate_correct S (Fin.append x (Fin.init w))).mpr
            ⟨w (Fin.last m), ?_⟩⟩
          simpa only [← Fin.append_snoc, Fin.snoc_init_self] using hw

def eliminateAll : {n : ℕ} → List (Inequality n) → List (Inequality 0)
  | 0, S => S
  | n + 1, S => eliminateAll (eliminate S)

theorem eliminateAll_correct {n : ℕ} (S : List (Inequality n)) :
    Satisfies (eliminateAll S) Fin.elim0 ↔ ∃ x, Satisfies S x := by
  first
  | induction n with
    | zero =>
        constructor
        · intro h
          exact ⟨Fin.elim0, h⟩
        · rintro ⟨x, hx⟩
          have hx0 : x = Fin.elim0 := by funext i; exact Fin.elim0 i
          simpa only [hx0, eliminateAll] using hx
    | succ n ih =>
        rw [eliminateAll, ih]
        constructor
        · rintro ⟨x, hx⟩
          obtain ⟨t, ht⟩ := (eliminate_correct S x).mp hx
          exact ⟨Fin.snoc x t, ht⟩
        · rintro ⟨x, hx⟩
          exact ⟨Fin.init x, (eliminate_correct S (Fin.init x)).mpr
            ⟨x (Fin.last n), by simpa only [Fin.snoc_init_self] using hx⟩⟩

end VolumePolynomials.RationalElimination
