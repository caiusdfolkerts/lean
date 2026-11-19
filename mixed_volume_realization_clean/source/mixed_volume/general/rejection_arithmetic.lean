module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.List.OfFn
public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp
public import volume_polynomials.mixed_volume_basis
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.List.Sublists
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Tactic.GCongr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Standby source partition. Generation is not a proof certificate.
Exact copied proof ranges are recorded in the adjacent manifest. -/

/- BEGIN SOURCE: VolumePolynomials/RationalElimination.lean -/
section


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
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/RationalElimination.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalPolytopeRepresentation.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Exact computable halfspaces for a finite rational convex hull

The algorithm writes the usual barycentric inequalities and eliminates the
barycentric variables with the proved rational Fourier--Motzkin algorithm.
Thus the output is a finite list of rational halfspaces whose real solution
set is exactly the convex hull, including empty and lower-dimensional hulls.
-/

open Set
open scoped BigOperators

namespace VolumePolynomials.RationalElimination

theorem convexHull_range_finiteWeights {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (v : ι → E) :
    convexHull ℝ (range v) =
      {x | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∑ i, w i • v i = x} := by
  first
  | classical
    apply Set.Subset.antisymm
    · apply convexHull_min
      · rintro x ⟨i, rfl⟩
        refine ⟨fun j => if j = i then 1 else 0, ?_, ?_, ?_⟩
        · intro j
          change 0 ≤ if j = i then (1 : ℝ) else 0
          split_ifs <;> norm_num
        · simp
        · simp
      · rintro x ⟨w, hw, hw1, rfl⟩ y ⟨z, hz, hz1, rfl⟩ a b ha hb hab
        refine ⟨fun i => a * w i + b * z i, ?_, ?_, ?_⟩
        · intro i
          exact add_nonneg (mul_nonneg ha (hw i)) (mul_nonneg hb (hz i))
        · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw1, hz1, mul_one, hab]
        · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    · rintro x ⟨w, hw, hw1, hwx⟩
      exact mem_convexHull_of_exists_fintype w v hw hw1 (fun i => mem_range_self i) hwx

def negative {n : ℕ} (p : Inequality n) : Inequality n :=
  ⟨fun i => -p.coefficient i, -p.bound⟩

theorem negative_value {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) :
    (negative p).value x = -p.value x := by
  first
  | simp [negative, Inequality.value, Finset.sum_neg_distrib]

def equality {n : ℕ} (a : Fin n → ℚ) (b : ℚ) : List (Inequality n) :=
  [⟨a, b⟩, negative ⟨a, b⟩]

theorem satisfies_equality {n : ℕ} (a : Fin n → ℚ) (b : ℚ) (x : Fin n → ℝ) :
    Satisfies (equality a b) x ↔ (∑ i, (a i : ℝ) * x i) = (b : ℝ) := by
  first
  | constructor
    · intro h
      have hu : (∑ i, (a i : ℝ) * x i) ≤ (b : ℝ) :=
        h (Inequality.mk a b) (by simp [equality])
      have hl := h (negative (Inequality.mk a b)) (by simp [equality])
      change (negative (Inequality.mk a b)).value x ≤
        ((negative (Inequality.mk a b)).bound : ℝ) at hl
      rw [negative_value] at hl
      have hl' : -(∑ i, (a i : ℝ) * x i) ≤ -(b : ℝ) := by
        simpa only [negative, Inequality.value, Rat.cast_neg] using hl
      exact le_antisymm hu (neg_le_neg_iff.mp hl')
    · intro h p hp
      have hp' : p = Inequality.mk a b ∨ p = negative (Inequality.mk a b) := by
        simpa [equality] using hp
      rcases hp' with rfl | rfl
      · exact h.le
      · change (negative (Inequality.mk a b)).value x ≤
          ((negative (Inequality.mk a b)).bound : ℝ)
        rw [negative_value]
        simpa only [negative, Inequality.value, Rat.cast_neg] using neg_le_neg h.ge

theorem satisfies_append {n : ℕ} (A B : List (Inequality n)) (x : Fin n → ℝ) :
    Satisfies (A ++ B) x ↔ Satisfies A x ∧ Satisfies B x := by
  first
  | constructor
    · intro h
      exact ⟨fun p hp => h p (List.mem_append.mpr (Or.inl hp)),
        fun p hp => h p (List.mem_append.mpr (Or.inr hp))⟩
    · rintro ⟨hA, hB⟩ p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hA p hp
      · exact hB p hp

theorem satisfies_ofFn {n m : ℕ} (p : Fin m → Inequality n) (x : Fin n → ℝ) :
    Satisfies (List.ofFn p) x ↔ ∀ j, (p j).Holds x := by
  first
  | simp [Satisfies, List.mem_ofFn]

theorem satisfies_flatten_ofFn {n m : ℕ} (p : Fin m → List (Inequality n))
    (x : Fin n → ℝ) :
    Satisfies (List.ofFn p).flatten x ↔ ∀ j, Satisfies (p j) x := by
  first
  | constructor
    · intro h j q hq
      exact h q (List.mem_flatten.mpr ⟨p j, List.mem_ofFn.mpr ⟨j, rfl⟩, hq⟩)
    · intro h q hq
      obtain ⟨L, hL, hqL⟩ := List.mem_flatten.mp hq
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
      exact h j q hqL

theorem value_append {n m : ℕ} (a : Fin n → ℚ) (b : Fin m → ℚ)
    (c : ℚ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    (Inequality.mk (Fin.append a b) c).value (Fin.append x w) =
      (∑ i, (a i : ℝ) * x i) + ∑ j, (b j : ℝ) * w j := by
  first
  | rw [Inequality.value, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

def nonnegativeConstraint (n : ℕ) {m : ℕ} (j : Fin m) : Inequality (n + m) :=
  ⟨Fin.append (fun _ => 0) (fun k => if k = j then -1 else 0), 0⟩

theorem nonnegativeConstraint_holds (n : ℕ) {m : ℕ} (j : Fin m)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    (nonnegativeConstraint n j).Holds (Fin.append x w) ↔ 0 ≤ w j := by
  first
  | simp only [Inequality.Holds, nonnegativeConstraint, value_append]
    simp [apply_ite, ite_mul]

def barycentricSystem {n m : ℕ} (v : Fin m → Fin n → ℚ) : List (Inequality (n + m)) :=
  List.ofFn (nonnegativeConstraint n) ++
    equality (Fin.append (fun _ : Fin n => 0) (fun _ : Fin m => 1)) 1 ++
    (List.ofFn fun i : Fin n =>
      equality (Fin.append (fun k => if k = i then 1 else 0) (fun j => -v j i)) 0).flatten

theorem barycentricSystem_correct {n m : ℕ} (v : Fin m → Fin n → ℚ)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    Satisfies (barycentricSystem v) (Fin.append x w) ↔
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
        ∑ j, w j • (fun i => (v j i : ℝ)) = x := by
  first
  | rw [barycentricSystem, satisfies_append, satisfies_append, satisfies_ofFn,
      satisfies_equality, satisfies_flatten_ofFn]
    simp only [nonnegativeConstraint_holds]
    have hsum : (∑ k : Fin (n + m),
        ((Fin.append (fun _ : Fin n => (0 : ℚ)) (fun _ : Fin m => 1)) k : ℝ) *
          Fin.append x w k) = ∑ j, w j := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Rat.cast_zero, Rat.cast_one,
        zero_mul, one_mul, Finset.sum_const_zero, zero_add]
    rw [hsum]
    have hcoord : (∀ i : Fin n,
        Satisfies (equality (Fin.append (fun k => if k = i then 1 else 0)
          (fun j => -v j i)) 0) (Fin.append x w)) ↔
        ∑ j, w j • (fun i => (v j i : ℝ)) = x := by
      simp only [satisfies_equality]
      have heval : ∀ i : Fin n,
          (∑ k : Fin (n + m),
            ((Fin.append (fun k => if k = i then (1 : ℚ) else 0) (fun j => -v j i)) k : ℝ) *
              Fin.append x w k) = x i - ∑ j, (v j i : ℝ) * w j := by
        intro i
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right, apply_ite, ite_mul,
          Finset.sum_neg_distrib, sub_eq_add_neg]
      simp only [heval, Rat.cast_zero, sub_eq_zero]
      constructor
      · intro h
        funext i
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using (h i).symm
      · intro h i
        have hi := congrFun h i
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hi.symm
    rw [hcoord]
    simp only [Rat.cast_one, and_assoc]

/-- A finite executable rational halfspace representation of the hull. -/
def hullHalfspaces {n m : ℕ} (v : Fin m → Fin n → ℚ) : List (Inequality n) :=
  eliminateSuffix n m (barycentricSystem v)

/-- The computed halfspaces describe the literal real convex hull. -/
theorem hullHalfspaces_correct {n m : ℕ} (v : Fin m → Fin n → ℚ) (x : Fin n → ℝ) :
    Satisfies (hullHalfspaces v) x ↔
      x ∈ convexHull ℝ (range (fun j => fun i => (v j i : ℝ))) := by
  first
  | rw [hullHalfspaces, eliminateSuffix_correct, convexHull_range_finiteWeights]
    simp only [Set.mem_setOf_eq, barycentricSystem_correct]

end VolumePolynomials.RationalElimination
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/RationalPolytopeRepresentation.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalBoxVolume.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Certified rational volume approximation

Closed rational halfspaces are tested on the extremal vertices of rational
grid boxes. The inner and outer counts are rational bounds on actual Lebesgue
volume. Their difference tends to zero, including for empty or degenerate
polytopes, because a convex set has null frontier. Searching the decidable
rational gap test therefore gives a terminating executable approximation.
-/

open Set Filter Metric MeasureTheory
open scoped BigOperators Topology

namespace VolumePolynomials.RationalElimination

namespace Inequality

def rationalValue {n : ℕ} (p : Inequality n) (x : Fin n → ℚ) : ℚ :=
  ∑ i, p.coefficient i * x i

theorem value_cast {n : ℕ} (p : Inequality n) (x : Fin n → ℚ) :
    p.value (fun i => (x i : ℝ)) = (p.rationalValue x : ℝ) := by
  first
  | simp [value, rationalValue]

theorem continuous_value {n : ℕ} (p : Inequality n) : Continuous p.value := by
  first
  | change Continuous (fun x : Fin n → ℝ => ∑ i, (p.coefficient i : ℝ) * x i)
    fun_prop

def upperCorner {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) : Fin n → ℚ :=
  fun i => if 0 ≤ p.coefficient i then ((ν i : ℚ) + 1) / (k + 1) else (ν i : ℚ) / (k + 1)

def lowerCorner {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) : Fin n → ℚ :=
  (negative p).upperCorner k ν

end Inequality

noncomputable abbrev cell {n : ℕ} (k : ℕ) (ν : Fin n → ℤ) : BoxIntegral.Box (Fin n) :=
  BoxIntegral.unitPartition.box (k + 1) ν

noncomputable def ambientBox (n R : ℕ) : BoxIntegral.Box (Fin n) :=
  ⟨fun _ => -((R : ℝ) + 1), fun _ => (R : ℝ) + 1,
    fun _ => by linarith [Nat.cast_nonneg (α := ℝ) R]⟩

theorem ambientBox_integral (n R : ℕ) : BoxIntegral.hasIntegralVertices (ambientBox n R) := by
  first
  | exact ⟨fun _ => -((R : ℤ) + 1), fun _ => (R : ℤ) + 1,
      fun _ => by simp [ambientBox], fun _ => by simp [ambientBox]⟩

/-- The explicit finite integer index set; no real-set membership is computed. -/
def gridIndices (n R k : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Ico (-((R : ℤ) + 1) * ((k : ℤ) + 1))
    (((R : ℤ) + 1) * ((k : ℤ) + 1)))

theorem mem_gridIndices_iff {n R k : ℕ} (ν : Fin n → ℤ) :
    ν ∈ gridIndices n R k ↔ cell k ν ≤ ambientBox n R := by
  first
  | have hk : 0 < (k : ℝ) + 1 := by positivity
    rw [gridIndices, Fintype.mem_piFinset, BoxIntegral.Box.le_iff_bounds]
    simp only [Finset.mem_Ico, Pi.le_def, ambientBox, cell,
      BoxIntegral.unitPartition.box_lower, BoxIntegral.unitPartition.box_upper, Nat.cast_add,
      Nat.cast_one]
    constructor
    · intro h
      constructor
      · intro i
        apply (le_div_iff₀ hk).mpr
        exact_mod_cast (h i).1
      · intro i
        apply (div_le_iff₀ hk).mpr
        exact_mod_cast (Int.add_one_le_iff.mpr (h i).2)
    · rintro ⟨hl, hu⟩ i
      constructor
      · exact_mod_cast (le_div_iff₀ hk).mp (hl i)
      · apply Int.add_one_le_iff.mp
        exact_mod_cast (div_le_iff₀ hk).mp (hu i)

theorem index_mem_gridIndices {n R k : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ ambientBox n R) :
    BoxIntegral.unitPartition.index (k + 1) x ∈ gridIndices n R k := by
  first
  | rw [mem_gridIndices_iff]
    exact BoxIntegral.unitPartition.mem_admissibleIndex_iff.mp
      (BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box (k + 1)
        (ambientBox_integral n R) hx)

theorem upperCorner_mem {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) :
    (fun i => (p.upperCorner k ν i : ℝ)) ∈ BoxIntegral.Box.Icc (cell k ν) := by
  first
  | have hk : 0 < (k : ℝ) + 1 := by positivity
    rw [BoxIntegral.Box.Icc_eq_pi]
    intro i _
    simp only [Inequality.upperCorner, cell, BoxIntegral.unitPartition.box_lower,
      BoxIntegral.unitPartition.box_upper, Set.mem_Icc, Nat.cast_add, Nat.cast_one]
    split_ifs <;> push_cast <;> constructor <;> first | rfl | gcongr <;> linarith

theorem lowerCorner_mem {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) :
    (fun i => (p.lowerCorner k ν i : ℝ)) ∈ BoxIntegral.Box.Icc (cell k ν) :=
  upperCorner_mem (negative p) k ν

theorem value_le_upperCorner {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ BoxIntegral.Box.Icc (cell k ν)) :
    p.value x ≤ (p.rationalValue (p.upperCorner k ν) : ℝ) := by
  first
  | rw [← p.value_cast]
    apply Finset.sum_le_sum
    intro i hi
    have hxi : (cell k ν).lower i ≤ x i ∧ x i ≤ (cell k ν).upper i :=
      ⟨hx.1 i, hx.2 i⟩
    by_cases ha : 0 ≤ p.coefficient i
    · have ha' : 0 ≤ (p.coefficient i : ℝ) := by exact_mod_cast ha
      simpa only [Inequality.upperCorner, if_pos ha, Rat.cast_div, Rat.cast_add,
        Rat.cast_intCast, Rat.cast_natCast, Rat.cast_one, cell,
        BoxIntegral.unitPartition.box_upper, Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonneg_left hxi.2 ha'
    · have ha' : (p.coefficient i : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge ha))
      simpa only [Inequality.upperCorner, if_neg ha, Rat.cast_div, Rat.cast_intCast,
        Rat.cast_natCast, Rat.cast_add, Rat.cast_one, cell,
        BoxIntegral.unitPartition.box_lower, Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonpos_left hxi.1 ha'

theorem lowerCorner_le_value {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ BoxIntegral.Box.Icc (cell k ν)) :
    (p.rationalValue (p.lowerCorner k ν) : ℝ) ≤ p.value x := by
  first
  | have h := value_le_upperCorner (negative p) k ν hx
    rw [← Inequality.value_cast, negative_value, negative_value] at h
    rw [← p.value_cast]
    exact neg_le_neg_iff.mp h

def solutionSet {n : ℕ} (S : List (Inequality n)) : Set (Fin n → ℝ) :=
  {x | Satisfies S x}

theorem isClosed_solutionSet {n : ℕ} (S : List (Inequality n)) :
    IsClosed (solutionSet S) := by
  first
  | have heq : solutionSet S =
        ⋂ p : Inequality n, ⋂ (_ : p ∈ S), {x | p.value x ≤ (p.bound : ℝ)} := by
      first
      | ext x
        simp only [solutionSet, Set.mem_setOf_eq, Satisfies, Inequality.Holds, Set.mem_iInter]
    rw [heq]
    exact isClosed_iInter fun p => isClosed_iInter fun _ : p ∈ S =>
      isClosed_le p.continuous_value (continuous_const : Continuous (fun _ : Fin n → ℝ => (p.bound : ℝ)))

theorem convex_solutionSet {n : ℕ} (S : List (Inequality n)) :
    Convex ℝ (solutionSet S) := by
  first
  | intro x hx y hy a b ha hb hab p hp
    have hpX := hx p hp
    have hpY := hy p hp
    have heq : p.value (a • x + b • y) = a * p.value x + b * p.value y := by
      first
      | simp only [Inequality.value, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    change p.value (a • x + b • y) ≤ (p.bound : ℝ)
    rw [heq]
    calc
      _ ≤ a * (p.bound : ℝ) + b * (p.bound : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hpX ha) (mul_le_mul_of_nonneg_left hpY hb)
      _ = (p.bound : ℝ) := by rw [← add_mul, hab, one_mul]

def innerTest {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) : Prop :=
  ∀ p ∈ S, p.rationalValue (p.upperCorner k ν) ≤ p.bound

def outerTest {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) : Prop :=
  ∀ p ∈ S, p.rationalValue (p.lowerCorner k ν) ≤ p.bound

instance innerTest_decidable {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) :
    Decidable (innerTest S k ν) := by unfold innerTest; infer_instance

instance outerTest_decidable {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) :
    Decidable (outerTest S k ν) := by unfold outerTest; infer_instance

theorem innerTest_iff {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) :
    innerTest S k ν ↔ BoxIntegral.Box.Icc (cell k ν) ⊆ solutionSet S := by
  first
  | constructor
    · intro h x hx p hp
      apply (value_le_upperCorner p k ν hx).trans
      exact_mod_cast h p hp
    · intro h p hp
      have hv := h (upperCorner_mem p k ν) p hp
      rw [Inequality.Holds, Inequality.value_cast] at hv
      exact_mod_cast hv

theorem outerTest_of_mem {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ BoxIntegral.Box.Icc (cell k ν)) (hs : x ∈ solutionSet S) :
    outerTest S k ν := by
  first
  | intro p hp
    have h := (lowerCorner_le_value p k ν hx).trans (hs p hp)
    exact_mod_cast h

def innerIndices {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : Finset (Fin n → ℤ) :=
  (gridIndices n R k).filter (innerTest S k)

def outerIndices {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : Finset (Fin n → ℤ) :=
  (gridIndices n R k).filter (outerTest S k)

noncomputable def gridUnion {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) : Set (Fin n → ℝ) :=
  ⋃ ν ∈ A, (cell k ν : Set (Fin n → ℝ))

theorem measurableSet_gridUnion {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) :
    MeasurableSet (gridUnion k A) := by
  first
  | exact Finset.measurableSet_biUnion A (fun ν _ => (cell k ν).measurableSet_coe)

theorem mem_gridUnion_iff {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) (x : Fin n → ℝ) :
    x ∈ gridUnion k A ↔ BoxIntegral.unitPartition.index (k + 1) x ∈ A := by
  first
  | simp only [gridUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨ν, hν, hx⟩
      have heq := BoxIntegral.unitPartition.mem_box_iff_index.mp hx
      rw [heq]
      exact hν
    · intro h
      exact ⟨_, h, BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl⟩

theorem gridUnion_subset_ambient {n R k : ℕ} {A : Finset (Fin n → ℤ)}
    (hA : A ⊆ gridIndices n R k) : gridUnion k A ⊆ ambientBox n R := by
  first
  | intro x hx
    simp only [gridUnion, Set.mem_iUnion] at hx
    obtain ⟨ν, hν, hx⟩ := hx
    exact (mem_gridIndices_iff ν).mp (hA hν) hx

theorem volume_gridUnion {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) :
    volume.real (gridUnion k A) = (A.card : ℝ) / ((k : ℝ) + 1) ^ n := by
  first
  | rw [gridUnion, measureReal_biUnion_finset
      (h := fun ν _ ↦ (cell k ν).isBounded.measure_lt_top.ne)]
    · simp [measureReal_def, cell, BoxIntegral.unitPartition.volume_box,
        div_eq_mul_inv, ENNReal.toReal_add]
    · intro ν hν ν' hν' hne
      exact BoxIntegral.unitPartition.disjoint.mp hne
    · intro ν hν
      exact (cell k ν).measurableSet_coe

def lowerVolume {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : ℚ :=
  ((innerIndices S R k).card : ℚ) / ((k : ℚ) + 1) ^ n

def upperVolume {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : ℚ :=
  ((outerIndices S R k).card : ℚ) / ((k : ℚ) + 1) ^ n

theorem lowerVolume_eq {n : ℕ} (S : List (Inequality n)) (R k : ℕ) :
    (lowerVolume S R k : ℝ) = volume.real (gridUnion k (innerIndices S R k)) := by
  first
  | rw [volume_gridUnion]
    simp [lowerVolume]

theorem upperVolume_eq {n : ℕ} (S : List (Inequality n)) (R k : ℕ) :
    (upperVolume S R k : ℝ) = volume.real (gridUnion k (outerIndices S R k)) := by
  first
  | rw [volume_gridUnion]
    simp [upperVolume]

theorem innerUnion_subset {n : ℕ} (S : List (Inequality n)) (R k : ℕ) :
    gridUnion k (innerIndices S R k) ⊆ solutionSet S := by
  first
  | intro x hx
    simp only [gridUnion, Set.mem_iUnion] at hx
    obtain ⟨ν, hν, hx⟩ := hx
    exact (innerTest_iff S k ν).mp (Finset.mem_filter.mp hν).2
      (BoxIntegral.Box.coe_subset_Icc hx)

theorem subset_outerUnion {n : ℕ} (S : List (Inequality n)) (R k : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) :
    solutionSet S ⊆ gridUnion k (outerIndices S R k) := by
  first
  | intro x hx
    rw [mem_gridUnion_iff]
    exact Finset.mem_filter.mpr ⟨index_mem_gridIndices (hbound hx),
      outerTest_of_mem S k _ (BoxIntegral.Box.coe_subset_Icc
        (BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl)) hx⟩

theorem volume_bounds {n : ℕ} (S : List (Inequality n)) (R k : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) :
    (lowerVolume S R k : ℝ) ≤ volume.real (solutionSet S) ∧
      volume.real (solutionSet S) ≤ (upperVolume S R k : ℝ) := by
  first
  | rw [lowerVolume_eq, upperVolume_eq]
    constructor
    · exact measureReal_mono (innerUnion_subset S R k)
        ((ambientBox n R).isBounded.subset hbound).measure_lt_top.ne
    · exact measureReal_mono (subset_outerUnion S R k hbound)
        ((ambientBox n R).isBounded.subset
          (gridUnion_subset_ambient (Finset.filter_subset _ _))).measure_lt_top.ne

theorem eventually_mem_innerUnion {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) {x : Fin n → ℝ}
    (hx : x ∈ interior (solutionSet S)) :
    ∀ᶠ k in atTop, x ∈ gridUnion k (innerIndices S R k) := by
  first
  | obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    have hevent := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hε)
    filter_upwards [hevent] with k hk
    rw [mem_gridUnion_iff]
    refine Finset.mem_filter.mpr ⟨index_mem_gridIndices (hbound (interior_subset hx)), ?_⟩
    rw [innerTest_iff]
    intro y hy
    apply interior_subset (hball ?_)
    apply (dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc _) hy
      (BoxIntegral.Box.coe_subset_Icc
        (BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl))).trans_lt
    exact (BoxIntegral.unitPartition.diam_boxIcc (k + 1) _).trans_lt (by simpa using hk)

theorem lowerCorner_index_tendsto {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) :
    Tendsto (fun k => fun i =>
      (p.lowerCorner k (BoxIntegral.unitPartition.index (k + 1) x) i : ℝ)) atTop (𝓝 x) := by
  first
  | apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε))
    refine ⟨N, fun k hk => ?_⟩
    apply (dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc _) (lowerCorner_mem p k _)
      (BoxIntegral.Box.coe_subset_Icc
        (BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl))).trans_lt
    exact (BoxIntegral.unitPartition.diam_boxIcc (k + 1) _).trans_lt (by simpa using hN k hk)

theorem eventually_notMem_outerUnion {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    {x : Fin n → ℝ} (hx : x ∉ solutionSet S) :
    ∀ᶠ k in atTop, x ∉ gridUnion k (outerIndices S R k) := by
  first
  | obtain ⟨p, hp, hpx⟩ : ∃ p ∈ S, (p.bound : ℝ) < p.value x := by
      first
      | simpa only [solutionSet, Set.mem_setOf_eq, Satisfies, Inequality.Holds,
          not_forall, not_le, exists_prop] using hx
    have hevent := (p.continuous_value.tendsto x |>.comp (lowerCorner_index_tendsto p x)).eventually
      (lt_mem_nhds hpx)
    filter_upwards [hevent] with k hk hxk
    rw [mem_gridUnion_iff] at hxk
    have htest := (Finset.mem_filter.mp hxk).2 p hp
    dsimp only [Function.comp_def] at hk
    rw [Inequality.value_cast] at hk
    exact (not_lt_of_ge (by exact_mod_cast htest)) hk

theorem tendsto_volume_bounds {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) :
    Tendsto (fun k => (lowerVolume S R k : ℝ)) atTop (𝓝 (volume.real (solutionSet S))) ∧
    Tendsto (fun k => (upperVolume S R k : ℝ)) atTop (𝓝 (volume.real (solutionSet S))) := by
  first
  | have hfinite : volume (solutionSet S) ≠ ⊤ :=
      ((ambientBox n R).isBounded.subset hbound).measure_lt_top.ne
    have hnull := (convex_solutionSet S).addHaar_frontier volume
    have hae : ∀ᵐ x ∂volume, x ∉ frontier (solutionSet S) :=
      measure_eq_zero_iff_ae_notMem.mp hnull
    have hinner : Tendsto (fun k => volume (gridUnion k (innerIndices S R k)))
        atTop (𝓝 (volume (solutionSet S))) := by
      first
      | apply tendsto_measure_of_ae_tendsto_indicator atTop (isClosed_solutionSet S).measurableSet
          (fun k => measurableSet_gridUnion k _) (ambientBox n R).measurableSet_coe
          (ambientBox n R).isBounded.measure_lt_top.ne
        · exact Eventually.of_forall (fun k => gridUnion_subset_ambient (Finset.filter_subset _ _))
        · filter_upwards [hae] with x hx
          by_cases hxS : x ∈ solutionSet S
          · have hxi := (mem_interior_iff_notMem_frontier hxS).mpr hx
            filter_upwards [eventually_mem_innerUnion S R hbound hxi] with k hk
            exact iff_of_true hk hxS
          · exact Eventually.of_forall (fun k => iff_of_false
              (fun h => hxS (innerUnion_subset S R k h)) hxS)
    have houter : Tendsto (fun k => volume (gridUnion k (outerIndices S R k)))
        atTop (𝓝 (volume (solutionSet S))) := by
      first
      | apply tendsto_measure_of_ae_tendsto_indicator atTop (isClosed_solutionSet S).measurableSet
          (fun k => measurableSet_gridUnion k _) (ambientBox n R).measurableSet_coe
          (ambientBox n R).isBounded.measure_lt_top.ne
        · exact Eventually.of_forall (fun k => gridUnion_subset_ambient (Finset.filter_subset _ _))
        · filter_upwards [hae] with x hx
          by_cases hxS : x ∈ solutionSet S
          · exact Eventually.of_forall (fun k => iff_of_true (subset_outerUnion S R k hbound hxS) hxS)
          · filter_upwards [eventually_notMem_outerUnion S R hxS] with k hk
            exact iff_of_false hk hxS
    constructor
    · simpa only [Function.comp_def, lowerVolume_eq, measureReal_def] using
        (ENNReal.tendsto_toReal hfinite).comp hinner
    · simpa only [Function.comp_def, upperVolume_eq, measureReal_def] using
        (ENNReal.tendsto_toReal hfinite).comp houter

theorem exists_gap_lt {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) (ε : ℚ) (hε : 0 < ε) :
    ∃ k, upperVolume S R k - lowerVolume S R k < ε := by
  first
  | have he : 0 < (ε : ℝ) := by exact_mod_cast hε
    have h := (tendsto_volume_bounds S R hbound).2.sub (tendsto_volume_bounds S R hbound).1
    rw [sub_self] at h
    obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds he)).exists
    exact ⟨k, by exact_mod_cast hk⟩

/-- A terminating rational-arithmetic search, using only the proved existence
of an accepted index as its termination certificate. -/
def approximateVolume {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) (ε : ℚ) (hε : 0 < ε) : ℚ :=
  lowerVolume S R (Nat.find (exists_gap_lt S R hbound ε hε))

theorem approximateVolume_correct {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) (ε : ℚ) (hε : 0 < ε) :
    |(approximateVolume S R hbound ε hε : ℝ) - volume.real (solutionSet S)| < (ε : ℝ) := by
  first
  | let k := Nat.find (exists_gap_lt S R hbound ε hε)
    have hk := Nat.find_spec (exists_gap_lt S R hbound ε hε)
    have hb := volume_bounds S R k hbound
    have hg : (upperVolume S R k : ℝ) - (lowerVolume S R k : ℝ) < (ε : ℝ) := by
      first
      | exact_mod_cast hk
    change |(lowerVolume S R k : ℝ) - volume.real (solutionSet S)| < (ε : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr hb.1)]
    linarith

end VolumePolynomials.RationalElimination
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/RationalBoxVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalInterpolation.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# Explicit rational extraction of every coefficient

Substitution `tᵢ = z^((d+2)^i)` sends distinct degree-`d` monomials to distinct
powers of `z`, all below `(d+2)^n`. Ordinary univariate Lagrange interpolation
at the positive integers then extracts every coefficient by a fixed rational
linear combination of volume evaluations. The larger sampling set avoids
any unproved multivariate interpolation theorem.
-/

open Finset Polynomial
open scoped BigOperators

namespace VolumePolynomials

def coefficientCode {n d : ℕ} (α : MultiIndex n d) : ℕ :=
  Nat.ofDigits (d + 2) (List.ofFn fun i => (α.1 i : ℕ))

def interpolationSize (n d : ℕ) : ℕ := (d + 2) ^ n

theorem coefficientCode_lt {n d : ℕ} (α : MultiIndex n d) :
    coefficientCode α < interpolationSize n d := by
  first
  | have h := Nat.ofDigits_lt_base_pow_length (b := d + 2) (by omega)
      (l := List.ofFn fun i => (α.1 i : ℕ)) (by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact (α.1 i).isLt.trans (by omega))
    simpa only [coefficientCode, interpolationSize, List.length_ofFn] using h

theorem coefficientCode_injective (n d : ℕ) :
    Function.Injective (coefficientCode (n := n) (d := d)) := by
  first
  | intro α β h
    have hlist := Nat.ofDigits_inj_of_len_eq (b := d + 2) (by omega)
      (by simp : (List.ofFn fun i => (α.1 i : ℕ)).length =
        (List.ofFn fun i => (β.1 i : ℕ)).length)
      (by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact (α.1 i).isLt.trans (by omega))
      (by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact (β.1 i).isLt.trans (by omega)) h
    have hfun := List.ofFn_injective hlist
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hfun i)

theorem coefficientCode_eq_sum {n d : ℕ} (α : MultiIndex n d) :
    coefficientCode α = ∑ i : Fin n, (α.1 i : ℕ) * (d + 2) ^ (i : ℕ) := by
  first
  | have hmap : (List.ofFn fun i => (α.1 i : ℕ)).mapIdx
        (fun i a => a * (d + 2) ^ i) =
        List.ofFn (fun i : Fin n => (α.1 i : ℕ) * (d + 2) ^ (i : ℕ)) := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp
    rw [coefficientCode, Nat.ofDigits_eq_sum_mapIdx, hmap, List.sum_ofFn]

def interpolationNode {n d : ℕ} (j : Fin (interpolationSize n d)) : ℚ :=
  (j.val : ℚ) + 1

def interpolationWeight {n d : ℕ} (j : Fin (interpolationSize n d)) (i : Fin n) : ℚ :=
  interpolationNode j ^ ((d + 2) ^ (i : ℕ))

/-- Coefficients of the product of the normalized linear factors
`(X-a)/(x-a)`. This recursion uses only executable rational arithmetic. -/
def lagrangeCoefficient (x : ℚ) : List ℚ → ℕ → ℚ
  | [], m => if m = 0 then 1 else 0
  | a :: l, 0 => (x - a)⁻¹ * (-(a * lagrangeCoefficient x l 0))
  | a :: l, m + 1 =>
      (x - a)⁻¹ * (lagrangeCoefficient x l m - a * lagrangeCoefficient x l (m + 1))

theorem lagrangeCoefficient_eq (x : ℚ) (l : List ℚ) (m : ℕ) :
    lagrangeCoefficient x l m =
      ((l.map (Lagrange.basisDivisor x)).prod).coeff m := by
  first
  | induction l generalizing m with
    | nil => simp [lagrangeCoefficient, Polynomial.coeff_one]
    | cons a l ih =>
        cases m with
        | zero =>
            simp only [lagrangeCoefficient, List.map_cons, List.prod_cons,
              Lagrange.basisDivisor, mul_assoc, sub_mul, Polynomial.coeff_C_mul,
              Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero, zero_sub, ih]
        | succ m =>
            simp only [lagrangeCoefficient, List.map_cons, List.prod_cons,
              Lagrange.basisDivisor, mul_assoc, sub_mul, Polynomial.coeff_C_mul,
              Polynomial.coeff_sub, Polynomial.coeff_X_mul, ih]

/-- Every arithmetic entry is rational, with a finite, executable formula.
The definition does not call Mathlib's noncomputable polynomial operations. -/
def coefficientExtractionWeight {n d : ℕ} (α : MultiIndex n d)
    (j : Fin (interpolationSize n d)) : ℚ :=
  lagrangeCoefficient (interpolationNode j)
    (((List.finRange (interpolationSize n d)).filter (fun k => decide (k ≠ j))).map
      interpolationNode) (coefficientCode α)

/-- The executable recursion computes the exact Lagrange coefficient. -/
theorem coefficientExtractionWeight_eq {n d : ℕ} (α : MultiIndex n d)
    (j : Fin (interpolationSize n d)) :
    coefficientExtractionWeight α j =
      (Lagrange.basis Finset.univ (interpolationNode (n := n) (d := d)) j).coeff
        (coefficientCode α) := by
  first
  | let l := (List.finRange (interpolationSize n d)).filter (fun k => decide (k ≠ j))
    have hl : l.Nodup := (List.nodup_finRange _).filter _
    have hs : l.toFinset = (Finset.univ : Finset (Fin (interpolationSize n d))).erase j := by
      ext k
      simp [l, and_comm]
    unfold coefficientExtractionWeight
    rw [lagrangeCoefficient_eq]
    simp only [List.map_map]
    rw [← List.prod_toFinset _ hl, hs]
    rfl

theorem interpolationNode_pos {n d : ℕ} (j : Fin (interpolationSize n d)) :
    0 < interpolationNode j := by
  first
  | dsimp [interpolationNode]
    positivity

theorem interpolationWeight_pos {n d : ℕ} (j : Fin (interpolationSize n d)) (i : Fin n) :
    0 < interpolationWeight j i := pow_pos (interpolationNode_pos j) _

noncomputable def codedPolynomial {n d : ℕ} (c : Coefficients n d) : Polynomial ℝ :=
  ∑ α, Polynomial.monomial (coefficientCode α) (c α)

theorem codedPolynomial_coeff {n d : ℕ} (c : Coefficients n d) (α : MultiIndex n d) :
    (codedPolynomial c).coeff (coefficientCode α) = c α := by
  first
  | classical
    simp only [codedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      (coefficientCode_injective n d).eq_iff]
    simp

theorem codedPolynomial_degree_lt {n d : ℕ} (c : Coefficients n d) :
    (codedPolynomial c).degree < interpolationSize n d := by
  first
  | classical
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [codedPolynomial, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro α _
    exact Polynomial.coeff_monomial_of_ne (c α)
      (ne_of_gt ((coefficientCode_lt α).trans_le hm))

theorem codedPolynomial_eval {n d : ℕ} (c : Coefficients n d) (z : ℝ) :
    (codedPolynomial c).eval z = evaluate c (fun i => z ^ ((d + 2) ^ (i : ℕ))) := by
  first
  | classical
    simp only [codedPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, evaluate]
    apply Finset.sum_congr rfl
    intro α _
    rw [coefficientCode_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, Nat.mul_comm]

theorem map_rational_lagrange_basis {n d : ℕ}
    (j : Fin (interpolationSize n d)) :
    Polynomial.map (algebraMap ℚ ℝ)
      (Lagrange.basis Finset.univ (interpolationNode (n := n) (d := d)) j) =
      Lagrange.basis Finset.univ (fun k : Fin (interpolationSize n d) =>
        (interpolationNode k : ℝ)) j := by
  first
  | classical
    simp [Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod,
      Polynomial.map_mul, Polynomial.map_sub]

/-- Exact coefficient recovery from a fixed finite list of strictly positive
integer weight vectors. There is no coefficient omission or bounded parameter
restriction in this statement. -/
theorem coefficient_eq_rational_samples {n d : ℕ} (c : Coefficients n d)
    (α : MultiIndex n d) :
    c α = ∑ j : Fin (interpolationSize n d),
      (coefficientExtractionWeight α j : ℝ) *
        evaluate c (fun i => (interpolationWeight j i : ℝ)) := by
  first
  | classical
    have hnode : Set.InjOn (fun j : Fin (interpolationSize n d) =>
        (interpolationNode j : ℝ))
        (↑(Finset.univ : Finset (Fin (interpolationSize n d))) : Set _) := by
      intro i _ j _ hij
      apply Fin.ext
      have hrat : interpolationNode i = interpolationNode j := Rat.cast_injective hij
      have hval : (i.val : ℚ) = (j.val : ℚ) := add_right_cancel hrat
      exact Nat.cast_injective hval
    have hdeg : (codedPolynomial c).degree <
        (Finset.univ : Finset (Fin (interpolationSize n d))).card := by
      simpa using codedPolynomial_degree_lt c
    have hp := Lagrange.eq_interpolate (f := codedPolynomial c) hnode hdeg
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff (coefficientCode α)) hp
    rw [codedPolynomial_coeff, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff] at hcoeff
    refine hcoeff.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Polynomial.coeff_C_mul, codedPolynomial_eval]
    have hw : (Lagrange.basis Finset.univ
        (fun k : Fin (interpolationSize n d) => (interpolationNode k : ℝ)) j).coeff
          (coefficientCode α) = (coefficientExtractionWeight α j : ℝ) := by
      rw [← map_rational_lagrange_basis, Polynomial.coeff_map]
      exact congrArg (fun q : ℚ => (q : ℝ)) (coefficientExtractionWeight_eq α j).symm
    rw [hw, mul_comm]
    simp only [interpolationWeight, Rat.cast_pow]

def coefficientExtractionBound (n d : ℕ) : ℚ :=
  ∑ α : MultiIndex n d, ∑ j : Fin (interpolationSize n d),
    |coefficientExtractionWeight α j|

theorem coefficientExtractionBound_nonneg (n d : ℕ) :
    0 ≤ coefficientExtractionBound n d :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- The interpolation formula supplies an explicit rational modulus for
coefficient error from uniformly bounded sample-evaluation errors. -/
theorem abs_coefficient_sub_le_of_samples {n d : ℕ} (c c' : Coefficients n d)
    {η : ℝ} (hη : 0 ≤ η)
    (hsample : ∀ j : Fin (interpolationSize n d),
      |evaluate c (fun i => (interpolationWeight j i : ℝ)) -
        evaluate c' (fun i => (interpolationWeight j i : ℝ))| ≤ η)
    (α : MultiIndex n d) :
    |c α - c' α| ≤ (coefficientExtractionBound n d : ℝ) * η := by
  first
  | classical
    rw [coefficient_eq_rational_samples c α, coefficient_eq_rational_samples c' α,
      ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : Fin (interpolationSize n d),
          |(coefficientExtractionWeight α j : ℝ)| * η := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (hsample j) (abs_nonneg _)
      _ = (∑ j : Fin (interpolationSize n d),
          |(coefficientExtractionWeight α j : ℝ)|) * η := (Finset.sum_mul _ _ _).symm
      _ ≤ (coefficientExtractionBound n d : ℝ) * η := by
        apply mul_le_mul_of_nonneg_right _ hη
        simp only [coefficientExtractionBound, Rat.cast_sum, Rat.cast_abs]
        exact Finset.single_le_sum
          (fun β _ => Finset.sum_nonneg (fun j _ =>
            abs_nonneg (coefficientExtractionWeight β j : ℝ)))
          (Finset.mem_univ α)

end VolumePolynomials
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/RationalInterpolation.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalHullSampling.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Executable samples for rational vertex lists

All lists used in the algorithm have explicit order. In particular no
noncomputable conversion from a finset to a list is used. Actual finite
Minkowski sums are represented by all finite choices of one listed vertex
from each summand; their volume samples are computed with the certified
box-counting search.
-/

open Set Finset MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.RationalHulls

abbrev RationalPoint (d : ℕ) := Fin d → ℚ

def realPoint {d : ℕ} (x : RationalPoint d) : Space d := fun i => (x i : ℝ)

theorem realPoint_zero (d : ℕ) : realPoint (0 : RationalPoint d) = (0 : Space d) := by
  first
  | funext i
    change ((0 : ℚ) : ℝ) = 0
    exact Rat.cast_zero

def vertices {d : ℕ} (L : List (RationalPoint d)) : Set (Space d) :=
  realPoint '' {x | x ∈ L}

def hull {d : ℕ} (L : List (RationalPoint d)) : Set (Space d) := convexHull ℝ (vertices L)

theorem vertices_finite {d : ℕ} (L : List (RationalPoint d)) : (vertices L).Finite := by
  first
  | simpa only [vertices, List.coe_toFinset] using L.toFinset.finite_toSet.image realPoint

theorem vertices_eq_range {d : ℕ} (L : List (RationalPoint d)) :
    vertices L = range (fun i : Fin L.length => realPoint (L.get i)) := by
  first
  | ext x
    simp only [vertices, Set.mem_image, Set.mem_setOf_eq, List.mem_iff_get, Set.mem_range]
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨L.get i, ⟨i, rfl⟩, rfl⟩

noncomputable def body {d : ℕ} (L : List (RationalPoint d)) (hL : 0 ∈ L) : Body d where
  carrier := hull L
  convex' := convex_convexHull ℝ _
  isCompact' := (vertices_finite L).isCompact_convexHull ℝ
  nonempty' := ⟨(0 : Space d),
    subset_convexHull ℝ _ ⟨(0 : RationalPoint d), hL, realPoint_zero d⟩⟩

theorem zero_mem_body {d : ℕ} (L : List (RationalPoint d)) (hL : 0 ∈ L) :
    (0 : Space d) ∈ body L hL :=
  subset_convexHull ℝ _ ⟨(0 : RationalPoint d), hL, realPoint_zero d⟩

theorem body_subset_box {d : ℕ} (L : List (RationalPoint d)) (hL : 0 ∈ L)
    (R : ℚ) (hbox : ∀ v ∈ L, ∀ i, |v i| ≤ R) :
    (body L hL : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)) := by
  first
  | apply convexHull_min _ (convex_Icc _ _)
    rintro x ⟨v, hv, rfl⟩
    constructor
    · intro i
      have h := (abs_le.mp (hbox v hv i)).1
      change -(R : ℝ) ≤ (v i : ℝ)
      exact_mod_cast h
    · intro i
      have h := (abs_le.mp (hbox v hv i)).2
      change (v i : ℝ) ≤ (R : ℝ)
      exact_mod_cast h

def radiusBound {d : ℕ} (L : List (RationalPoint d)) : ℚ :=
  (L.map (fun v => ∑ i, |v i|)).sum

def integerRadius {d : ℕ} (L : List (RationalPoint d)) : ℕ := ⌈radiusBound L⌉₊

theorem abs_le_radiusBound {d : ℕ} (L : List (RationalPoint d))
    {v : RationalPoint d} (hv : v ∈ L) (i : Fin d) : |v i| ≤ radiusBound L := by
  first
  | apply (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)).trans
    exact List.single_le_sum (by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
      exact Finset.sum_nonneg (fun j _ => abs_nonneg (w j))) _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem hull_subset_ambient {d : ℕ} (L : List (RationalPoint d)) :
    hull L ⊆ RationalElimination.ambientBox d (integerRadius L) := by
  first
  | have hclosed : hull L ⊆ Icc (fun _ : Fin d => -(integerRadius L : ℝ))
        (fun _ => (integerRadius L : ℝ)) := by
      apply convexHull_min _ (convex_Icc _ _)
      rintro x ⟨v, hv, rfl⟩
      have hcoord (i : Fin d) : |realPoint v i| ≤ (integerRadius L : ℝ) := by
        have h := (abs_le_radiusBound L hv i).trans (Nat.le_ceil (radiusBound L))
        change |(v i : ℝ)| ≤ (integerRadius L : ℝ)
        rw [← Rat.cast_abs]
        exact_mod_cast h
      exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
    intro x hx i
    have h := hclosed hx
    exact ⟨by change -((integerRadius L : ℝ) + 1) < x i; linarith [h.1 i],
      by change x i ≤ (integerRadius L : ℝ) + 1; linarith [h.2 i]⟩

theorem halfspaces_solution_eq_hull {d : ℕ} (L : List (RationalPoint d)) :
    RationalElimination.solutionSet (RationalElimination.hullHalfspaces L.get) = hull L := by
  first
  | ext x
    rw [RationalElimination.solutionSet, Set.mem_setOf_eq,
      RationalElimination.hullHalfspaces_correct, hull, vertices_eq_range]
    rfl

/-- The radius and every halfspace are computed from the given finite list. -/
def approximateHullVolume {d : ℕ} (L : List (RationalPoint d)) (ε : ℚ) (hε : 0 < ε) : ℚ :=
  RationalElimination.approximateVolume (RationalElimination.hullHalfspaces L.get)
    (integerRadius L) (by rw [halfspaces_solution_eq_hull]; exact hull_subset_ambient L) ε hε

theorem approximateHullVolume_correct {d : ℕ} (L : List (RationalPoint d))
    (ε : ℚ) (hε : 0 < ε) :
    |(approximateHullVolume L ε hε : ℝ) - volume.real (hull L)| < (ε : ℝ) := by
  first
  | unfold approximateHullVolume
    simpa only [halfspaces_solution_eq_hull] using
      RationalElimination.approximateVolume_correct
        (RationalElimination.hullHalfspaces L.get) (integerRadius L)
        (by rw [halfspaces_solution_eq_hull]; exact hull_subset_ambient L) ε hε

/-- Ordered finite Cartesian products. -/
def selections {α : Type*} : {n : ℕ} → (Fin n → List α) → List (Fin n → α)
  | 0, _ => [Fin.elim0]
  | n + 1, L => (L 0).flatMap (fun a => (selections (Fin.tail L)).map (Fin.cons a))

theorem mem_selections {α : Type*} {n : ℕ} (L : Fin n → List α) (f : Fin n → α) :
    f ∈ selections L ↔ ∀ i, f i ∈ L i := by
  first
  | induction n with
    | zero =>
        simp only [selections, List.mem_singleton]
        constructor
        · intro _ i
          exact Fin.elim0 i
        · intro _
          funext i
          exact Fin.elim0 i
    | succ n ih =>
        simp only [selections, List.mem_flatMap, List.mem_map]
        constructor
        · rintro ⟨a, ha, g, hg, rfl⟩ i
          cases i using Fin.cases with
          | zero => exact ha
          | succ i => exact (ih (Fin.tail L) g).mp hg i
        · intro h
          exact ⟨f 0, h 0, Fin.tail f, (ih (Fin.tail L) (Fin.tail f)).mpr (fun i => h i.succ),
            Fin.cons_self_tail f⟩

def weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) : List (RationalPoint d) :=
  (selections L).map (fun f => ∑ i, t i • f i)

theorem mem_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) (v : RationalPoint d) :
    v ∈ weightedVertices L t ↔ ∃ f : Fin n → RationalPoint d,
      (∀ i, f i ∈ L i) ∧ ∑ i, t i • f i = v := by
  first
  | simp only [weightedVertices, List.mem_map, mem_selections]

theorem zero_mem_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (hL : ∀ i, 0 ∈ L i) (t : Fin n → ℚ) : 0 ∈ weightedVertices L t := by
  first
  | exact Iff.mpr (mem_weightedVertices L t 0) ⟨fun _ => 0, hL, by simp⟩

theorem vertices_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) :
    vertices (weightedVertices L t) = ∑ i, (t i : ℝ) • vertices (L i) := by
  first
  | classical
    ext x
    rw [Set.mem_fintype_sum]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨f, hf, rfl⟩ := Iff.mp (mem_weightedVertices L t v) hv
      refine ⟨fun i => (t i : ℝ) • realPoint (f i), ?_, ?_⟩
      · intro i
        exact ⟨realPoint (f i), ⟨f i, hf i, rfl⟩, rfl⟩
      · ext j
        simp [realPoint]
    · rintro ⟨a, ha, rfl⟩
      have hpoints : ∀ i, ∃ q ∈ L i, (t i : ℝ) • realPoint q = a i := by
        intro i
        obtain ⟨y, ⟨q, hq, rfl⟩, hqy⟩ := ha i
        exact ⟨q, hq, hqy⟩
      choose q hq hqa using hpoints
      refine ⟨∑ i, t i • q i, Iff.mpr (mem_weightedVertices L t _) ⟨q, hq, rfl⟩, ?_⟩
      rw [show (∑ i, a i) = ∑ i, (t i : ℝ) • realPoint (q i) by simp only [hqa]]
      ext j
      simp [realPoint]

theorem hull_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) :
    hull (weightedVertices L t) = ∑ i, (t i : ℝ) • hull (L i) := by
  first
  | rw [hull, vertices_weightedVertices, convexHull_sum]
    simp only [convexHull_smul, hull]

theorem weightedSum_body {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (hL : ∀ i, 0 ∈ L i) (t : Fin n → ℚ) :
    (weightedSum (fun i => body (L i) (hL i)) (fun i => (t i : ℝ)) : Set (Space d)) =
      hull (weightedVertices L t) := by
  first
  | rw [weightedSum, coe_sum_body, hull_weightedVertices]
    rfl

/-- Pure rational approximate coefficient vector recovered from all prescribed
positive rational samples. -/
def approximateCoefficients {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (ε : ℚ) (hε : 0 < ε) : MultiIndex n d → ℚ :=
  fun α => ∑ j : Fin (interpolationSize n d), coefficientExtractionWeight α j *
    approximateHullVolume (weightedVertices L (interpolationWeight j)) ε hε

theorem approximateCoefficients_correct {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (hL : ∀ i, 0 ∈ L i) {c : Coefficients n d}
    (hc : Realizes (fun i => body (L i) (hL i)) c) (ε : ℚ) (hε : 0 < ε)
    (α : MultiIndex n d) :
    |(approximateCoefficients L ε hε α : ℝ) - c α| ≤
      (coefficientExtractionBound n d : ℝ) * (ε : ℝ) := by
  first
  | rw [coefficient_eq_rational_samples c α]
    simp only [approximateCoefficients, Rat.cast_sum, Rat.cast_mul, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : Fin (interpolationSize n d),
          |(coefficientExtractionWeight α j : ℝ)| * (ε : ℝ) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul, hc _ (fun i => by exact_mod_cast (interpolationWeight_pos j i).le)]
        change |(coefficientExtractionWeight α j : ℝ)| *
          |(approximateHullVolume _ ε hε : ℝ) - volume.real
            (weightedSum (fun i => body (L i) (hL i))
              (fun i => (interpolationWeight j i : ℝ)) : Set (Space d))| ≤ _
        rw [weightedSum_body]
        exact mul_le_mul_of_nonneg_left (approximateHullVolume_correct _ ε hε).le (abs_nonneg _)
      _ = (∑ j : Fin (interpolationSize n d), |(coefficientExtractionWeight α j : ℝ)|) * (ε : ℝ) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (coefficientExtractionBound n d : ℝ) * (ε : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast hε.le)
        simp only [coefficientExtractionBound, Rat.cast_sum, Rat.cast_abs]
        exact Finset.single_le_sum
          (fun β _ => Finset.sum_nonneg (fun j _ => abs_nonneg (coefficientExtractionWeight β j : ℝ)))
          (Finset.mem_univ α)

end VolumePolynomials.RationalHulls
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/RationalHullSampling.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalGridBodies.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Finite rational grids for every bounded convex body

The enumerable objects are ordered sublists of a finite rational grid,
containing the origin. Every compact convex body in the prescribed box and
containing the origin has a listed convex hull at Hausdorff distance at most
`1/(k+1)`. The approximation theorem covers all dimensions and degenerate bodies.
-/

open Set Metric
open scoped BigOperators Pointwise

namespace VolumePolynomials.RationalHulls

def coordinateGrid (R k : ℕ) : List ℚ :=
  List.ofFn (fun i : Fin (2 * R * (k + 1) + 1) =>
    ((i.val : ℚ) - (R : ℚ) * (k + 1)) / (k + 1))

theorem zero_mem_coordinateGrid (R k : ℕ) : (0 : ℚ) ∈ coordinateGrid R k := by
  first
  | apply List.mem_ofFn.mpr
    refine ⟨⟨R * (k + 1),
      Nat.lt_succ_of_le (Nat.mul_le_mul_right (k + 1) (by omega))⟩, ?_⟩
    simp

theorem abs_le_of_mem_coordinateGrid {R k : ℕ} {q : ℚ}
    (hq : q ∈ coordinateGrid R k) : |q| ≤ (R : ℚ) := by
  first
  | obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    have hk : 0 < (k : ℚ) + 1 := by positivity
    have hi : (i.val : ℚ) ≤ 2 * (R : ℚ) * ((k : ℚ) + 1) := by
      exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have hi0 : 0 ≤ (i.val : ℚ) := by positivity
    rw [abs_le]
    constructor
    · apply (le_div_iff₀ hk).mpr
      nlinarith
    · apply (div_le_iff₀ hk).mpr
      nlinarith

theorem exists_coordinateGrid_near {R k : ℕ} {x : ℝ}
    (hx : -(R : ℝ) ≤ x ∧ x ≤ (R : ℝ)) :
    ∃ q ∈ coordinateGrid R k, |x - (q : ℝ)| ≤ 1 / ((k : ℝ) + 1) := by
  first
  | let a : ℝ := ((k : ℝ) + 1) * (x + (R : ℝ))
    have ha : 0 ≤ a := mul_nonneg (by positivity) (by linarith)
    have hb : a ≤ (2 * R * (k + 1) : ℕ) := by
      dsimp [a]
      push_cast
      nlinarith
    let i : Fin (2 * R * (k + 1) + 1) :=
      ⟨⌊a⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le hb)⟩
    let q : ℚ := ((i.val : ℚ) - (R : ℚ) * (k + 1)) / (k + 1)
    refine ⟨q, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    have hk : 0 < (k : ℝ) + 1 := by positivity
    have hlo := Nat.floor_le ha
    have hhi := Nat.lt_floor_add_one a
    have hq : (q : ℝ) * ((k : ℝ) + 1) = (⌊a⌋₊ : ℝ) - (R : ℝ) * ((k : ℝ) + 1) := by
      dsimp [q, i]
      push_cast
      exact div_mul_cancel₀ _ hk.ne'
    have hnonneg : 0 ≤ x - (q : ℝ) := by
      apply (mul_nonneg_iff_of_pos_right hk).mp
      dsimp [a] at hlo
      nlinarith
    rw [abs_of_nonneg hnonneg]
    apply (le_div_iff₀ hk).mpr
    dsimp [a] at hhi
    nlinarith

def vertexGrid (d R k : ℕ) : List (RationalPoint d) :=
  selections (fun _ : Fin d => coordinateGrid R k)

theorem mem_vertexGrid {d R k : ℕ} (v : RationalPoint d) :
    v ∈ vertexGrid d R k ↔ ∀ i, v i ∈ coordinateGrid R k := mem_selections _ _

theorem zero_mem_vertexGrid (d R k : ℕ) : (0 : RationalPoint d) ∈ vertexGrid d R k :=
  Iff.mpr (mem_vertexGrid 0) (fun _ => zero_mem_coordinateGrid R k)

theorem vertexGrid_bounded {d R k : ℕ} {v : RationalPoint d}
    (hv : v ∈ vertexGrid d R k) (i : Fin d) : |v i| ≤ (R : ℚ) :=
  abs_le_of_mem_coordinateGrid (Iff.mp (mem_vertexGrid v) hv i)

theorem exists_vertexGrid_near {d R k : ℕ} {x : Space d}
    (hx : x ∈ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) :
    ∃ v ∈ vertexGrid d R k, dist x (realPoint v) ≤ 1 / ((k : ℝ) + 1) := by
  first
  | choose v hv hdist using fun i => exists_coordinateGrid_near (R := R) (k := k)
      (x := x i) ⟨hx.1 i, hx.2 i⟩
    refine ⟨v, Iff.mpr (mem_vertexGrid v) hv, ?_⟩
    exact (dist_pi_le_iff (by positivity)).mpr
      (fun i => by simpa only [Real.dist_eq, realPoint] using hdist i)

/-- All finite vertex-list candidates. Membership is an executable rational
list predicate, and every candidate is a nonempty actual body. -/
def candidates (d R k : ℕ) : List (List (RationalPoint d)) :=
  (vertexGrid d R k).sublists.filter (fun L => 0 ∈ L)

theorem mem_candidates {d R k : ℕ} (L : List (RationalPoint d)) :
    L ∈ candidates d R k ↔ L.Sublist (vertexGrid d R k) ∧ 0 ∈ L := by
  first
  | simp [candidates, List.mem_sublists]

theorem candidate_bounded {d R k : ℕ} (L : List (RationalPoint d))
    (hL : L ∈ candidates d R k) :
    (body L (Iff.mp (mem_candidates L) hL).2 : Set (Space d)) ⊆
      Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)) := by
  first
  | apply body_subset_box L _ (R : ℚ)
    intro v hv i
    exact vertexGrid_bounded ((Iff.mp (mem_candidates L) hL).1.subset hv) i

/-- Quantitative completeness of the finite rational body enumeration. -/
theorem exists_candidate_near {d R k : ℕ} (K : Body d)
    (h0 : (0 : Space d) ∈ K)
    (hbox : (K : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) :
    ∃ L, ∃ hL : L ∈ candidates d R k,
      dist K (body L (Iff.mp (mem_candidates L) hL).2) ≤ 1 / ((k : ℝ) + 1) := by
  first
  | classical
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    have hε : 0 ≤ ε := by positivity
    let P : RationalPoint d → Prop := fun v => ∃ x ∈ K, dist (realPoint v) x ≤ ε
    let L : List (RationalPoint d) := (vertexGrid d R k).filter (fun v => P v)
    have hL0 : (0 : RationalPoint d) ∈ L := by
      apply List.mem_filter.mpr
      refine ⟨zero_mem_vertexGrid d R k, ?_⟩
      simp only [decide_eq_true_eq]
      exact ⟨0, h0, by simpa only [realPoint_zero, dist_self] using hε⟩
    have hL : L ∈ candidates d R k :=
      Iff.mpr (mem_candidates L) ⟨List.filter_sublist, hL0⟩
    let Q := body L hL0
    have hQ : (Q : Set (Space d)) ⊆ (K : Set (Space d)) + closedBall 0 ε := by
      apply convexHull_min _ (K.convex.add (convex_closedBall _ _))
      rintro y ⟨v, hv, rfl⟩
      have hv' : v ∈ vertexGrid d R k ∧ P v := by
        simpa only [L, List.mem_filter, decide_eq_true_eq, Set.mem_setOf_eq] using hv
      obtain ⟨x, hx, hdist⟩ := hv'.2
      refine ⟨x, hx, realPoint v - x, ?_, by abel⟩
      simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hdist
    refine ⟨L, hL, ?_⟩
    change hausdorffDist (K : Set (Space d)) (Q : Set (Space d)) ≤ ε
    apply hausdorffDist_le_of_mem_dist hε
    · intro x hx
      obtain ⟨v, hv, hdist⟩ := exists_vertexGrid_near (hbox hx)
      have hvm : v ∈ L := by
        apply List.mem_filter.mpr
        refine ⟨hv, ?_⟩
        simp only [decide_eq_true_eq]
        exact ⟨x, hx, by rwa [dist_comm]⟩
      exact ⟨realPoint v, subset_convexHull ℝ _ ⟨v, hvm, rfl⟩, hdist⟩
    · intro y hy
      obtain ⟨x, hx, z, hz, rfl⟩ := hQ hy
      refine ⟨x, hx, ?_⟩
      simpa only [mem_closedBall, dist_eq_norm, sub_zero, add_sub_cancel_left] using hz

/-- All candidate tuples, generated by the same finite-list product algorithm. -/
def candidateTuples (n d R k : ℕ) : List (Fin n → List (RationalPoint d)) :=
  selections (fun _ : Fin n => candidates d R k)

theorem mem_candidateTuples {n d R k : ℕ} (L : Fin n → List (RationalPoint d)) :
    L ∈ candidateTuples n d R k ↔ ∀ i, L i ∈ candidates d R k := mem_selections _ _

end VolumePolynomials.RationalHulls
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/RationalGridBodies.lean -/

/- BEGIN SOURCE: VolumePolynomials/RealizationCone.lean -/
section

@[expose] public section

/-!
# Scaling and zero-volume realizations

The zero-coefficient conclusion below is derived from actual geometric
monotonicity, without assuming coefficient nonnegativity or Minkowski's
polynomial-existence theorem.
-/

noncomputable section
open Set MeasureTheory Finset
open scoped Pointwise BigOperators NNReal

namespace VolumePolynomials

theorem evaluate_smul {n d : ℕ} (r : ℝ) (c : Coefficients n d) (t : Fin n → ℝ) :
    evaluate (r • c) t = r * evaluate c t := by
  simp [evaluate, Finset.mul_sum, mul_assoc]

theorem weightedSum_smul {n d : ℕ} (r : ℝ) (K : Fin n → Body d) (t : Fin n → ℝ) :
    weightedSum (fun i => r • K i) t = r • weightedSum K t := by
  simp [weightedSum, Finset.smul_sum, smul_smul, mul_comm]

theorem Realizes.dilate {n d : ℕ} {K : Fin n → Body d} {c : Coefficients n d}
    (h : Realizes K c) {r : ℝ} (hr : 0 ≤ r) :
    Realizes (fun i => r • K i) (r ^ d • c) := by
  intro t ht
  rw [evaluate_smul, h t ht]
  simp only [volumeFunction, weightedSum_smul, bodyVolume_smul _ hr]

theorem smul_mem_volumeLocus {n d : ℕ} (hd : 0 < d) {c : Coefficients n d}
    (hc : c ∈ VolumeLocus n d) {a : ℝ} (ha : 0 ≤ a) : a • c ∈ VolumeLocus n d := by
  obtain ⟨K, hK⟩ := hc
  have h := hK.dilate (Real.rpow_nonneg ha ((d : ℝ)⁻¹))
  rw [Real.rpow_inv_natCast_pow ha hd.ne'] at h
  exact ⟨_, h⟩

theorem bodyVolume_mono {d : ℕ} {K L : Body d} (h : K ≤ L) :
    bodyVolume K ≤ bodyVolume L :=
  ENNReal.toReal_mono L.isCompact.measure_lt_top.ne (measure_mono h)

theorem weightedSum_le_smul_of_zero_mem {n d : ℕ} (K : Fin n → Body d)
    (h0 : ∀ i, (0 : Space d) ∈ K i) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    {r : ℝ} (hr : 0 ≤ r) (htr : ∀ i, t i ≤ r) : weightedSum K t ≤ r • ∑ i, K i := by
  rw [Finset.smul_sum]
  apply sum_body_mono
  intro i
  change (⟨t i, ht i⟩ : ℝ≥0) • K i ≤ (⟨r, hr⟩ : ℝ≥0) • K i
  exact (K i).smul_le_of_le (h0 i) (htr i)

theorem volumeFunction_le_of_zero_mem {n d : ℕ} (K : Fin n → Body d)
    (h0 : ∀ i, (0 : Space d) ∈ K i) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    {r : ℝ} (hr : 0 ≤ r) (htr : ∀ i, t i ≤ r) :
    volumeFunction K t ≤ r ^ d * bodyVolume (∑ i, K i) := by
  calc
    volumeFunction K t ≤ bodyVolume (r • ∑ i, K i) :=
      bodyVolume_mono (weightedSum_le_smul_of_zero_mem K h0 t ht hr htr)
    _ = r ^ d * bodyVolume (∑ i, K i) := bodyVolume_smul _ hr

theorem volumeFunction_le {n d : ℕ} (K : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {r : ℝ} (hr : 0 ≤ r)
    (htr : ∀ i, t i ≤ r) :
    volumeFunction K t ≤ r ^ d * bodyVolume (∑ i, K i) := by
  choose p hp using fun i => (K i).nonempty
  let L : Fin n → Body d := fun i => translateBody (-p i) (K i)
  have h0 : ∀ i, (0 : Space d) ∈ L i := by
    intro i
    simpa [L, mem_translateBody] using hp i
  have h := volumeFunction_le_of_zero_mem L h0 t ht hr htr
  have hsum : bodyVolume (∑ i, L i) = bodyVolume (∑ i, K i) := by
    simpa only [volumeFunction, weightedSum_one] using
      volumeFunction_translate K (fun i => -p i) (fun _ => 1)
  rwa [hsum, volumeFunction_translate] at h

theorem Realizes.evaluate_le_sum {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    evaluate c t ≤ (1 + ∑ i, t i) ^ d * ∑ α, c α := by
  rw [hc t ht, hc.sum_coefficients]
  apply volumeFunction_le K t ht
  · exact add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => ht i)
  · intro i
    exact (Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)

/-- A realizing tuple of total volume zero realizes only the zero polynomial.
This includes all configurations whose total Minkowski sum is lower dimensional. -/
theorem Realizes.eq_zero_of_sum_eq_zero {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) (hzero : ∑ α, c α = 0) : c = 0 := by
  apply coefficients_eq_of_evaluate_nonneg
  intro t ht
  have hu := hc.evaluate_le_sum t ht
  rw [hzero, mul_zero] at hu
  have hl := hc.evaluate_nonneg ht
  simpa [evaluate] using le_antisymm hu hl

theorem zero_mem_volumeLocus {n d : ℕ} (hd : 0 < d) :
    (0 : Coefficients n d) ∈ VolumeLocus n d := by
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨fun _ => 0, fun t _ => ?_⟩
  simp [evaluate, volumeFunction, weightedSum, bodyVolume, Measure.real]
  change 0 = (volume {(0 : Space d)}).toReal
  simp

end VolumePolynomials
end -- original EOF section
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/RealizationCone.lean -/

