module
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Papers.FieldCoordinates
public import Papers.FieldSpan
public import Papers.FiniteHullCertificates
public import Papers.HomogeneousConvex
public import Papers.PolytopeTargets
public import Papers.RationalCoordinates

set_option Elab.async false

/-!
# The seventeen-vertex field theorem

The exact arithmetic, convex-hull certificate, face ranks, and reconstruction
argument share the same polytope and realization definitions as Theorem 3.
Each constituent proof retains its original scope below.
-/

section BundlePart0
/- Source: Papers/QuadraticArithmetic.lean -/








@[expose] public section

/-!
# Exact arithmetic for the 17-vertex certificate

The integer-pair operations encode `a + b φ`, where `φ² = φ + 1`.
All finite certificate checks use ordinary kernel reduction (`decide`).
The bridge from integer arithmetic to real geometry is proved here.
-/

namespace Papers.Nonrational

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

theorem phi_sq : phi ^ 2 = phi + 1 := by
  have h : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  dsimp [phi]
  nlinarith

theorem phi_basic_bounds : 1 < phi ∧ phi < 2 := by
  have h : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  dsimp [phi]
  constructor <;> nlinarith

/-- Integers representing an element of `ℤ[φ]`. -/
abbrev QuadInt := ℤ × ℤ

namespace QuadInt

def add (x y : QuadInt) : QuadInt := (x.1 + y.1, x.2 + y.2)
def neg (x : QuadInt) : QuadInt := (-x.1, -x.2)
def mul (x y : QuadInt) : QuadInt :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

noncomputable def eval (x : QuadInt) : ℝ := (x.1 : ℝ) + (x.2 : ℝ) * phi

@[simp] theorem eval_zero : eval (0, 0) = 0 := by simp [eval]

@[simp] theorem eval_add (x y : QuadInt) : eval (add x y) = eval x + eval y := by
  simp only [eval, add, Int.cast_add]
  ring

@[simp] theorem eval_neg (x : QuadInt) : eval (neg x) = -eval x := by
  simp only [eval, neg, Int.cast_neg]
  ring

@[simp] theorem eval_mul (x y : QuadInt) : eval (mul x y) = eval x * eval y := by
  simp only [eval, mul, Int.cast_add, Int.cast_mul]
  linear_combination -((x.2 : ℝ) * (y.2 : ℝ)) * phi_sq

/-- A five-coordinate dot product, expressed with integer-pair operations. -/
def dot5 (x y : Fin 5 → QuadInt) : QuadInt :=
  add (mul (x 0) (y 0)) (add (mul (x 1) (y 1))
    (add (mul (x 2) (y 2)) (add (mul (x 3) (y 3)) (mul (x 4) (y 4)))))

theorem eval_dot5 (x y : Fin 5 → QuadInt) :
    eval (dot5 x y) = ∑ k : Fin 5, eval (x k) * eval (y k) := by
  simp [dot5, Fin.sum_univ_succ]

/-- A rational lower bound obtained by choosing the appropriate endpoint
of a certified interval for `φ`. -/
def positiveAt (scale lo hi : ℤ) (x : QuadInt) : Bool :=
  if 0 ≤ x.2 then decide (0 < scale * x.1 + lo * x.2)
  else decide (0 < scale * x.1 + hi * x.2)

theorem eval_pos_of_positiveAt (scale lo hi : ℤ)
    (hscale : 0 < scale)
    (hlo : (lo : ℝ) / scale ≤ phi) (hhi : phi ≤ (hi : ℝ) / scale)
    (x : QuadInt) (hx : positiveAt scale lo hi x = true) : 0 < eval x := by
  have hscale' : (0 : ℝ) < scale := by exact_mod_cast hscale
  by_cases hb : 0 ≤ x.2
  · have hsum : 0 < scale * x.1 + lo * x.2 := by
      simpa [positiveAt, hb] using hx
    have hsum' : (0 : ℝ) < scale * (x.1 : ℝ) + lo * (x.2 : ℝ) := by
      exact_mod_cast hsum
    have hb' : (0 : ℝ) ≤ x.2 := by exact_mod_cast hb
    have hmul := mul_le_mul_of_nonneg_right ((div_le_iff₀ hscale').mp hlo) hb'
    have hproduct : 0 < (scale : ℝ) * eval x := by
      dsimp [eval]
      nlinarith
    exact (mul_pos_iff_of_pos_left hscale').mp hproduct
  · have hsum : 0 < scale * x.1 + hi * x.2 := by
      simpa [positiveAt, hb] using hx
    have hsum' : (0 : ℝ) < scale * (x.1 : ℝ) + hi * (x.2 : ℝ) := by
      exact_mod_cast hsum
    have hb' : (x.2 : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hb))
    have hmul := mul_le_mul_of_nonpos_right ((le_div_iff₀ hscale').mp hhi) hb'
    have hproduct : 0 < (scale : ℝ) * eval x := by
      dsimp [eval]
      nlinarith
    exact (mul_pos_iff_of_pos_left hscale').mp hproduct

end QuadInt
end Papers.Nonrational

end
end BundlePart0

section BundlePart1
/- Source: Papers/SeventeenData.lean -/



@[expose] public section

/-! Generated from the supplied exact certificate. All assertions below are
kernel-checked integer computations, not trusted calls to the generator. -/

namespace Papers.Nonrational.SeventeenData
open QuadInt
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def vertices : Fin 17 → Fin 5 → QuadInt :=
  ![![(1, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (-1, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (-1, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (1, 0), (0, 0)], ![(1, 0), (0, 0), (1, 0), (1, 0), (0, 0)], ![(0, 0), (-1, 0), (0, 1), (0, 1), (0, 0)], ![(1, 0), (1, 0), (1, -1), (0, 0), (0, 0)], ![(6, -6), (5, 0), (4, 0), (16, 0), (1, 0)], ![(7, -6), (6, 0), (4, 0), (16, 0), (1, 0)], ![(-15, 4), (-6, 0), (13, 0), (20, 0), (1, 0)], ![(-15, 4), (-6, 0), (14, 0), (21, 0), (1, 0)], ![(12, -7), (10, -1), (4, 1), (17, 0), (1, 0)], ![(12, -6), (11, 0), (4, 0), (17, 0), (1, 0)], ![(11, 6), (12, 0), (-4, 0), (6, 0), (-1, 0)], ![(11, 6), (11, 0), (-3, 0), (6, 0), (-1, 0)], ![(17, 0), (-9, 0), (15, 1), (11, 0), (-1, 0)], ![(17, 0), (-8, 0), (15, 0), (10, 0), (-1, 0)]]

def forms : Fin 23 → Fin 5 → QuadInt :=
  ![![(0, 0), (0, 0), (-1, 0), (3, 0), (-44, 0)], ![(1, 1), (-1, -1), (-1, 0), (0, 0), (9, 11)], ![(0, 0), (1, -1), (-3, 0), (3, 0), (-15, -6)], ![(3, 0), (-1, 0), (0, 0), (0, 0), (39, -12)], ![(0, 0), (1, -1), (-1, 0), (2, 0), (-41, 11)], ![(0, 2), (-1, -2), (-2, -1), (1, 0), (14, 14)], ![(1, 0), (0, 0), (0, 0), (1, 0), (17, 6)], ![(-1, 2), (-1, -2), (-1, -2), (2, 0), (5, 12)], ![(2, 1), (0, -1), (-1, 0), (0, 0), (19, 25)], ![(-1, 1), (2, -3), (-2, -1), (3, 0), (-33, 26)], ![(0, 0), (1, -1), (-1, 0), (1, 0), (-24, 11)], ![(0, 0), (1, -1), (-1, 0), (1, 0), (-13, 8)], ![(0, 0), (0, 0), (0, 0), (1, 0), (-16, 0)], ![(0, 0), (0, 0), (0, 0), (1, 0), (6, 0)], ![(1, 0), (0, 0), (0, 0), (0, 0), (15, -4)], ![(1, 0), (0, 0), (0, 0), (0, 0), (17, 0)], ![(0, 0), (0, 0), (-1, 0), (1, 0), (-6, 0)], ![(1, 0), (-1, 0), (0, 0), (0, 0), (-1, 6)], ![(0, 0), (-9, 4), (-28, 4), (36, 3), (-410, -88)], ![(0, 0), (0, 0), (-2, 0), (9, 0), (60, 0)], ![(4, 0), (0, 0), (0, 0), (21, -10), (-360, 184)], ![(6, -1), (1, -5), (32, -26), (-38, 27), (450, -268)], ![(0, 0), (0, 0), (-1, 0), (1, 0), (-4, -1)]]

def values : Fin 23 → Fin 17 → QuadInt :=
  ![![(0, 0), (0, 0), (1, 0), (3, 0), (2, 0), (0, 2), (-1, 1), (0, 0), (0, 0), (3, 0), (5, 0), (3, -1), (3, 0), (66, 0), (65, 0), (62, -1), (59, 0)], ![(1, 1), (1, 1), (1, 0), (0, 0), (0, 1), (1, 0), (-1, 1), (0, 0), (0, 0), (-9, 10), (-10, 10), (1, 0), (0, 0), (0, 0), (0, 1), (2, 14), (1, 14)], ![(0, 0), (-1, 1), (3, 0), (3, 0), (0, 0), (-1, 1), (-2, 2), (26, -11), (27, -12), (0, 0), (0, 0), (35, -19), (35, -17), (57, -6), (53, -5), (-6, 12), (-8, 14)], ![(3, 0), (1, 0), (0, 0), (0, 0), (3, 0), (1, 0), (2, 0), (52, -30), (54, -30), (0, 0), (0, 0), (65, -32), (64, -30), (-18, 30), (-17, 30), (21, 12), (20, 12)], ![(0, 0), (-1, 1), (1, 0), (2, 0), (1, 0), (-1, 2), (0, 0), (-8, 6), (-7, 5), (-20, 17), (-19, 17), (0, 0), (0, 0), (69, -23), (67, -22), (39, -3), (38, -3)], ![(0, 2), (1, 2), (2, 1), (1, 0), (-1, 1), (0, 0), (-2, 2), (5, 0), (4, 0), (22, -9), (21, -10), (0, 0), (0, 0), (0, 0), (-1, 1), (-25, 20), (-26, 21)], ![(1, 0), (0, 0), (0, 0), (1, 0), (2, 0), (0, 1), (1, 0), (39, 0), (40, 0), (22, 10), (23, 10), (46, -1), (46, 0), (0, 0), (0, 0), (11, -6), (10, -6)], ![(-1, 2), (1, 2), (1, 2), (2, 0), (0, 0), (-1, 1), (-1, 1), (10, 0), (8, 0), (61, -28), (62, -30), (-1, 1), (0, 0), (0, 0), (0, 0), (-8, 7), (-9, 8)], ![(2, 1), (0, 1), (1, 0), (0, 0), (1, 1), (0, 0), (1, 1), (21, 8), (23, 8), (-20, 28), (-21, 28), (33, 6), (33, 8), (13, -8), (12, -7), (0, 0), (0, 0)], ![(-1, 1), (-2, 3), (2, 1), (3, 0), (0, 0), (-3, 3), (0, 0), (5, 13), (6, 11), (8, 16), (9, 15), (13, 2), (14, 1), (78, -47), (74, -45), (0, 0), (0, 0)], ![(0, 0), (-1, 1), (1, 0), (1, 0), (0, 0), (-1, 1), (0, 0), (-7, 6), (-6, 5), (-23, 17), (-23, 17), (0, 0), (0, 0), (46, -23), (44, -22), (11, -3), (11, -3)], ![(0, 0), (-1, 1), (1, 0), (1, 0), (0, 0), (-1, 1), (0, 0), (4, 3), (5, 2), (-12, 14), (-12, 14), (11, -3), (11, -3), (35, -20), (33, -19), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (1, 0), (1, 0), (0, 1), (0, 0), (0, 0), (0, 0), (4, 0), (5, 0), (1, 0), (1, 0), (22, 0), (22, 0), (27, 0), (26, 0)], ![(0, 0), (0, 0), (0, 0), (1, 0), (1, 0), (0, 1), (0, 0), (22, 0), (22, 0), (26, 0), (27, 0), (23, 0), (23, 0), (0, 0), (0, 0), (5, 0), (4, 0)], ![(1, 0), (0, 0), (0, 0), (0, 0), (1, 0), (0, 0), (1, 0), (21, -10), (22, -10), (0, 0), (0, 0), (27, -11), (27, -10), (-4, 10), (-4, 10), (2, 4), (2, 4)], ![(1, 0), (0, 0), (0, 0), (0, 0), (1, 0), (0, 0), (1, 0), (23, -6), (24, -6), (2, 4), (2, 4), (29, -7), (29, -6), (-6, 6), (-6, 6), (0, 0), (0, 0)], ![(0, 0), (0, 0), (1, 0), (1, 0), (0, 0), (0, 0), (-1, 1), (6, 0), (6, 0), (1, 0), (1, 0), (7, -1), (7, 0), (16, 0), (15, 0), (2, -1), (1, 0)], ![(1, 0), (1, 0), (0, 0), (0, 0), (1, 0), (1, 0), (0, 0), (0, 0), (0, 0), (-10, 10), (-10, 10), (1, 0), (0, 0), (0, 0), (1, 0), (27, -6), (26, -6)], ![(0, 0), (9, -4), (28, -4), (36, 3), (8, 7), (16, 11), (-41, 32), (9, -4), (0, 0), (0, 0), (8, 7), (0, 0), (-9, 23), (630, 138), (611, 138), (471, 121), (422, 146)], ![(0, 0), (0, 0), (2, 0), (9, 0), (7, 0), (0, 7), (-2, 2), (196, 0), (196, 0), (214, 0), (221, 0), (205, -2), (205, 0), (2, 0), (0, 0), (9, -2), (0, 0)], ![(4, 0), (0, 0), (0, 0), (21, -10), (25, -10), (-10, 11), (4, 0), (0, 0), (4, 0), (0, 0), (21, -10), (45, -14), (45, -10), (530, -220), (530, -220), (659, -294), (638, -284)], ![(6, -1), (-1, 5), (-32, 26), (-38, 27), (0, 0), (0, 0), (65, -38), (17, -1), (24, -7), (6, -1), (0, 0), (0, 0), (21, -10), (-734, 493), (-703, 472), (-321, 209), (-256, 171)], ![(0, 0), (0, 0), (1, 0), (1, 0), (0, 0), (0, 0), (-1, 1), (8, -1), (8, -1), (3, -1), (3, -1), (9, -2), (9, -1), (14, 1), (13, 1), (0, 0), (-1, 1)]]

def chart : Fin 5 → QuadInt := ![(1, 0), (-1, 0), (-1, 0), (1, 0), (0, 0)]

def chartValues : Fin 17 → QuadInt := ![(1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (-1, 1), (13, -6), (13, -6), (-2, 4), (-2, 4), (15, -7), (14, -6), (9, 6), (9, 6), (22, -1), (20, 0)]

def scale : ℤ := 1000
def lo : ℤ := 1618
def hi : ℤ := 1619

theorem interval : (lo : ℝ) / scale ≤ phi ∧ phi ≤ (hi : ℝ) / scale := by
  have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  dsimp [phi, lo, hi, scale]
  constructor <;> nlinarith

theorem dot_values : ∀ f v, dot5 (forms f) (vertices v) = values f v := by decide

theorem chart_values : ∀ v, dot5 chart (vertices v) = chartValues v := by decide

theorem values_nonnegative : ∀ f v, values f v = (0, 0) ∨
    positiveAt scale lo hi (values f v) = true := by decide

theorem chart_positive : ∀ v, positiveAt scale lo hi (chartValues v) = true := by decide

theorem distinguish_vertices : ∀ v w : Fin 17, v ≠ w →
    ∃ f, values f v = (0, 0) ∧ positiveAt scale lo hi (values f w) = true := by decide

end Papers.Nonrational.SeventeenData

end
end BundlePart1

section BundlePart2
/- Source: Papers/SeventeenCoordinates.lean -/





@[expose] public section

/-!
# The actual seventeen-vertex convex hull

Coordinates are obtained by dehomogenizing the supplied exact construction in
its positive chart. Supporting forms are evaluated on real points, and the
convex-polytope structure is derived from their strict separation properties.
-/

noncomputable section

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

namespace Papers.Nonrational.Seventeen

def homogeneous (v : Fin 17) (i : Fin 5) : ℝ := QuadInt.eval (SeventeenData.vertices v i)
def chartValue (v : Fin 17) : ℝ := QuadInt.eval (SeventeenData.chartValues v)
def formCoordinate (f : Fin 23) (i : Fin 5) : ℝ := QuadInt.eval (SeventeenData.forms f i)
def supportValue (f : Fin 23) (v : Fin 17) : ℝ := QuadInt.eval (SeventeenData.values f v)

theorem eval_pos_of_certificate (x : QuadInt)
    (h : QuadInt.positiveAt SeventeenData.scale SeventeenData.lo SeventeenData.hi x = true) :
    0 < QuadInt.eval x :=
  QuadInt.eval_pos_of_positiveAt SeventeenData.scale SeventeenData.lo SeventeenData.hi
    (by norm_num [SeventeenData.scale]) SeventeenData.interval.1 SeventeenData.interval.2 x h

theorem chartValue_pos (v : Fin 17) : 0 < chartValue v :=
  eval_pos_of_certificate _ (SeventeenData.chart_positive v)

theorem supportValue_nonneg (f : Fin 23) (v : Fin 17) : 0 ≤ supportValue f v := by
  rcases SeventeenData.values_nonnegative f v with h | h
  · simp [supportValue, h]
  · exact (eval_pos_of_certificate _ h).le

theorem chart_identity (v : Fin 17) :
    chartValue v = homogeneous v 0 - homogeneous v 1 - homogeneous v 2 + homogeneous v 3 := by
  rw [chartValue, ← SeventeenData.chart_values, QuadInt.eval_dot5]
  norm_num [SeventeenData.chart, QuadInt.eval, homogeneous, Fin.sum_univ_succ]
  ring

theorem support_identity (f : Fin 23) (v : Fin 17) :
    supportValue f v = ∑ i : Fin 5, formCoordinate f i * homogeneous v i := by
  rw [supportValue, ← SeventeenData.dot_values, QuadInt.eval_dot5]
  rfl

def point (v : Fin 17) : E 4 :=
  WithLp.toLp 2 (fun i : Fin 4 => homogeneous v i.succ / chartValue v)

@[simp] theorem point_apply (v : Fin 17) (i : Fin 4) :
    point v i = homogeneous v i.succ / chartValue v := rfl

def coordinate (i : Fin 4) : E 4 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => x i
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem coordinate_apply (i : Fin 4) (x : E 4) : coordinate i x = x i := rfl

def support (f : Fin 23) : E 4 →L[ℝ] ℝ :=
  (formCoordinate f 0 + formCoordinate f 1) • coordinate 0 +
  (formCoordinate f 0 + formCoordinate f 2) • coordinate 1 +
  (formCoordinate f 3 - formCoordinate f 0) • coordinate 2 +
  formCoordinate f 4 • coordinate 3

def offset (f : Fin 23) : ℝ := -formCoordinate f 0

@[simp] theorem support_apply (f : Fin 23) (x : E 4) :
    support f x = (formCoordinate f 0 + formCoordinate f 1) * x 0 +
      (formCoordinate f 0 + formCoordinate f 2) * x 1 +
      (formCoordinate f 3 - formCoordinate f 0) * x 2 + formCoordinate f 4 * x 3 := rfl

theorem support_at_point (f : Fin 23) (v : Fin 17) :
    support f (point v) = supportValue f v / chartValue v + offset f := by
  rw [support_apply, support_identity]
  simp only [point_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [Fin.sum_univ_succ]
  dsimp [offset]
  have hc := ne_of_gt (chartValue_pos v)
  field_simp
  linear_combination formCoordinate f 0 * chart_identity v

theorem support_bound (f : Fin 23) (v : Fin 17) : offset f ≤ support f (point v) := by
  rw [support_at_point]
  exact le_add_of_nonneg_left (div_nonneg (supportValue_nonneg f v) (chartValue_pos v).le)

theorem support_incidence (f : Fin 23) (v : Fin 17) :
    support f (point v) = offset f ↔ SeventeenData.values f v = (0, 0) := by
  constructor
  · intro h
    rcases SeventeenData.values_nonnegative f v with hz | hp
    · exact hz
    · have hp' : 0 < supportValue f v := eval_pos_of_certificate _ hp
      have hdiv := div_pos hp' (chartValue_pos v)
      rw [support_at_point] at h
      linarith
  · intro h
    rw [support_at_point]
    simp [supportValue, h]

theorem support_separation (v w : Fin 17) (hvw : v ≠ w) :
    ∃ f, support f (point v) = offset f ∧ offset f < support f (point w) := by
  obtain ⟨f, hfv, hfw⟩ := SeventeenData.distinguish_vertices v w hvw
  refine ⟨f, (support_incidence f v).mpr hfv, ?_⟩
  rw [support_at_point]
  exact lt_add_of_pos_left _ (div_pos (eval_pos_of_certificate _ hfw) (chartValue_pos w))

theorem point_injective : Function.Injective point :=
  separatingSupports_injective point support offset support_separation

def polytope : ConvexPolytope 4 :=
  polytopeOfSeparatingSupports point (by decide) support offset support_bound support_separation

@[simp] theorem polytope_vertices : polytope.vertices = Finset.univ.image point := rfl

theorem polytope_card : polytope.vertices.card = 17 :=
  polytopeOfSeparatingSupports_card point (by decide) support offset support_bound support_separation

theorem point_mem_vertices (v : Fin 17) : point v ∈ polytope.vertices := by
  classical
  rw [polytope_vertices]
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

theorem point_zero : point 0 = 0 := by
  ext i
  fin_cases i <;>
    norm_num [point, homogeneous, chartValue, SeventeenData.vertices,
      SeventeenData.chartValues, QuadInt.eval]

theorem point_one : point 1 = WithLp.toLp 2 ![-1, 0, 0, 0] := by
  ext i
  fin_cases i <;>
    norm_num [point, homogeneous, chartValue, SeventeenData.vertices,
      SeventeenData.chartValues, QuadInt.eval]

theorem point_two : point 2 = WithLp.toLp 2 ![0, -1, 0, 0] := by
  ext i
  fin_cases i <;>
    norm_num [point, homogeneous, chartValue, SeventeenData.vertices,
      SeventeenData.chartValues, QuadInt.eval]

theorem point_three : point 3 = WithLp.toLp 2 ![0, 0, 1, 0] := by
  ext i
  fin_cases i <;>
    norm_num [point, homogeneous, chartValue, SeventeenData.vertices,
      SeventeenData.chartValues, QuadInt.eval]

def axis (i : Fin 4) : E 4 := WithLp.toLp 2 (fun j => if j = i then 1 else 0)

theorem fourth_axis_identity : axis 3 =
    chartValue 7 • point 7 + (5 : ℝ) • point 1 + (4 : ℝ) • point 2 - (16 : ℝ) • point 3 := by
  rw [point_one, point_two, point_three]
  have hc := ne_of_gt (chartValue_pos 7)
  ext i
  fin_cases i <;>
    norm_num [axis, point_apply, homogeneous, SeventeenData.vertices, QuadInt.eval]
  all_goals field_simp
  all_goals ring

/-- The exact construction spans all four affine coordinate directions. -/
theorem polytope_fullDim : polytope.IsFullDim := by
  let W := vectorSpan ℝ polytope.toSet
  have hm (v : Fin 17) : point v ∈ W := by
    change point v ∈ vectorSpan ℝ (convexHull ℝ (polytope.vertices : Set (E 4)))
    have h := vsub_mem_vectorSpan ℝ
      (subset_convexHull ℝ _ (point_mem_vertices v))
      (subset_convexHull ℝ _ (point_mem_vertices 0))
    simpa only [point_zero, vsub_eq_sub, sub_zero] using h
  have ha0 : axis 0 ∈ W := by
    have h : axis 0 = -point 1 := by
      rw [point_one]
      ext i
      fin_cases i <;> norm_num [axis]
    rw [h]
    exact W.neg_mem (hm 1)
  have ha1 : axis 1 ∈ W := by
    have h : axis 1 = -point 2 := by
      rw [point_two]
      ext i
      fin_cases i <;> norm_num [axis]
    rw [h]
    exact W.neg_mem (hm 2)
  have ha2 : axis 2 ∈ W := by
    have h : axis 2 = point 3 := by
      rw [point_three]
      ext i
      fin_cases i <;> norm_num [axis]
    rw [h]
    exact hm 3
  have ha3 : axis 3 ∈ W := by
    rw [fourth_axis_identity]
    exact W.sub_mem
      (W.add_mem (W.add_mem (W.smul_mem _ (hm 7)) (W.smul_mem _ (hm 1)))
        (W.smul_mem _ (hm 2))) (W.smul_mem _ (hm 3))
  have hall : ∀ i : Fin 4, axis i ∈ W := by
    intro i
    fin_cases i <;> assumption
  have htop : W = ⊤ := by
    apply top_unique
    intro x _
    have hx : x = ∑ i : Fin 4, x i • axis i := by
      ext j
      fin_cases j <;> simp [axis, Fin.sum_univ_succ]
    rw [hx]
    exact W.sum_mem (fun i _ => W.smul_mem _ (hall i))
  change Module.finrank ℝ W = 4
  rw [htop, finrank_top]
  exact finrank_euclideanSpace_fin

def face (f : Fin 23) : Set (E 4) := minimumFace polytope (support f) (offset f)

theorem point_mem_face_iff (f : Fin 23) (v : Fin 17) :
    point v ∈ face f ↔ SeventeenData.values f v = (0, 0) := by
  change (point v ∈ polytope.toSet ∧ support f (point v) = offset f) ↔ _
  have hv : point v ∈ polytope.toSet :=
    subset_convexHull ℝ _ (point_mem_vertices v)
  rw [support_incidence, and_iff_right hv]

theorem face_isFace (f : Fin 23)
    (hne : ∃ v, SeventeenData.values f v = (0, 0)) : polytope.IsFace (face f) := by
  apply minimumFace_isFace
  · intro x hx
    rw [polytope_vertices] at hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact support_bound f v
  · obtain ⟨v, hv⟩ := hne
    exact ⟨point v, point_mem_vertices v, (support_incidence f v).mpr hv⟩

theorem eval_mem_subfield (K : Subfield ℝ) (hphi : phi ∈ K) (x : QuadInt) :
    QuadInt.eval x ∈ K :=
  K.add_mem (K.intCast_mem x.1) (K.mul_mem (K.intCast_mem x.2) hphi)

theorem point_coordinates_in (K : Subfield ℝ) (hphi : phi ∈ K)
    (v : Fin 17) (i : Fin 4) : point v i ∈ K := by
  exact K.div_mem (eval_mem_subfield K hphi _) (eval_mem_subfield K hphi _)

theorem coordinates_in_of_sqrt_five (K : Subfield ℝ) (hsqrt : Real.sqrt 5 ∈ K) :
    CoordinatesIn K polytope := by
  have hphi : phi ∈ K := K.div_mem (K.add_mem K.one_mem hsqrt) (by norm_num)
  intro x hx i
  rw [polytope_vertices] at hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact point_coordinates_in K hphi v i

/-- The construction side of Theorem 1, with the actual convex-polytope
definition and its ordinary face poset.  The converse is a separate theorem. -/
theorem realizable_of_sqrt_five (K : Subfield ℝ) (hsqrt : Real.sqrt 5 ∈ K) :
    RealizableOver polytope K :=
  ⟨polytope, CombinatoriallyEquivalent.refl polytope, coordinates_in_of_sqrt_five K hsqrt⟩

end Papers.Nonrational.Seventeen

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/SeventeenChart.lean -/




@[expose] public section

/-! The positive affine chart preserves the exact homogeneous face ranks. -/

noncomputable section
namespace Papers.Nonrational.Seventeen
open Set Module
open Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification

def chartEquiv : (E 4 × ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun z := ![z.2 + z.1 0 + z.1 1 - z.1 2, z.1 0, z.1 1, z.1 2, z.1 3]
  invFun w := (WithLp.toLp 2 (fun i : Fin 4 => w i.succ), w 0 - w 1 - w 2 + w 3)
  left_inv z := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · dsimp
      ring
  right_inv w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

theorem chartEquiv_homogenize (v : Fin 17) :
    chartEquiv (homogenize (K := ℝ) (point v)) = (chartValue v)⁻¹ • homogeneous v := by
  have hc := ne_of_gt (chartValue_pos v)
  ext i
  fin_cases i
  · change 1 + homogeneous v 1 / chartValue v + homogeneous v 2 / chartValue v -
      homogeneous v 3 / chartValue v = (chartValue v)⁻¹ * homogeneous v 0
    field_simp
    linear_combination chart_identity v
  all_goals simp [chartEquiv, homogenize, point_apply, div_eq_mul_inv, mul_comm]

theorem chart_map_homogeneousSpan (S : Set (Fin 17)) :
    Submodule.map chartEquiv.toLinearMap (homogeneousSpan (K := ℝ) (point '' S)) =
      Submodule.span ℝ (homogeneous '' S) := by
  rw [homogeneousSpan, Submodule.map_span]
  simp only [Set.image_image, LinearEquiv.coe_coe]
  simp_rw [chartEquiv_homogenize]
  exact span_scaled_image homogeneous (fun v => (chartValue v)⁻¹) S
    (fun v _ => inv_ne_zero (ne_of_gt (chartValue_pos v)))

theorem finrank_homogeneousSpan_points (S : Set (Fin 17)) :
    finrank ℝ (homogeneousSpan (K := ℝ) (point '' S)) =
      finrank ℝ (Submodule.span ℝ (homogeneous '' S)) := by
  rw [← chart_map_homogeneousSpan S]
  exact (chartEquiv.finrank_map_eq _).symm

end Papers.Nonrational.Seventeen

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/QuadraticDeterminants.lean -/




@[expose] public section

/-! Small exact determinants for the supplied homogeneous face coordinates. -/

namespace Papers.Nonrational.QuadInt

def det2 (M : Fin 2 → Fin 2 → QuadInt) : QuadInt :=
  add (mul (M 0 0) (M 1 1)) (neg (mul (M 0 1) (M 1 0)))

def det3 (M : Fin 3 → Fin 3 → QuadInt) : QuadInt :=
  add (mul (M 0 0) (det2 (fun i j => M i.succ ((0 : Fin 3).succAbove j))))
    (add (neg (mul (M 0 1) (det2 (fun i j => M i.succ ((1 : Fin 3).succAbove j)))))
      (mul (M 0 2) (det2 (fun i j => M i.succ ((2 : Fin 3).succAbove j)))))

def det4 (M : Fin 4 → Fin 4 → QuadInt) : QuadInt :=
  add (mul (M 0 0) (det3 (fun i j => M i.succ ((0 : Fin 4).succAbove j))))
    (add (neg (mul (M 0 1) (det3 (fun i j => M i.succ ((1 : Fin 4).succAbove j)))))
      (add (mul (M 0 2) (det3 (fun i j => M i.succ ((2 : Fin 4).succAbove j))))
        (neg (mul (M 0 3) (det3 (fun i j => M i.succ ((3 : Fin 4).succAbove j)))))))

theorem eval_det2 (M : Fin 2 → Fin 2 → QuadInt) :
    eval (det2 M) = Matrix.det (Matrix.of (fun i j => eval (M i j))) := by
  simp [det2, Matrix.det_fin_two, sub_eq_add_neg]

theorem eval_det3 (M : Fin 3 → Fin 3 → QuadInt) :
    eval (det3 M) = Matrix.det (Matrix.of (fun i j => eval (M i j))) := by
  simp [det3, eval_det2, Matrix.det_fin_two, Matrix.det_fin_three,
    Fin.succAbove, Fin.lt_def, -Fin.val_fin_lt] <;> ring

theorem eval_det4 (M : Fin 4 → Fin 4 → QuadInt) :
    eval (det4 M) = Matrix.det (Matrix.of (fun i j => eval (M i j))) := by
  simp only [det4, eval_add, eval_mul, eval_neg, eval_det3]
  rw [Matrix.det_succ_row_zero (n := 3)]
  simp [Fin.sum_univ_succ, Matrix.of_apply, Matrix.submatrix] <;> ring

def combine3 (a : Fin 3 → QuadInt) (p : Fin 3 → Fin 5 → QuadInt) : Fin 5 → QuadInt :=
  fun j => add (mul (a 0) (p 0 j)) (add (mul (a 1) (p 1 j)) (mul (a 2) (p 2 j)))

def combine4 (a : Fin 4 → QuadInt) (p : Fin 4 → Fin 5 → QuadInt) : Fin 5 → QuadInt :=
  fun j => add (mul (a 0) (p 0 j)) (add (mul (a 1) (p 1 j))
    (add (mul (a 2) (p 2 j)) (mul (a 3) (p 3 j))))

theorem eval_combine3 (a : Fin 3 → QuadInt) (p : Fin 3 → Fin 5 → QuadInt) (j : Fin 5) :
    eval (combine3 a p j) = ∑ i : Fin 3, eval (a i) * eval (p i j) := by
  simp [combine3, Fin.sum_univ_succ]

theorem eval_combine4 (a : Fin 4 → QuadInt) (p : Fin 4 → Fin 5 → QuadInt) (j : Fin 5) :
    eval (combine4 a p j) = ∑ i : Fin 4, eval (a i) * eval (p i j) := by
  simp [combine4, Fin.sum_univ_succ]

end Papers.Nonrational.QuadInt

end
end BundlePart4

section BundlePart5
/- Source: Papers/SeventeenRankData.lean -/




@[expose] public section

/-! Exact face ranks: all finite arithmetic identities are checked by `decide`. -/
namespace Papers.Nonrational.SeventeenRankData
open QuadInt SeventeenData
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def faceForms : Fin 21 → Fin 5 → QuadInt :=
  ![![(0, 0), (0, 0), (-1, 0), (3, 0), (-44, 0)], ![(1, 1), (-1, -1), (-1, 0), (0, 0), (9, 11)], ![(0, 0), (1, -1), (-3, 0), (3, 0), (-15, -6)], ![(3, 0), (-1, 0), (0, 0), (0, 0), (39, -12)], ![(0, 0), (1, -1), (-1, 0), (2, 0), (-41, 11)], ![(0, 2), (-1, -2), (-2, -1), (1, 0), (14, 14)], ![(1, 0), (0, 0), (0, 0), (1, 0), (17, 6)], ![(-1, 2), (-1, -2), (-1, -2), (2, 0), (5, 12)], ![(2, 1), (0, -1), (-1, 0), (0, 0), (19, 25)], ![(-1, 1), (2, -3), (-2, -1), (3, 0), (-33, 26)], ![(0, 0), (1, -1), (-1, 0), (1, 0), (-24, 11)], ![(0, 0), (1, -1), (-1, 0), (1, 0), (-13, 8)], ![(0, 0), (0, 0), (0, 0), (1, 0), (-16, 0)], ![(0, 0), (0, 0), (0, 0), (1, 0), (6, 0)], ![(1, 0), (0, 0), (0, 0), (0, 0), (15, -4)], ![(1, 0), (0, 0), (0, 0), (0, 0), (17, 0)], ![(0, 0), (0, 0), (-1, 0), (1, 0), (-6, 0)], ![(1, 0), (-1, 0), (0, 0), (0, 0), (-1, 6)], ![(0, 0), (2, -2), (-2, 0), (2, 0), (-37, 19)], ![(0, 0), (0, 0), (0, 0), (2, 0), (-10, 0)], ![(2, 0), (0, 0), (0, 0), (0, 0), (32, -4)]]

def faceValues : Fin 21 → Fin 17 → QuadInt :=
  ![![(0, 0), (0, 0), (1, 0), (3, 0), (2, 0), (0, 2), (-1, 1), (0, 0), (0, 0), (3, 0), (5, 0), (3, -1), (3, 0), (66, 0), (65, 0), (62, -1), (59, 0)], ![(1, 1), (1, 1), (1, 0), (0, 0), (0, 1), (1, 0), (-1, 1), (0, 0), (0, 0), (-9, 10), (-10, 10), (1, 0), (0, 0), (0, 0), (0, 1), (2, 14), (1, 14)], ![(0, 0), (-1, 1), (3, 0), (3, 0), (0, 0), (-1, 1), (-2, 2), (26, -11), (27, -12), (0, 0), (0, 0), (35, -19), (35, -17), (57, -6), (53, -5), (-6, 12), (-8, 14)], ![(3, 0), (1, 0), (0, 0), (0, 0), (3, 0), (1, 0), (2, 0), (52, -30), (54, -30), (0, 0), (0, 0), (65, -32), (64, -30), (-18, 30), (-17, 30), (21, 12), (20, 12)], ![(0, 0), (-1, 1), (1, 0), (2, 0), (1, 0), (-1, 2), (0, 0), (-8, 6), (-7, 5), (-20, 17), (-19, 17), (0, 0), (0, 0), (69, -23), (67, -22), (39, -3), (38, -3)], ![(0, 2), (1, 2), (2, 1), (1, 0), (-1, 1), (0, 0), (-2, 2), (5, 0), (4, 0), (22, -9), (21, -10), (0, 0), (0, 0), (0, 0), (-1, 1), (-25, 20), (-26, 21)], ![(1, 0), (0, 0), (0, 0), (1, 0), (2, 0), (0, 1), (1, 0), (39, 0), (40, 0), (22, 10), (23, 10), (46, -1), (46, 0), (0, 0), (0, 0), (11, -6), (10, -6)], ![(-1, 2), (1, 2), (1, 2), (2, 0), (0, 0), (-1, 1), (-1, 1), (10, 0), (8, 0), (61, -28), (62, -30), (-1, 1), (0, 0), (0, 0), (0, 0), (-8, 7), (-9, 8)], ![(2, 1), (0, 1), (1, 0), (0, 0), (1, 1), (0, 0), (1, 1), (21, 8), (23, 8), (-20, 28), (-21, 28), (33, 6), (33, 8), (13, -8), (12, -7), (0, 0), (0, 0)], ![(-1, 1), (-2, 3), (2, 1), (3, 0), (0, 0), (-3, 3), (0, 0), (5, 13), (6, 11), (8, 16), (9, 15), (13, 2), (14, 1), (78, -47), (74, -45), (0, 0), (0, 0)], ![(0, 0), (-1, 1), (1, 0), (1, 0), (0, 0), (-1, 1), (0, 0), (-7, 6), (-6, 5), (-23, 17), (-23, 17), (0, 0), (0, 0), (46, -23), (44, -22), (11, -3), (11, -3)], ![(0, 0), (-1, 1), (1, 0), (1, 0), (0, 0), (-1, 1), (0, 0), (4, 3), (5, 2), (-12, 14), (-12, 14), (11, -3), (11, -3), (35, -20), (33, -19), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (1, 0), (1, 0), (0, 1), (0, 0), (0, 0), (0, 0), (4, 0), (5, 0), (1, 0), (1, 0), (22, 0), (22, 0), (27, 0), (26, 0)], ![(0, 0), (0, 0), (0, 0), (1, 0), (1, 0), (0, 1), (0, 0), (22, 0), (22, 0), (26, 0), (27, 0), (23, 0), (23, 0), (0, 0), (0, 0), (5, 0), (4, 0)], ![(1, 0), (0, 0), (0, 0), (0, 0), (1, 0), (0, 0), (1, 0), (21, -10), (22, -10), (0, 0), (0, 0), (27, -11), (27, -10), (-4, 10), (-4, 10), (2, 4), (2, 4)], ![(1, 0), (0, 0), (0, 0), (0, 0), (1, 0), (0, 0), (1, 0), (23, -6), (24, -6), (2, 4), (2, 4), (29, -7), (29, -6), (-6, 6), (-6, 6), (0, 0), (0, 0)], ![(0, 0), (0, 0), (1, 0), (1, 0), (0, 0), (0, 0), (-1, 1), (6, 0), (6, 0), (1, 0), (1, 0), (7, -1), (7, 0), (16, 0), (15, 0), (2, -1), (1, 0)], ![(1, 0), (1, 0), (0, 0), (0, 0), (1, 0), (1, 0), (0, 0), (0, 0), (0, 0), (-10, 10), (-10, 10), (1, 0), (0, 0), (0, 0), (1, 0), (27, -6), (26, -6)], ![(0, 0), (-2, 2), (2, 0), (2, 0), (0, 0), (-2, 2), (0, 0), (-3, 9), (-1, 7), (-35, 31), (-35, 31), (11, -3), (11, -3), (81, -43), (77, -41), (11, -3), (11, -3)], ![(0, 0), (0, 0), (0, 0), (2, 0), (2, 0), (0, 2), (0, 0), (22, 0), (22, 0), (30, 0), (32, 0), (24, 0), (24, 0), (22, 0), (22, 0), (32, 0), (30, 0)], ![(2, 0), (0, 0), (0, 0), (0, 0), (2, 0), (0, 0), (2, 0), (44, -16), (46, -16), (2, 4), (2, 4), (56, -18), (56, -16), (-10, 16), (-10, 16), (2, 4), (2, 4)]]

def faceVertices : Fin 21 → Finset (Fin 17) :=
  ![{0, 1, 7, 8}, {3, 7, 8, 12, 13}, {0, 4, 9, 10}, {2, 3, 9, 10}, {0, 6, 11, 12}, {5, 11, 12, 13}, {1, 2, 13, 14}, {4, 12, 13, 14}, {3, 5, 15, 16}, {4, 6, 15, 16}, {0, 4, 6, 11, 12}, {0, 4, 6, 15, 16}, {0, 1, 2, 6, 7, 8}, {0, 1, 2, 6, 13, 14}, {1, 2, 3, 5, 9, 10}, {1, 2, 3, 5, 15, 16}, {0, 1, 4, 5}, {2, 3, 6, 7, 8, 12, 13}, {0, 4, 6}, {0, 1, 2, 6}, {1, 2, 3, 5}]

theorem face_dot : ∀ f v, dot5 (faceForms f) (vertices v) = faceValues f v := by decide

theorem face_nonnegative : ∀ f v, faceValues f v = (0, 0) ∨
    positiveAt scale lo hi (faceValues f v) = true := by decide

theorem face_membership : ∀ f v, faceValues f v = (0, 0) ↔ v ∈ faceVertices f := by decide

theorem face_nonempty : ∀ f, (faceVertices f).Nonempty := by decide

def planeFace : Fin 14 → Fin 21 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 18, 19, 20]

def planeBasis : Fin 14 → Fin 3 → Fin 17 :=
  ![![0, 1, 7], ![3, 7, 8], ![0, 4, 9], ![2, 3, 9], ![0, 6, 11], ![5, 11, 12], ![1, 2, 13], ![4, 12, 13], ![3, 5, 15], ![4, 6, 15], ![0, 1, 4], ![0, 4, 6], ![0, 1, 2], ![1, 2, 3]]

def planeColumns : Fin 14 → Fin 3 → Fin 5 :=
  ![![1, 0, 2], ![1, 0, 3], ![0, 1, 2], ![0, 2, 3], ![0, 1, 2], ![1, 0, 2], ![0, 1, 2], ![1, 0, 2], ![0, 1, 3], ![1, 0, 2], ![1, 0, 2], ![1, 0, 2], ![0, 1, 2], ![1, 2, 3]]

def planeDelta : Fin 14 → QuadInt := ![(4, 0), (-1, 6), (6, 0), (15, -4), (-7, 11), (5, 15), (11, 6), (69, 138), (17, 0), (2, 8), (1, 0), (1, 0), (1, 0), (1, 0)]

def planeCoefficients : Fin 14 → Fin 17 → Fin 3 → QuadInt :=
  ![![![(4, 0), (0, 0), (0, 0)], ![(0, 0), (4, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (4, 0)], ![(4, 0), (-4, 0), (4, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(-1, 6), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (-1, 6), (0, 0)], ![(0, 0), (0, 0), (-1, 6)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(-1, 6), (5, -30), (-6, 36)], ![(-22, 132), (18, -108), (-17, 102)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(6, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (6, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (6, 0)], ![(-6, 0), (6, 0), (6, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(15, -4), (0, 0), (0, 0)], ![(0, 0), (15, -4), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (15, -4)], ![(-15, 4), (15, -4), (15, -4)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(-7, 11), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (-7, 11), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (-7, 11)], ![(7, -11), (4, 15), (-7, 11)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(5, 15), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (5, 15), (0, 0)], ![(0, 0), (0, 0), (5, 15)], ![(230, 115), (-230, -115), (225, 100)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(0, 0), (0, 0), (0, 0)], ![(11, 6), (0, 0), (0, 0)], ![(0, 0), (11, 6), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (11, 6)], ![(11, 6), (-11, -6), (11, 6)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(69, 138), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (69, 138), (0, 0)], ![(0, 0), (0, 0), (69, 138)], ![(69, 138), (-3, -6), (66, 132)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(17, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (17, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (17, 0)], ![(-17, 17), (-17, 0), (17, 0)]], ![![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(2, 8), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (2, 8), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (2, 8)], ![(-2, -8), (2, 8), (2, 8)]], ![![(1, 0), (0, 0), (0, 0)], ![(0, 0), (1, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (1, 0)], ![(0, -1), (1, 0), (0, 1)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(1, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (1, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (1, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(1, 0), (0, 0), (0, 0)], ![(0, 0), (1, 0), (0, 0)], ![(0, 0), (0, 0), (1, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(1, 0), (-1, 0), (-1, 1)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]], ![![(0, 0), (0, 0), (0, 0)], ![(1, 0), (0, 0), (0, 0)], ![(0, 0), (1, 0), (0, 0)], ![(0, 0), (0, 0), (1, 0)], ![(0, 0), (0, 0), (0, 0)], ![(1, 0), (0, -1), (0, 1)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0)]]]

theorem plane_basis_mem : ∀ f i, planeBasis f i ∈ faceVertices (planeFace f) := by decide

theorem plane_minor : ∀ f,
    det3 (fun i j => vertices (planeBasis f i) (planeColumns f j)) = planeDelta f := by decide

theorem plane_delta_positive : ∀ f,
    positiveAt scale lo hi (planeDelta f) = true := by decide

theorem plane_spanning : ∀ f v, v ∈ faceVertices (planeFace f) → ∀ j,
    mul (planeDelta f) (vertices v j) =
      combine3 (planeCoefficients f v) (fun i => vertices (planeBasis f i)) j := by decide

def facetFace : Fin 7 → Fin 21 := ![10, 11, 12, 13, 14, 15, 17]

def facetBasis : Fin 7 → Fin 4 → Fin 17 :=
  ![![0, 4, 6, 11], ![0, 4, 6, 15], ![0, 1, 2, 7], ![0, 1, 2, 13], ![1, 2, 3, 9], ![1, 2, 3, 15], ![2, 3, 6, 7]]

def facetColumns : Fin 7 → Fin 4 → Fin 5 :=
  ![![1, 0, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 2, 3], ![1, 0, 2, 3]]

def facetDelta : Fin 7 → QuadInt := ![(24, -11), (13, -8), (16, 0), (6, 0), (15, -4), (17, 0), (-1, 6)]

def facetCoefficients : Fin 7 → Fin 17 → Fin 4 → QuadInt :=
  ![![![(24, -11), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (24, -11), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (24, -11), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (24, -11)], ![(-24, 11), (0, 0), (13, 2), (24, -11)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)]], ![![(13, -8), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (13, -8), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (13, -8), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (13, -8)], ![(0, 0), (-13, 8), (13, -8), (13, -8)]], ![![(16, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (16, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (16, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(16, 0), (-16, 0), (-16, 16), (0, 0)], ![(0, 0), (0, 0), (0, 0), (16, 0)], ![(16, 0), (-16, 0), (0, 0), (16, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)]], ![![(6, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (6, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (6, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(6, 0), (-6, 0), (-6, 6), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (6, 0)], ![(0, 0), (6, 0), (-6, 0), (6, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)]], ![![(0, 0), (0, 0), (0, 0), (0, 0)], ![(15, -4), (0, 0), (0, 0), (0, 0)], ![(0, 0), (15, -4), (0, 0), (0, 0)], ![(0, 0), (0, 0), (15, -4), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(15, -4), (4, -11), (-4, 11), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (15, -4)], ![(0, 0), (-15, 4), (15, -4), (15, -4)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)]], ![![(0, 0), (0, 0), (0, 0), (0, 0)], ![(17, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (17, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (17, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(17, 0), (0, -17), (0, 17), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (17, 0)], ![(-17, 0), (0, 17), (-17, 0), (17, 0)]], ![![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(-1, 6), (0, 0), (0, 0), (0, 0)], ![(0, 0), (-1, 6), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (-1, 6), (0, 0)], ![(0, 0), (0, 0), (0, 0), (-1, 6)], ![(-7, 1), (0, 0), (-1, 6), (-1, 6)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(-42, 6), (-1, 6), (-6, 36), (-1, 6)], ![(-119, 17), (-22, 132), (-17, 102), (1, -6)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (0, 0)]]]

theorem facet_basis_mem : ∀ f i, facetBasis f i ∈ faceVertices (facetFace f) := by decide

theorem facet_minor : ∀ f,
    det4 (fun i j => vertices (facetBasis f i) (facetColumns f j)) = facetDelta f := by decide

theorem facet_delta_positive : ∀ f,
    positiveAt scale lo hi (facetDelta f) = true := by decide

theorem facet_spanning : ∀ f v, v ∈ faceVertices (facetFace f) → ∀ j,
    mul (facetDelta f) (vertices v j) =
      combine4 (facetCoefficients f v) (fun i => vertices (facetBasis f i)) j := by decide

end Papers.Nonrational.SeventeenRankData

end
end BundlePart5

section BundlePart6
/- Source: Papers/CoordinateRankCertificate.lean -/



@[expose] public section

/-! Exact rank certificates: a nonzero minor and explicit spanning relations. -/

noncomputable section
namespace Papers.Coordinates
open Set Submodule Module

variable {K : Type*} [Field K]

def selectCoordinates {d r : ℕ} (columns : Fin r → Fin d) :
    (Fin d → K) →ₗ[K] (Fin r → K) where
  toFun x := x ∘ columns
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem independent_of_minor {d r : ℕ} (p : Fin r → Fin d → K)
    (columns : Fin r → Fin d)
    (hdet : Matrix.det (Matrix.of (fun i j => p i (columns j))) ≠ 0) :
    LinearIndependent K p := by
  apply LinearIndependent.of_comp (selectCoordinates columns)
  exact Matrix.linearIndependent_rows_of_det_ne_zero hdet

theorem finrank_span_of_certificate {ι : Type*} {d r : ℕ}
    (p : ι → Fin d → K) (S : Set ι)
    (basis : Fin r → ι) (columns : Fin r → Fin d)
    (hb : ∀ i, basis i ∈ S)
    (Δ : K) (hΔ : Δ ≠ 0)
    (hdet : Matrix.det (Matrix.of (fun i j => p (basis i) (columns j))) = Δ)
    (a : ι → Fin r → K)
    (hspan : ∀ v ∈ S, Δ • p v = ∑ i : Fin r, a v i • p (basis i)) :
    finrank K (Submodule.span K (p '' S)) = r := by
  let q : Fin r → Fin d → K := p ∘ basis
  have hq : LinearIndependent K q := independent_of_minor q columns (by
    change Matrix.det (Matrix.of (fun i j => p (basis i) (columns j))) ≠ 0
    rw [hdet]
    exact hΔ)
  have heq : Submodule.span K (p '' S) = Submodule.span K (Set.range q) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      apply (Submodule.smul_mem_iff _ hΔ).mp
      rw [hspan v hv]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i)))
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact Set.mem_image_of_mem p (hb i)
  rw [heq, finrank_span_eq_card hq, Fintype.card_fin]

end Papers.Coordinates

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/SeventeenFaceRanks.lean -/





@[expose] public section

/-! Certified ranks and dimensions of the faces used in reconstruction. -/

noncomputable section
namespace Papers.Nonrational.Seventeen
open Set Module
open Papers.Coordinates Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open SeventeenRankData

theorem plane_raw_rank (f : Fin 14) :
    finrank ℝ (Submodule.span ℝ (homogeneous '' (faceVertices (planeFace f) : Set (Fin 17)))) = 3 := by
  apply finrank_span_of_certificate homogeneous (faceVertices (planeFace f))
    (planeBasis f) (planeColumns f) (plane_basis_mem f)
    (QuadInt.eval (planeDelta f))
    (ne_of_gt (eval_pos_of_certificate _ (plane_delta_positive f)))
    (a := fun v i => QuadInt.eval (planeCoefficients f v i))
  · change Matrix.det (Matrix.of (fun i j =>
      QuadInt.eval (SeventeenData.vertices (planeBasis f i) (planeColumns f j)))) = _
    rw [← QuadInt.eval_det3, plane_minor]
  · intro v hv
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    change QuadInt.eval (planeDelta f) * QuadInt.eval (SeventeenData.vertices v j) = _
    rw [← QuadInt.eval_mul, plane_spanning f v hv j, QuadInt.eval_combine3]
    rfl

theorem facet_raw_rank (f : Fin 7) :
    finrank ℝ (Submodule.span ℝ (homogeneous '' (faceVertices (facetFace f) : Set (Fin 17)))) = 4 := by
  apply finrank_span_of_certificate homogeneous (faceVertices (facetFace f))
    (facetBasis f) (facetColumns f) (facet_basis_mem f)
    (QuadInt.eval (facetDelta f))
    (ne_of_gt (eval_pos_of_certificate _ (facet_delta_positive f)))
    (a := fun v i => QuadInt.eval (facetCoefficients f v i))
  · change Matrix.det (Matrix.of (fun i j =>
      QuadInt.eval (SeventeenData.vertices (facetBasis f i) (facetColumns f j)))) = _
    rw [← QuadInt.eval_det4, facet_minor]
  · intro v hv
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    change QuadInt.eval (facetDelta f) * QuadInt.eval (SeventeenData.vertices v j) = _
    rw [← QuadInt.eval_mul, facet_spanning f v hv j, QuadInt.eval_combine4]
    rfl

def faceCoefficient (f : Fin 21) (i : Fin 5) : ℝ := QuadInt.eval (faceForms f i)
def faceValue (f : Fin 21) (v : Fin 17) : ℝ := QuadInt.eval (faceValues f v)
def faceOffset (f : Fin 21) : ℝ := -faceCoefficient f 0

def faceSupport (f : Fin 21) : E 4 →L[ℝ] ℝ :=
  (faceCoefficient f 0 + faceCoefficient f 1) • coordinate 0 +
  (faceCoefficient f 0 + faceCoefficient f 2) • coordinate 1 +
  (faceCoefficient f 3 - faceCoefficient f 0) • coordinate 2 +
  faceCoefficient f 4 • coordinate 3

theorem faceValue_nonneg (f : Fin 21) (v : Fin 17) : 0 ≤ faceValue f v := by
  rcases face_nonnegative f v with h | h
  · simp [faceValue, h]
  · exact (eval_pos_of_certificate _ h).le

theorem faceSupport_at_point (f : Fin 21) (v : Fin 17) :
    faceSupport f (point v) = faceValue f v / chartValue v + faceOffset f := by
  have hval : faceValue f v = ∑ i : Fin 5, faceCoefficient f i * homogeneous v i := by
    rw [faceValue, ← face_dot, QuadInt.eval_dot5]
    rfl
  rw [hval]
  simp only [faceSupport, map_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, coordinate_apply, smul_eq_mul, point_apply,
    Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
    show (2 : Fin 4).succ = (3 : Fin 5) from rfl,
    show (3 : Fin 4).succ = (4 : Fin 5) from rfl]
  dsimp only [faceOffset]
  have hc := ne_of_gt (chartValue_pos v)
  field_simp
  linear_combination faceCoefficient f 0 * chart_identity v

theorem faceSupport_bound (f : Fin 21) (v : Fin 17) :
    faceOffset f ≤ faceSupport f (point v) := by
  rw [faceSupport_at_point]
  exact le_add_of_nonneg_left (div_nonneg (faceValue_nonneg f v) (chartValue_pos v).le)

theorem faceSupport_incidence (f : Fin 21) (v : Fin 17) :
    faceSupport f (point v) = faceOffset f ↔ v ∈ faceVertices f := by
  rw [← face_membership]
  constructor
  · intro h
    rcases face_nonnegative f v with hz | hp
    · exact hz
    · have hpos : 0 < faceValue f v := eval_pos_of_certificate _ hp
      have hdiv := div_pos hpos (chartValue_pos v)
      rw [faceSupport_at_point] at h
      linarith
  · intro h
    rw [faceSupport_at_point]
    simp [faceValue, h]

def reconstructionFaceSet (f : Fin 21) : Set (E 4) :=
  minimumFace polytope (faceSupport f) (faceOffset f)

theorem reconstructionFaceSet_isFace (f : Fin 21) :
    polytope.IsFace (reconstructionFaceSet f) := by
  apply minimumFace_isFace
  · intro x hx
    rw [polytope_vertices] at hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact faceSupport_bound f v
  · obtain ⟨v, hv⟩ := face_nonempty f
    exact ⟨point v, point_mem_vertices v, (faceSupport_incidence f v).mpr hv⟩

def reconstructionFace (f : Fin 21) : FaceType polytope :=
  ⟨reconstructionFaceSet f, reconstructionFaceSet_isFace f⟩

theorem point_mem_reconstructionFace (f : Fin 21) (v : Fin 17) :
    point v ∈ (reconstructionFace f).val ↔ v ∈ faceVertices f := by
  change (point v ∈ polytope.toSet ∧ faceSupport f (point v) = faceOffset f) ↔ _
  rw [faceSupport_incidence, and_iff_right (vertex_mem_body polytope (point_mem_vertices v))]

theorem reconstructionFace_eq_hull (f : Fin 21) :
    (reconstructionFace f).val = convexHull ℝ (point '' (faceVertices f : Set (Fin 17))) := by
  classical
  rw [face_eq_hull_vertices polytope (reconstructionFace f).property]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter, polytope_vertices, Finset.mem_image,
    Finset.mem_univ, true_and, Set.mem_image]
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, (point_mem_reconstructionFace f v).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, (point_mem_reconstructionFace f v).mpr hv⟩

theorem face_homogeneous_rank (f : Fin 21) :
    finrank ℝ (homogeneousSpan (K := ℝ) (reconstructionFace f).val) =
      finrank ℝ (Submodule.span ℝ (homogeneous '' (faceVertices f : Set (Fin 17)))) := by
  rw [reconstructionFace_eq_hull,
    homogeneousSpan_convexHull _ (Set.Nonempty.image _ (face_nonempty f)),
    finrank_homogeneousSpan_points]

theorem plane_face_dimension (f : Fin 14) : faceDim (reconstructionFace (planeFace f)).val = 2 := by
  have h := face_homogeneous_rank (planeFace f)
  rw [plane_raw_rank, finrank_homogeneousSpan (reconstructionFace (planeFace f)).property.2] at h
  change finrank ℝ (vectorSpan ℝ (reconstructionFace (planeFace f)).val) = 2
  omega

theorem facet_face_dimension (f : Fin 7) : faceDim (reconstructionFace (facetFace f)).val = 3 := by
  have h := face_homogeneous_rank (facetFace f)
  rw [facet_raw_rank, finrank_homogeneousSpan (reconstructionFace (facetFace f)).property.2] at h
  change finrank ℝ (vectorSpan ℝ (reconstructionFace (facetFace f)).val) = 3
  omega

end Papers.Nonrational.Seventeen

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/SeventeenRealization.lean -/




@[expose] public section

/-!
# Coordinates in an arbitrary realization

Every rank and exclusion below is derived from an ordinary face-poset
isomorphism. No projective incidence data are added to that isomorphism.
-/

noncomputable section
namespace Papers.Nonrational.Seventeen
open Set Module
open Papers.Coordinates Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open SeventeenRankData

def labelledVertex (v : Fin 17) : VertexType polytope := ⟨point v, point_mem_vertices v⟩

theorem labelledVertex_bijective : Function.Bijective labelledVertex := by
  constructor
  · intro v w h
    exact point_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    rw [polytope_vertices] at hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨v, rfl⟩

def labelEquiv : Fin 17 ≃ VertexType polytope := Equiv.ofBijective labelledVertex labelledVertex_bijective

variable {Q : ConvexPolytope 4} (φ : FaceType polytope ≃o FaceType Q)

def realizationVertex (v : Fin 17) : VertexType Q := imageVertex φ (labelledVertex v)
def realizationPoint (v : Fin 17) : E 4 := (realizationVertex φ v).val

theorem realizationVertex_bijective : Function.Bijective (realizationVertex φ) :=
  (vertexEquivOfFaceOrder φ).bijective.comp labelledVertex_bijective

theorem realizationPoint_injective : Function.Injective (realizationPoint φ) := by
  intro v w h
  exact (realizationVertex_bijective φ).1 (Subtype.ext h)

theorem realizationPoint_mem_face (f : Fin 21) (v : Fin 17) :
    realizationPoint φ v ∈ (φ (reconstructionFace f)).val ↔ v ∈ faceVertices f := by
  exact (imageVertex_mem_iff φ (labelledVertex v) (reconstructionFace f)).trans
    (point_mem_reconstructionFace f v)

theorem realizationFace_eq_hull (f : Fin 21) :
    (φ (reconstructionFace f)).val =
      convexHull ℝ (realizationPoint φ '' (faceVertices f : Set (Fin 17))) := by
  classical
  rw [face_eq_hull_vertices Q (φ (reconstructionFace f)).property]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_image]
  constructor
  · rintro ⟨hx, hxf⟩
    obtain ⟨v, hv⟩ := (realizationVertex_bijective φ).2 ⟨x, hx⟩
    have hvx : realizationPoint φ v = x := congrArg Subtype.val hv
    refine ⟨v, ?_, hvx⟩
    exact (realizationPoint_mem_face φ f v).mp (hvx.symm ▸ hxf)
  · rintro ⟨v, hv, rfl⟩
    exact ⟨(realizationVertex φ v).property, (realizationPoint_mem_face φ f v).mpr hv⟩

def realizationHomogeneous (v : Fin 17) : Fin 5 → ℝ :=
  chartEquiv (homogenize (K := ℝ) (realizationPoint φ v))

theorem realization_homogeneous_span (f : Fin 21) :
    Submodule.span ℝ (realizationHomogeneous φ '' (faceVertices f : Set (Fin 17))) =
      Submodule.map chartEquiv.toLinearMap
        (homogeneousSpan (K := ℝ) (φ (reconstructionFace f)).val) := by
  rw [realizationFace_eq_hull,
    homogeneousSpan_convexHull _ (Set.Nonempty.image _ (face_nonempty f)),
    homogeneousSpan, Submodule.map_span]
  simp only [Set.image_image, LinearEquiv.coe_coe, realizationHomogeneous]
  rfl

theorem realization_homogeneous_rank (f : Fin 21) :
    finrank ℝ (Submodule.span ℝ
      (realizationHomogeneous φ '' (faceVertices f : Set (Fin 17)))) =
      faceDim (reconstructionFace f).val + 1 := by
  rw [realization_homogeneous_span, chartEquiv.finrank_map_eq,
    finrank_homogeneousSpan (φ (reconstructionFace f)).property.2]
  change faceDim (φ (reconstructionFace f)).val + 1 = _
  rw [faceOrderIso_dimension]

theorem realization_homogeneous_triples (i j k : Fin 17)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    LinearIndependent ℝ ![realizationHomogeneous φ i,
      realizationHomogeneous φ j, realizationHomogeneous φ k] := by
  have hnc := vertices_not_collinear Q
    (realizationVertex φ i).property (realizationVertex φ j).property
    (realizationVertex φ k).property
    (fun h => hij (realizationPoint_injective φ h))
    (fun h => hik (realizationPoint_injective φ h))
    (fun h => hjk (realizationPoint_injective φ h))
  have ha := affineIndependent_iff_not_collinear_set.mpr hnc
  have hi := (linearIndependent_homogenize_iff _).mpr ha
  have hm := hi.map' chartEquiv.toLinearMap (LinearMap.ker_eq_bot.mpr chartEquiv.injective)
  convert hm using 1
  ext a
  fin_cases a <;> rfl

theorem realization_homogeneous_notMem_span (f : Fin 21) (v : Fin 17)
    (hv : v ∉ faceVertices f) :
    realizationHomogeneous φ v ∉ Submodule.span ℝ
      (realizationHomogeneous φ '' (faceVertices f : Set (Fin 17))) := by
  intro h
  rw [realization_homogeneous_span] at h
  obtain ⟨z, hz, heq⟩ := h
  have hzeq : z = homogenize (K := ℝ) (realizationPoint φ v) := chartEquiv.injective heq
  rw [hzeq] at hz
  have haf := (homogenize_mem_span_iff (φ (reconstructionFace f)).property.2 _).mp hz
  exact vertex_notMem_affineSpan_face Q (φ (reconstructionFace f)).property
    (realizationVertex φ v).property
    (fun hm => hv ((realizationPoint_mem_face φ f v).mp hm)) haf

variable (K : Subfield ℝ) (hK : CoordinatesIn K Q)

include hK in
theorem realizationHomogeneous_mem (v : Fin 17) (i : Fin 5) :
    realizationHomogeneous φ v i ∈ K := by
  have hm (j : Fin 4) : realizationPoint φ v j ∈ K :=
    hK _ (realizationVertex φ v).property j
  fin_cases i
  · exact K.sub_mem (K.add_mem (K.add_mem K.one_mem (hm 0)) (hm 1)) (hm 2)
  all_goals exact hm _

def fieldPoint (v : Fin 17) (i : Fin 5) : K :=
  ⟨realizationHomogeneous φ v i, realizationHomogeneous_mem φ K hK v i⟩

@[simp] theorem coordinateMap_fieldPoint (v : Fin 17) :
    coordinateMap K.subtype 5 (fieldPoint φ K hK v) = realizationHomogeneous φ v := rfl

def fieldFaceSpan (f : Fin 21) : Submodule K (Fin 5 → K) :=
  Submodule.span K (fieldPoint φ K hK '' (faceVertices f : Set (Fin 17)))

theorem fieldFaceSpan_rank (f : Fin 21) :
    finrank K (fieldFaceSpan φ K hK f) = faceDim (reconstructionFace f).val + 1 := by
  rw [fieldFaceSpan, ← finrank_span_coordinateMap K.subtype,
    Set.image_image]
  simp_rw [coordinateMap_fieldPoint]
  exact realization_homogeneous_rank φ f

theorem fieldPoint_triples (i j k : Fin 17) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    LinearIndependent K ![fieldPoint φ K hK i, fieldPoint φ K hK j, fieldPoint φ K hK k] := by
  apply linearIndependent_of_coordinate_map K.subtype
  convert realization_homogeneous_triples φ i j k hij hik hjk using 1
  ext a b
  fin_cases a <;> rfl

theorem fieldPoint_notMem_faceSpan (f : Fin 21) (v : Fin 17)
    (hv : v ∉ faceVertices f) : fieldPoint φ K hK v ∉ fieldFaceSpan φ K hK f := by
  intro h
  have hm := coordinateMap_mem_span K.subtype h
  simp only [Set.image_image, coordinateMap_fieldPoint] at hm
  exact realization_homogeneous_notMem_span φ f v hv hm

end Papers.Nonrational.Seventeen

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/NonrationalGolden.lean -/












@[expose] public section

/-!
# The arithmetic obstruction in the nonrational four-polytope paper

This file proves the quadratic field obstruction, including its converse.
The geometric reconstruction of the incidences is a separate dependency.
The normalized equations are not presented as a formalization of Theorem 1.
-/

namespace Papers.Nonrational

open Matrix

/-- Four homogeneous points in projective three-space are coplanar
exactly when their four representatives have zero determinant. -/
def Coplanar4 {K : Type*} [CommRing K] (a b c d : Fin 4 → K) : Prop :=
  Matrix.det (Matrix.of ![a, b, c, d]) = 0

theorem golden_equations {K : Type*} [CommRing K] (s t : K)
    (h₁ : s - t - 1 = 0) (h₂ : s * (1 - t) - t = 0) :
    t ^ 2 + t - 1 = 0 := by
  have hs : s = t + 1 := by linear_combination h₁
  rw [hs] at h₂
  linear_combination -h₂

theorem square_five_of_golden {K : Type*} [CommRing K] (t : K)
    (ht : t ^ 2 + t - 1 = 0) : (2 * t + 1) ^ 2 = 5 := by
  linear_combination 4 * ht

theorem sqrt_five_mem_of_square (K : Subfield ℝ) (a : ℝ)
    (ha : a ∈ K) (h : a ^ 2 = 5) : Real.sqrt 5 ∈ K := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have heq : a = Real.sqrt 5 ∨ a = -Real.sqrt 5 := by
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp (h.trans hs.symm)
  rcases heq with heq | heq
  · exact heq ▸ ha
  · have hn := K.neg_mem ha
    simpa only [heq, neg_neg] using hn

theorem sqrt_five_mem_of_golden (K : Subfield ℝ) (t : ℝ)
    (htK : t ∈ K) (ht : t ^ 2 + t - 1 = 0) : Real.sqrt 5 ∈ K := by
  apply sqrt_five_mem_of_square K (2 * t + 1)
  · exact K.add_mem (K.mul_mem (by norm_num) htK) K.one_mem
  · exact square_five_of_golden t ht

/-- The incidence obstruction is equivalent, over any real subfield,
to containing the quadratic irrational, with no positivity condition on the root. -/
theorem exists_golden_root_iff (K : Subfield ℝ) :
    (∃ t : ℝ, t ∈ K ∧ t ^ 2 + t - 1 = 0) ↔ Real.sqrt 5 ∈ K := by
  constructor
  · rintro ⟨t, htK, ht⟩
    exact sqrt_five_mem_of_golden K t htK ht
  · intro hs
    refine ⟨(Real.sqrt 5 - 1) / 2, K.div_mem (K.sub_mem hs K.one_mem) (by norm_num), ?_⟩
    have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith

theorem original_affine_equations (u v : ℝ)
    (h₁ : u * (v - 1) = 1) (h₂ : v * (u - 1) = 1) :
    u = v ∧ u ^ 2 - u - 1 = 0 ∧ (2 * u - 1) ^ 2 = 5 := by
  have huv : u = v := by nlinarith
  subst v
  constructor
  · rfl
  constructor <;> nlinarith

theorem original_affine_field_obstruction (K : Subfield ℝ) (u v : ℝ)
    (hu : u ∈ K) (h₁ : u * (v - 1) = 1) (h₂ : v * (u - 1) = 1) :
    Real.sqrt 5 ∈ K := by
  have h := original_affine_equations u v h₁ h₂
  exact sqrt_five_mem_of_square K (2 * u - 1)
    (K.sub_mem (K.mul_mem (by norm_num) hu) K.one_mem) h.2.2

end Papers.Nonrational

end
end BundlePart9

section BundlePart10
/- Source: Papers/NonrationalIncidence.lean -/






@[expose] public section

/-!
# The projective golden configuration

The first part eliminates the arbitrary nonzero coordinate scales.  None of
these scales is assumed to be rational or equal to one.  This is the algebraic
step needed after choosing a projective basis in an arbitrary realization.
-/

noncomputable section

namespace Papers.Nonrational

section Elimination

variable {K : Type*} [Field K]

theorem coplanar_iff_dependent (a b c d : Fin 4 → K) :
    Coplanar4 a b c d ↔ ¬LinearIndependent K ![a, b, c, d] := by
  change Matrix.det (Matrix.of ![a, b, c, d]) = 0 ↔ _
  rw [← not_ne_iff]
  apply not_congr
  exact (Matrix.linearIndependent_row_iff.trans Matrix.nonsingular_iff_det_ne_zero).symm

theorem coplanar_linear_image (f : (Fin 4 → K) →ₗ[K] (Fin 4 → K))
    {a b c d : Fin 4 → K} (h : Coplanar4 a b c d) :
    Coplanar4 (f a) (f b) (f c) (f d) := by
  rw [coplanar_iff_dependent] at h ⊢
  intro hi
  apply h
  apply LinearIndependent.of_comp f
  convert hi using 1
  ext j
  fin_cases j <;> rfl

/-- The five determinant equations after placing 1,2,3,4 at the coordinate
points.  All unused coordinates retain their original field values. -/
theorem coordinate_incidence_equations
    (a b c d e f g h i u v w : K)
    (h1267 : Coplanar4 ![1, 0, 0, 0] ![0, 1, 0, 0]
      ![a, 0, b, c] ![0, d, e, f])
    (h2356 : Coplanar4 ![0, 1, 0, 0] ![0, 0, 1, 0]
      ![u, v, 0, w] ![a, 0, b, c])
    (h3458 : Coplanar4 ![0, 0, 1, 0] ![0, 0, 0, 1]
      ![u, v, 0, w] ![g, h, i, 0])
    (h4678 : Coplanar4 ![0, 0, 0, 1] ![a, 0, b, c]
      ![0, d, e, f] ![g, h, i, 0])
    (h1578 : Coplanar4 ![1, 0, 0, 0] ![u, v, 0, w]
      ![0, d, e, f] ![g, h, i, 0]) :
    (b * f - c * e = 0) ∧ (c * u - a * w = 0) ∧
    (h * u - g * v = 0) ∧ (a * d * i - a * e * h - b * d * g = 0) ∧
    (w * d * i - w * e * h - v * f * i = 0) := by
  simp [Coplanar4, Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
    Matrix.det_fin_two, Fin.sum_univ_succ, Fin.succAbove]
    at h1267 h2356 h3458 h4678 h1578
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h1267
  · linear_combination h2356
  · linear_combination h3458
  · linear_combination h4678
  · linear_combination h1578

/-- Eliminate the six remaining projective scales from the four incidence
equations.  The variables are the actual coordinates, not normalized values
postulated as additional hypotheses on a realization. -/
theorem incidence_scale_elimination
    (a b c d e f g h i u v w : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hg : g ≠ 0) (hu : u ≠ 0)
    (h1267 : b * f - c * e = 0)
    (h2356 : c * u - a * w = 0)
    (h3458 : h * u - g * v = 0)
    (h4678 : a * d * i - a * e * h - b * d * g = 0)
    (h1578 : w * d * i - w * e * h - v * f * i = 0) :
    let s := a * i / (b * g)
    let t := a * h * e / (b * d * g)
    s - t - 1 = 0 ∧ s * (1 - t) - t = 0 := by
  dsimp
  have hf : f = c * e / b := by
    apply (eq_div_iff hb).mpr
    linear_combination h1267
  have hw : w = c * u / a := by
    apply (eq_div_iff ha).mpr
    linear_combination -h2356
  have hv : v = h * u / g := by
    apply (eq_div_iff hg).mpr
    linear_combination -h3458
  have hcore : b * d * g * i - b * e * h * g - a * e * h * i = 0 := by
    have hraw := h1578
    rw [hw, hv, hf] at hraw
    field_simp at hraw
    have hprod : (c * u) * (b * d * g * i - b * e * h * g - a * e * h * i) = 0 := by
      linear_combination hraw
    exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hc hu)
  constructor
  · field_simp
    linear_combination h4678
  · field_simp
    linear_combination a * hcore

theorem incidence_scale_golden_root
    (a b c d e f g h i u v w : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hg : g ≠ 0) (hu : u ≠ 0)
    (h1267 : b * f - c * e = 0)
    (h2356 : c * u - a * w = 0)
    (h3458 : h * u - g * v = 0)
    (h4678 : a * d * i - a * e * h - b * d * g = 0)
    (h1578 : w * d * i - w * e * h - v * f * i = 0) :
    (a * h * e / (b * d * g)) ^ 2 + a * h * e / (b * d * g) - 1 = 0 := by
  have hs := incidence_scale_elimination a b c d e f g h i u v w
    ha hb hc hd hg hu h1267 h2356 h3458 h4678 h1578
  exact golden_equations _ _ hs.1 hs.2

/-- The virtual point's first coordinate cannot vanish: otherwise its
incidence with 2356 makes it proportional to point 2. -/
theorem virtual_first_coordinate_ne_zero
    (a c u v w : K) (ha : a ≠ 0) (h2356 : c * u - a * w = 0)
    (hnot2 : ∀ t : K, ![u, v, 0, w] ≠ t • ![0, 1, 0, 0]) : u ≠ 0 := by
  intro hu
  have hw : w = 0 := by
    have haw : a * w = 0 := by simpa [hu] using h2356.symm
    exact (mul_eq_zero.mp haw).resolve_left ha
  apply hnot2 v
  ext j
  fin_cases j <;> simp [hu, hw]

end Elimination

/-- The scale elimination produces an element of the actual realization
field; taking a square root outside that field is not used. -/
theorem incidence_scale_field_obstruction
    (K : Subfield ℝ) (a b c d e f g h i u v w : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hg : g ≠ 0) (hu : u ≠ 0)
    (h1267 : b * f - c * e = 0)
    (h2356 : c * u - a * w = 0)
    (h3458 : h * u - g * v = 0)
    (h4678 : a * d * i - a * e * h - b * d * g = 0)
    (h1578 : w * d * i - w * e * h - v * f * i = 0) :
    Real.sqrt 5 ∈ K := by
  have ht := incidence_scale_golden_root a b c d e f g h i u v w
    ha hb hc hd hg hu h1267 h2356 h3458 h4678 h1578
  exact sqrt_five_mem_of_golden K (a * h * e / (b * d * g) : K).val
    (a * h * e / (b * d * g) : K).property (by exact_mod_cast ht)

end Papers.Nonrational

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/GoldenConfiguration.lean -/




@[expose] public section

/-!
# The projective incidence lemma, with arbitrary coordinate frames

The seven labels are indexed as 1,2,3,4,6,7,8. The omitted fifth point is
supplied separately because it need not be a vertex. No diagonal
normalization or nonzero coordinate is postulated: these are derived from
the independence and noncollinearity hypotheses.
-/

noncomputable section
namespace Papers.Nonrational

variable {K : Type*} [Field K]

theorem independent_triple_not_combination {V : Type*} [AddCommGroup V] [Module K V]
    {x y z : V} (h : LinearIndependent K ![x, y, z]) (a b : K) :
    z ≠ a • x + b • y := by
  intro heq
  have hsum : ∑ i : Fin 3, ![a, b, -1] i • ![x, y, z] i = 0 := by
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    rw [heq]
    module
  have hz := (Fintype.linearIndependent_iff.mp h) ![a, b, -1] hsum 2
  norm_num at hz

def GoldenIncidences (p : Fin 7 → Fin 4 → K) (w : Fin 4 → K) : Prop :=
  Coplanar4 (p 0) (p 1) (p 2) (p 6) ∧
  Coplanar4 (p 0) (p 1) (p 3) w ∧
  Coplanar4 (p 0) (p 1) (p 4) (p 5) ∧
  Coplanar4 (p 0) (p 2) (p 3) (p 4) ∧
  Coplanar4 (p 0) w (p 5) (p 6) ∧
  Coplanar4 (p 1) (p 2) (p 3) (p 5) ∧
  Coplanar4 (p 1) (p 2) w (p 4) ∧
  Coplanar4 (p 2) (p 3) w (p 6) ∧
  Coplanar4 (p 3) (p 4) (p 5) (p 6)

def NoCollinearTriples (p : Fin 7 → Fin 4 → K) : Prop :=
  ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
    LinearIndependent K ![p i, p j, p k]

theorem normalized_golden_root
    (p6 p7 p8 w : Fin 4 → K)
    (h6a : LinearIndependent K ![![0,0,1,0], ![0,0,0,1], p6])
    (h6b : LinearIndependent K ![![1,0,0,0], ![0,0,0,1], p6])
    (h6c : LinearIndependent K ![![1,0,0,0], ![0,0,1,0], p6])
    (h7d : LinearIndependent K ![![0,0,1,0], ![0,0,0,1], p7])
    (h8g : LinearIndependent K ![![0,1,0,0], ![0,0,1,0], p8])
    (hw2 : ∀ t : K, w ≠ t • ![0,1,0,0])
    (h1238 : Coplanar4 ![1,0,0,0] ![0,1,0,0] ![0,0,1,0] p8)
    (h1245 : Coplanar4 ![1,0,0,0] ![0,1,0,0] ![0,0,0,1] w)
    (h1267 : Coplanar4 ![1,0,0,0] ![0,1,0,0] p6 p7)
    (h1346 : Coplanar4 ![1,0,0,0] ![0,0,1,0] ![0,0,0,1] p6)
    (h1578 : Coplanar4 ![1,0,0,0] w p7 p8)
    (h2347 : Coplanar4 ![0,1,0,0] ![0,0,1,0] ![0,0,0,1] p7)
    (h2356 : Coplanar4 ![0,1,0,0] ![0,0,1,0] w p6)
    (h3458 : Coplanar4 ![0,0,1,0] ![0,0,0,1] w p8)
    (h4678 : Coplanar4 ![0,0,0,1] p6 p7 p8) :
    ∃ t : K, t ^ 2 + t - 1 = 0 := by
  have h61 : p6 1 = 0 := by
    simpa [Coplanar4, Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
      Matrix.det_fin_two, Fin.sum_univ_succ, Fin.succAbove] using h1346
  have h70 : p7 0 = 0 := by
    simpa [Coplanar4, Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
      Matrix.det_fin_two, Fin.sum_univ_succ, Fin.succAbove] using h2347
  have h83 : p8 3 = 0 := by
    simpa [Coplanar4, Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
      Matrix.det_fin_two, Fin.sum_univ_succ, Fin.succAbove] using h1238
  have hw2zero : w 2 = 0 := by
    simpa [Coplanar4, Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
      Matrix.det_fin_two, Fin.sum_univ_succ, Fin.succAbove] using h1245
  have hp6 : p6 = ![p6 0, 0, p6 2, p6 3] := by
    ext j
    fin_cases j <;> simp [h61]
  have hp7 : p7 = ![0, p7 1, p7 2, p7 3] := by
    ext j
    fin_cases j <;> simp [h70]
  have hp8 : p8 = ![p8 0, p8 1, p8 2, 0] := by
    ext j
    fin_cases j <;> simp [h83]
  have hwp : w = ![w 0, w 1, 0, w 3] := by
    ext j
    fin_cases j <;> simp [hw2zero]
  have ha : p6 0 ≠ 0 := by
    intro h0
    apply independent_triple_not_combination h6a (p6 2) (p6 3)
    ext j
    fin_cases j <;> simp [h0, h61]
  have hb : p6 2 ≠ 0 := by
    intro h0
    apply independent_triple_not_combination h6b (p6 0) (p6 3)
    ext j
    fin_cases j <;> simp [h0, h61]
  have hc : p6 3 ≠ 0 := by
    intro h0
    apply independent_triple_not_combination h6c (p6 0) (p6 2)
    ext j
    fin_cases j <;> simp [h0, h61]
  have hd : p7 1 ≠ 0 := by
    intro h0
    apply independent_triple_not_combination h7d (p7 2) (p7 3)
    ext j
    fin_cases j <;> simp [h0, h70]
  have hg : p8 0 ≠ 0 := by
    intro h0
    apply independent_triple_not_combination h8g (p8 1) (p8 2)
    ext j
    fin_cases j <;> simp [h0, h83]
  have equations := coordinate_incidence_equations
    (p6 0) (p6 2) (p6 3) (p7 1) (p7 2) (p7 3)
    (p8 0) (p8 1) (p8 2) (w 0) (w 1) (w 3)
    (by simpa only [← hp6, ← hp7] using h1267)
    (by simpa only [← hwp, ← hp6] using h2356)
    (by simpa only [← hwp, ← hp8] using h3458)
    (by simpa only [← hp6, ← hp7, ← hp8] using h4678)
    (by simpa only [← hwp, ← hp7, ← hp8] using h1578)
  have hu : w 0 ≠ 0 := virtual_first_coordinate_ne_zero
    (p6 0) (p6 3) (w 0) (w 1) (w 3) ha equations.2.1
    (by simpa only [← hwp] using hw2)
  exact ⟨p6 0 * p8 1 * p7 2 / (p6 2 * p7 1 * p8 0),
    incidence_scale_golden_root
      (p6 0) (p6 2) (p6 3) (p7 1) (p7 2) (p7 3)
      (p8 0) (p8 1) (p8 2) (w 0) (w 1) (w 3)
      ha hb hc hd hg hu equations.1 equations.2.1 equations.2.2.1
      equations.2.2.2.1 equations.2.2.2.2⟩

/-- Lemma 5's incidence implication in homogeneous coordinates over an
arbitrary field. The first four points form the required projective frame. -/
theorem projective_golden_root (p : Fin 7 → Fin 4 → K) (w : Fin 4 → K)
    (hframe : LinearIndependent K ![p 0, p 1, p 2, p 3])
    (htriples : NoCollinearTriples p)
    (hw : ∀ t : K, w ≠ t • p 1) (hinc : GoldenIncidences p w) :
    ∃ t : K, t ^ 2 + t - 1 = 0 := by
  classical
  let b := basisOfPiSpaceOfLinearIndependent hframe
  let e := b.equivFun
  have hb (i : Fin 4) : b i = ![p 0, p 1, p 2, p 3] i :=
    congrFun (coe_basisOfPiSpaceOfLinearIndependent hframe) i
  have he (i j : Fin 4) : e (![p 0, p 1, p 2, p 3] i) j =
      if i = j then 1 else 0 := by
    rw [← hb]
    exact b.equivFun_self i j
  have he0 : e (p 0) = ![1,0,0,0] := by
    ext j
    have hj := he 0 j
    fin_cases j <;> simpa using hj
  have he1 : e (p 1) = ![0,1,0,0] := by
    ext j
    have hj := he 1 j
    fin_cases j <;> simpa using hj
  have he2 : e (p 2) = ![0,0,1,0] := by
    ext j
    have hj := he 2 j
    fin_cases j <;> simpa using hj
  have he3 : e (p 3) = ![0,0,0,1] := by
    ext j
    have hj := he 3 j
    fin_cases j <;> simpa using hj
  have hLI (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      LinearIndependent K ![e (p i), e (p j), e (p k)] := by
    have h := (htriples i j k hij hik hjk).map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    convert h using 1
    ext r
    fin_cases r <;> rfl
  rcases hinc with ⟨h1238, h1245, h1267, h1346, h1578, h2347, h2356, h3458, h4678⟩
  apply normalized_golden_root (e (p 4)) (e (p 5)) (e (p 6)) (e w)
  · simpa only [LinearEquiv.coe_toLinearMap, he2, he3] using hLI 2 3 4 (by decide) (by decide) (by decide)
  · simpa only [LinearEquiv.coe_toLinearMap, he0, he3] using hLI 0 3 4 (by decide) (by decide) (by decide)
  · simpa only [LinearEquiv.coe_toLinearMap, he0, he2] using hLI 0 2 4 (by decide) (by decide) (by decide)
  · simpa only [LinearEquiv.coe_toLinearMap, he2, he3] using hLI 2 3 5 (by decide) (by decide) (by decide)
  · simpa only [LinearEquiv.coe_toLinearMap, he1, he2] using hLI 1 2 6 (by decide) (by decide) (by decide)
  · intro t ht
    apply hw t
    apply e.injective
    simpa only [map_smul, he1] using ht
  · simpa only [LinearEquiv.coe_toLinearMap, he0, he1, he2] using coplanar_linear_image e.toLinearMap h1238
  · simpa only [LinearEquiv.coe_toLinearMap, he0, he1, he3] using coplanar_linear_image e.toLinearMap h1245
  · simpa only [LinearEquiv.coe_toLinearMap, he0, he1] using coplanar_linear_image e.toLinearMap h1267
  · simpa only [LinearEquiv.coe_toLinearMap, he0, he2, he3] using coplanar_linear_image e.toLinearMap h1346
  · simpa only [LinearEquiv.coe_toLinearMap, he0] using coplanar_linear_image e.toLinearMap h1578
  · simpa only [LinearEquiv.coe_toLinearMap, he1, he2, he3] using coplanar_linear_image e.toLinearMap h2347
  · simpa only [LinearEquiv.coe_toLinearMap, he1, he2] using coplanar_linear_image e.toLinearMap h2356
  · simpa only [LinearEquiv.coe_toLinearMap, he2, he3] using coplanar_linear_image e.toLinearMap h3458
  · simpa only [LinearEquiv.coe_toLinearMap, he3] using coplanar_linear_image e.toLinearMap h4678

theorem projective_golden_field_obstruction (K : Subfield ℝ)
    (p : Fin 7 → Fin 4 → K) (w : Fin 4 → K)
    (hframe : LinearIndependent K ![p 0, p 1, p 2, p 3])
    (htriples : NoCollinearTriples p)
    (hw : ∀ t : K, w ≠ t • p 1) (hinc : GoldenIncidences p w) :
    Real.sqrt 5 ∈ K := by
  obtain ⟨t, ht⟩ := projective_golden_root p w hframe htriples hw hinc
  exact sqrt_five_mem_of_golden K t.val t.property (by exact_mod_cast ht)

end Papers.Nonrational

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/ProjectiveSpan.lean -/



@[expose] public section

/-! Dimension arguments used to recover projective incidences from faces. -/

noncomputable section
namespace Papers.Nonrational
open Set Submodule Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

theorem independent_card_le_submodule {m : ℕ} {p : Fin m → V}
    (hp : LinearIndependent K p) (W : Submodule K V) (hm : ∀ i, p i ∈ W) :
    m ≤ finrank K W := by
  have hs : Submodule.span K (Set.range p) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hm i)
  simpa only [finrank_span_eq_card hp, Fintype.card_fin] using Submodule.finrank_mono hs

theorem span_eq_of_independent_of_finrank {m : ℕ} {p : Fin m → V}
    (hp : LinearIndependent K p) (W : Submodule K V) (hm : ∀ i, p i ∈ W)
    (hd : finrank K W = m) : Submodule.span K (Set.range p) = W := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hm i)
  · rw [finrank_span_eq_card hp, Fintype.card_fin, hd]

theorem not_independent_of_finrank_lt {m : ℕ} {p : Fin m → V}
    (W : Submodule K V) (hm : ∀ i, p i ∈ W) (hd : finrank K W < m) :
    ¬LinearIndependent K p := fun hp =>
  Nat.not_le_of_gt hd (independent_card_le_submodule hp W hm)

theorem dependent_quad_of_rank_le_three (W : Submodule K V) (a b c d : V)
    (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hd : d ∈ W)
    (hr : finrank K W ≤ 3) : ¬LinearIndependent K ![a, b, c, d] := by
  apply not_independent_of_finrank_lt W
  · intro i
    fin_cases i <;> assumption
  · omega

/-- Two three-dimensional homogeneous face spans sharing an independent
pair together have dimension at most four. -/
theorem two_planes_sup_rank_le_four (U W : Submodule K V)
    (hU : finrank K U ≤ 3) (hW : finrank K W ≤ 3)
    (x y : V) (hxy : LinearIndependent K ![x, y])
    (hxU : x ∈ U) (hyU : y ∈ U) (hxW : x ∈ W) (hyW : y ∈ W) :
    finrank K (U ⊔ W : Submodule K V) ≤ 4 := by
  have htwo : 2 ≤ finrank K (U ⊓ W : Submodule K V) :=
    independent_card_le_submodule hxy (U ⊓ W) (by
      intro i
      fin_cases i
      · exact ⟨hxU, hxW⟩
      · exact ⟨hyU, hyW⟩)
  have heq := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

/-- A vector outside the ambient reconstruction hyperplane forces a strict
drop when intersecting any span containing that vector with the hyperplane. -/
theorem inf_rank_le_three_of_outside (U H : Submodule K V)
    (hU : finrank K U ≤ 4) {x : V} (hxU : x ∈ U) (hxH : x ∉ H) :
    finrank K (U ⊓ H : Submodule K V) ≤ 3 := by
  have hproper : U ⊓ H < U := by
    apply lt_of_le_of_ne inf_le_left
    intro heq
    have hx : x ∈ U ⊓ H := heq.symm ▸ hxU
    exact hxH hx.2
  have hlt := Submodule.finrank_lt_finrank_of_lt hproper
  omega

theorem bridge_rank_le_three (U W H : Submodule K V)
    (hU : finrank K U ≤ 3) (hW : finrank K W ≤ 3)
    (x y : V) (hxy : LinearIndependent K ![x, y])
    (hxU : x ∈ U) (hyU : y ∈ U) (hxW : x ∈ W) (hyW : y ∈ W)
    (hxH : x ∉ H) : finrank K ((U ⊔ W) ⊓ H : Submodule K V) ≤ 3 := by
  apply inf_rank_le_three_of_outside
  · exact two_planes_sup_rank_le_four U W hU hW x y hxy hxU hyU hxW hyW
  · exact (show U ≤ U ⊔ W from le_sup_left) hxU
  · exact hxH

/-- A line in a five-dimensional vector space meets a four-dimensional
hyperplane in a nonzero vector. This is linear, not affine, intersection. -/
theorem exists_nonzero_line_hyperplane (H L : Submodule K V)
    (hV : finrank K V ≤ 5) (hH : finrank K H = 4) (hL : finrank K L = 2) :
    ∃ w : V, w ≠ 0 ∧ w ∈ H ∧ w ∈ L := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq H L
  have hle : finrank K (H ⊔ L : Submodule K V) ≤ 5 :=
    (Submodule.finrank_le _).trans hV
  have hpos : 0 < finrank K (H ⊓ L : Submodule K V) := by omega
  haveI : Nontrivial (H ⊓ L : Submodule K V) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨w, hw⟩ := exists_ne (0 : (H ⊓ L : Submodule K V))
  refine ⟨w.val, ?_, w.property.1, w.property.2⟩
  intro hz
  apply hw
  exact Subtype.ext hz

/-- If two four-dimensional spans share a three-dimensional span and an
additional point, they coincide. An omitted point therefore excludes every
additional point of one span from the other. -/
theorem auxiliary_outside_hyperplane (E F H : Submodule K V)
    (hE : finrank K E = 3) (hF : finrank K F = 4) (hH : finrank K H = 4)
    (hEF : E ≤ F) (hEH : E ≤ H) {y z : V}
    (hyF : y ∈ F) (hyE : y ∉ E) (hzH : z ∈ H) (hzF : z ∉ F) : y ∉ H := by
  intro hyH
  let W := E ⊔ Submodule.span K {y}
  have hW : finrank K W = 4 := by
    dsimp only [W]
    rw [Submodule.finrank_sup_span_singleton hyE, hE]
  have hWF : W ≤ F := sup_le hEF ((Submodule.span_singleton_le_iff_mem y F).mpr hyF)
  have hWH : W ≤ H := sup_le hEH ((Submodule.span_singleton_le_iff_mem y H).mpr hyH)
  have heqF : W = F := Submodule.eq_of_le_of_finrank_eq hWF (hW.trans hF.symm)
  have heqH : W = H := Submodule.eq_of_le_of_finrank_eq hWH (hW.trans hH.symm)
  exact hzF ((heqF.symm.trans heqH).symm ▸ hzH)

end Papers.Nonrational

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/GoldenSubspace.lean -/



@[expose] public section

/-! The golden incidence lemma in any four-dimensional linear subspace. -/

noncomputable section
namespace Papers.Nonrational
open Set Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def GoldenDependencies (p : Fin 7 → V) (w : V) : Prop :=
  (¬LinearIndependent K ![p 0, p 1, p 2, p 6]) ∧
  (¬LinearIndependent K ![p 0, p 1, p 3, w]) ∧
  (¬LinearIndependent K ![p 0, p 1, p 4, p 5]) ∧
  (¬LinearIndependent K ![p 0, p 2, p 3, p 4]) ∧
  (¬LinearIndependent K ![p 0, w, p 5, p 6]) ∧
  (¬LinearIndependent K ![p 1, p 2, p 3, p 5]) ∧
  (¬LinearIndependent K ![p 1, p 2, w, p 4]) ∧
  (¬LinearIndependent K ![p 2, p 3, w, p 6]) ∧
  (¬LinearIndependent K ![p 3, p 4, p 5, p 6])

theorem dependent_quad_map (f : V →ₗ[K] (Fin 4 → K)) {a b c d : V}
    (h : ¬LinearIndependent K ![a, b, c, d]) :
    Coplanar4 (f a) (f b) (f c) (f d) := by
  rw [coplanar_iff_dependent]
  intro hi
  apply h
  apply LinearIndependent.of_comp f
  convert hi using 1
  ext i
  fin_cases i <;> rfl

theorem golden_root_in_subspace (H : Submodule K V) [FiniteDimensional K H]
    (hH : finrank K H = 4) (p : Fin 7 → V) (w : V)
    (hp : ∀ i, p i ∈ H) (hw : w ∈ H)
    (hframe : LinearIndependent K ![p 0, p 1, p 2, p 3])
    (htriples : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      LinearIndependent K ![p i, p j, p k])
    (hwline : ∀ t : K, w ≠ t • p 1)
    (hinc : GoldenDependencies (K := K) p w) :
    ∃ t : K, t ^ 2 + t - 1 = 0 := by
  let e := (Module.finBasisOfFinrankEq K H hH).equivFun
  obtain ⟨f, hf⟩ := e.toLinearMap.exists_extend
  have hf_apply (x : H) : f x.val = e x := by
    exact congrArg (fun g : H →ₗ[K] (Fin 4 → K) => g x) hf
  have hmap {m : ℕ} (q : Fin m → V) (hq : ∀ i, q i ∈ H)
      (hi : LinearIndependent K q) : LinearIndependent K (fun i => f (q i)) := by
    let qH : Fin m → H := fun i => ⟨q i, hq i⟩
    have hiH : LinearIndependent K qH := LinearIndependent.of_comp H.subtype hi
    have hiE := hiH.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    convert hiE using 1
    funext i
    exact hf_apply (qH i)
  apply projective_golden_root (fun i => f (p i)) (f w)
  · have hm : ∀ i : Fin 4, ![p 0, p 1, p 2, p 3] i ∈ H := by
      intro i
      fin_cases i <;> exact hp _
    convert hmap _ hm hframe using 1
    ext i
    fin_cases i <;> rfl
  · intro i j k hij hik hjk
    have hm : ∀ a : Fin 3, ![p i, p j, p k] a ∈ H := by
      intro a
      fin_cases a <;> exact hp _
    convert hmap _ hm (htriples i j k hij hik hjk) using 1
    ext a
    fin_cases a <;> rfl
  · intro t heq
    apply hwline t
    have he : e ⟨w, hw⟩ = e (t • (⟨p 1, hp 1⟩ : H)) := by
      rw [map_smul, ← hf_apply, ← hf_apply]
      exact heq
    exact congrArg Subtype.val (e.injective he)
  · obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := hinc
    exact ⟨dependent_quad_map f h1, dependent_quad_map f h2,
      dependent_quad_map f h3, dependent_quad_map f h4, dependent_quad_map f h5,
      dependent_quad_map f h6, dependent_quad_map f h7, dependent_quad_map f h8,
      dependent_quad_map f h9⟩

end Papers.Nonrational

end
end
end BundlePart13

section BundlePart14
/- Source: Papers/SeventeenReconstruction.lean -/




@[expose] public section

/-!
# Universal reconstruction from the twenty-one certified faces

The hypotheses are abstract homogeneous ranks and face-span exclusions.
`SeventeenRealization` derives precisely these hypotheses for every ordinary
combinatorial realization of the constructed polytope.
-/

noncomputable section
namespace Papers.Nonrational.Seventeen
open Set Module
open SeventeenRankData

variable {K : Type*} [Field K]

def reconstructionSpan (p : Fin 17 → Fin 5 → K) (f : Fin 21) :
    Submodule K (Fin 5 → K) := Submodule.span K (p '' (faceVertices f : Set (Fin 17)))

theorem mem_reconstructionSpan (p : Fin 17 → Fin 5 → K) (f : Fin 21) (v : Fin 17)
    (hv : v ∈ faceVertices f) : p v ∈ reconstructionSpan p f :=
  Submodule.subset_span ⟨v, hv, rfl⟩

theorem reconstructionSpan_le (p : Fin 17 → Fin 5 → K) (f : Fin 21)
    (W : Submodule K (Fin 5 → K)) (h : ∀ v ∈ faceVertices f, p v ∈ W) :
    reconstructionSpan p f ≤ W :=
  Submodule.span_le.mpr (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)

theorem reconstructionSpan_mono (p : Fin 17 → Fin 5 → K) (f g : Fin 21)
    (h : faceVertices f ⊆ faceVertices g) : reconstructionSpan p f ≤ reconstructionSpan p g :=
  Submodule.span_mono (Set.image_mono h)

theorem independent_pair_of_triple {V : Type*} [AddCommGroup V] [Module K V]
    {a b c : V} (h : LinearIndependent K ![a, b, c]) : LinearIndependent K ![a, b] := by
  have hi := h.comp Fin.castSucc (Fin.castSucc_injective 2)
  convert hi using 1
  ext i
  fin_cases i <;> rfl

theorem golden_root_of_face_ranks (p : Fin 17 → Fin 5 → K)
    (htriples : ∀ i j k : Fin 17, i ≠ j → i ≠ k → j ≠ k →
      LinearIndependent K ![p i, p j, p k])
    (hplanes : ∀ f : Fin 14, finrank K (reconstructionSpan p (planeFace f)) = 3)
    (hfacets : ∀ f : Fin 7, finrank K (reconstructionSpan p (facetFace f)) = 4)
    (hflat : ∀ f v, v ∉ faceVertices f → p v ∉ reconstructionSpan p f) :
    ∃ t : K, t ^ 2 + t - 1 = 0 := by
  let F := reconstructionSpan p
  have hm := mem_reconstructionSpan p
  have h012 : LinearIndependent K ![p 0, p 1, p 2] :=
    htriples 0 1 2 (by decide) (by decide) (by decide)
  have hF19 : Submodule.span K (Set.range ![p 0, p 1, p 2]) = F 19 := by
    apply span_eq_of_independent_of_finrank h012
    · intro i
      fin_cases i <;> exact hm 19 _ (by decide)
    · exact hplanes 12
  have hp3 : p 3 ∉ Submodule.span K (Set.range ![p 0, p 1, p 2]) := by
    rw [hF19]
    exact hflat 19 3 (by decide)
  have hframe : LinearIndependent K ![p 0, p 1, p 2, p 3] := by
    convert h012.finSnoc hp3 using 1
    ext i
    fin_cases i <;> rfl
  let H := Submodule.span K (Set.range ![p 0, p 1, p 2, p 3])
  have hH : finrank K H = 4 := by
    exact (finrank_span_eq_card hframe).trans (Fintype.card_fin 4)
  have h0 : p 0 ∈ H := Submodule.subset_span ⟨0, rfl⟩
  have h1 : p 1 ∈ H := Submodule.subset_span ⟨1, rfl⟩
  have h2 : p 2 ∈ H := Submodule.subset_span ⟨2, rfl⟩
  have h3 : p 3 ∈ H := Submodule.subset_span ⟨3, rfl⟩
  have h19H : F 19 ≤ H := by
    rw [← hF19]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> assumption
  have h6 : p 6 ∈ H := h19H (hm 19 6 (by decide))
  have hF20 : Submodule.span K (Set.range ![p 1, p 2, p 3]) = F 20 := by
    apply span_eq_of_independent_of_finrank
      (htriples 1 2 3 (by decide) (by decide) (by decide))
    · intro i
      fin_cases i <;> exact hm 20 _ (by decide)
    · exact hplanes 13
  have h20H : F 20 ≤ H := by
    rw [← hF20]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> assumption
  have h5 : p 5 ∈ H := h20H (hm 20 5 (by decide))
  have hF16 : Submodule.span K (Set.range ![p 0, p 1, p 5]) = F 16 := by
    apply span_eq_of_independent_of_finrank
      (htriples 0 1 5 (by decide) (by decide) (by decide))
    · intro i
      fin_cases i <;> exact hm 16 _ (by decide)
    · exact hplanes 10
  have h16H : F 16 ≤ H := by
    rw [← hF16]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> assumption
  have h4 : p 4 ∈ H := h16H (hm 16 4 (by decide))
  have h18H : F 18 ≤ H := by
    apply reconstructionSpan_le
    intro v hv
    have hv' : v = 0 ∨ v = 4 ∨ v = 6 := by simpa [faceVertices] using hv
    rcases hv' with rfl | rfl | rfl <;> assumption
  have hout7 : p 7 ∉ H := auxiliary_outside_hyperplane (F 19) (F 12) H
    (hplanes 12) (hfacets 2) hH (reconstructionSpan_mono p 19 12 (by decide)) h19H
    (hm 12 7 (by decide)) (hflat 19 7 (by decide)) h3 (hflat 12 3 (by decide))
  have hout9 : p 9 ∉ H := auxiliary_outside_hyperplane (F 20) (F 14) H
    (hplanes 13) (hfacets 4) hH (reconstructionSpan_mono p 20 14 (by decide)) h20H
    (hm 14 9 (by decide)) (hflat 20 9 (by decide)) h0 (hflat 14 0 (by decide))
  have hout11 : p 11 ∉ H := auxiliary_outside_hyperplane (F 18) (F 10) H
    (hplanes 11) (hfacets 0) hH (reconstructionSpan_mono p 18 10 (by decide)) h18H
    (hm 10 11 (by decide)) (hflat 18 11 (by decide)) h1 (hflat 10 1 (by decide))
  have hout13 : p 13 ∉ H := auxiliary_outside_hyperplane (F 19) (F 13) H
    (hplanes 12) (hfacets 3) hH (reconstructionSpan_mono p 19 13 (by decide)) h19H
    (hm 13 13 (by decide)) (hflat 19 13 (by decide)) h3 (hflat 13 3 (by decide))
  have hout15 : p 15 ∉ H := auxiliary_outside_hyperplane (F 18) (F 11) H
    (hplanes 11) (hfacets 1) hH (reconstructionSpan_mono p 18 11 (by decide)) h18H
    (hm 11 15 (by decide)) (hflat 18 15 (by decide)) h1 (hflat 11 1 (by decide))
  have hpair1213 : LinearIndependent K ![p 12, p 13] := independent_pair_of_triple
    (htriples 12 13 1 (by decide) (by decide) (by decide))
  let L := Submodule.span K (Set.range ![p 12, p 13])
  have hL : finrank K L = 2 := (finrank_span_eq_card hpair1213).trans (Fintype.card_fin 2)
  obtain ⟨w, hw0, hwH, hwL⟩ := exists_nonzero_line_hyperplane H L (by simp) hH hL
  have hnot1 : p 1 ∉ L := (linearIndependent_finCons.mp
    (htriples 1 12 13 (by decide) (by decide) (by decide))).2
  have hwline : ∀ t : K, w ≠ t • p 1 := by
    intro t ht
    have ht0 : t ≠ 0 := by
      intro hz
      apply hw0
      simpa [hz] using ht
    apply hnot1
    rw [ht] at hwL
    exact (Submodule.smul_mem_iff _ ht0).mp hwL
  have hwFace (f : Fin 21) (h12 : 12 ∈ faceVertices f) (h13 : 13 ∈ faceVertices f) :
      w ∈ F f := by
    apply (show L ≤ F f from ?_) hwL
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hm f 12 h12
    · exact hm f 13 h13
  have hwF1 : w ∈ F 1 := hwFace 1 (by decide) (by decide)
  have hwF5 : w ∈ F 5 := hwFace 5 (by decide) (by decide)
  have hwF7 : w ∈ F 7 := hwFace 7 (by decide) (by decide)
  have hwF17 : w ∈ F 17 := hwFace 17 (by decide) (by decide)
  have hr01 : finrank K ((F 0 ⊔ F 1) ⊓ H : Submodule K (Fin 5 → K)) ≤ 3 :=
    bridge_rank_le_three (F 0) (F 1) H (hplanes 0).le (hplanes 1).le (p 7) (p 8)
      (independent_pair_of_triple (htriples 7 8 0 (by decide) (by decide) (by decide)))
      (hm 0 7 (by decide)) (hm 0 8 (by decide))
      (hm 1 7 (by decide)) (hm 1 8 (by decide)) hout7
  have hr23 : finrank K ((F 2 ⊔ F 3) ⊓ H : Submodule K (Fin 5 → K)) ≤ 3 :=
    bridge_rank_le_three (F 2) (F 3) H (hplanes 2).le (hplanes 3).le (p 9) (p 10)
      (independent_pair_of_triple (htriples 9 10 0 (by decide) (by decide) (by decide)))
      (hm 2 9 (by decide)) (hm 2 10 (by decide))
      (hm 3 9 (by decide)) (hm 3 10 (by decide)) hout9
  have hr45 : finrank K ((F 4 ⊔ F 5) ⊓ H : Submodule K (Fin 5 → K)) ≤ 3 :=
    bridge_rank_le_three (F 4) (F 5) H (hplanes 4).le (hplanes 5).le (p 11) (p 12)
      (independent_pair_of_triple (htriples 11 12 0 (by decide) (by decide) (by decide)))
      (hm 4 11 (by decide)) (hm 4 12 (by decide))
      (hm 5 11 (by decide)) (hm 5 12 (by decide)) hout11
  have hr67 : finrank K ((F 6 ⊔ F 7) ⊓ H : Submodule K (Fin 5 → K)) ≤ 3 :=
    bridge_rank_le_three (F 6) (F 7) H (hplanes 6).le (hplanes 7).le (p 13) (p 14)
      (independent_pair_of_triple (htriples 13 14 0 (by decide) (by decide) (by decide)))
      (hm 6 13 (by decide)) (hm 6 14 (by decide))
      (hm 7 13 (by decide)) (hm 7 14 (by decide)) hout13
  have hr89 : finrank K ((F 8 ⊔ F 9) ⊓ H : Submodule K (Fin 5 → K)) ≤ 3 :=
    bridge_rank_le_three (F 8) (F 9) H (hplanes 8).le (hplanes 9).le (p 15) (p 16)
      (independent_pair_of_triple (htriples 15 16 0 (by decide) (by decide) (by decide)))
      (hm 8 15 (by decide)) (hm 8 16 (by decide))
      (hm 9 15 (by decide)) (hm 9 16 (by decide)) hout15
  have hr17 : finrank K (F 17 ⊓ H : Submodule K (Fin 5 → K)) ≤ 3 :=
    inf_rank_le_three_of_outside (F 17) H (hfacets 6).le (hm 17 7 (by decide)) hout7
  let numeric : Fin 7 → Fin 5 → K := fun i => p (Fin.castLE (by decide : 7 ≤ 17) i)
  have hnumeric : ∀ i, numeric i ∈ H := by
    intro i
    fin_cases i <;> assumption
  apply golden_root_in_subspace H hH numeric w hnumeric hwH hframe
  · intro i j k hij hik hjk
    apply htriples
    · exact fun h => hij ((Fin.castLE_injective (by decide : 7 ≤ 17)) h)
    · exact fun h => hik ((Fin.castLE_injective (by decide : 7 ≤ 17)) h)
    · exact fun h => hjk ((Fin.castLE_injective (by decide : 7 ≤ 17)) h)
  · exact hwline
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact dependent_quad_of_rank_le_three (F 19) _ _ _ _
        (hm 19 0 (by decide)) (hm 19 1 (by decide))
        (hm 19 2 (by decide)) (hm 19 6 (by decide)) (hplanes 12).le
    · exact dependent_quad_of_rank_le_three ((F 0 ⊔ F 1) ⊓ H) _ _ _ _
        ⟨Submodule.mem_sup_left (hm 0 0 (by decide)), h0⟩
        ⟨Submodule.mem_sup_left (hm 0 1 (by decide)), h1⟩
        ⟨Submodule.mem_sup_right (hm 1 3 (by decide)), h3⟩ ⟨Submodule.mem_sup_right hwF1, hwH⟩ hr01
    · exact dependent_quad_of_rank_le_three (F 16) _ _ _ _
        (hm 16 0 (by decide)) (hm 16 1 (by decide))
        (hm 16 4 (by decide)) (hm 16 5 (by decide)) (hplanes 10).le
    · exact dependent_quad_of_rank_le_three ((F 2 ⊔ F 3) ⊓ H) _ _ _ _
        ⟨Submodule.mem_sup_left (hm 2 0 (by decide)), h0⟩
        ⟨Submodule.mem_sup_right (hm 3 2 (by decide)), h2⟩
        ⟨Submodule.mem_sup_right (hm 3 3 (by decide)), h3⟩
        ⟨Submodule.mem_sup_left (hm 2 4 (by decide)), h4⟩ hr23
    · exact dependent_quad_of_rank_le_three ((F 4 ⊔ F 5) ⊓ H) _ _ _ _
        ⟨Submodule.mem_sup_left (hm 4 0 (by decide)), h0⟩ ⟨Submodule.mem_sup_right hwF5, hwH⟩
        ⟨Submodule.mem_sup_right (hm 5 5 (by decide)), h5⟩
        ⟨Submodule.mem_sup_left (hm 4 6 (by decide)), h6⟩ hr45
    · exact dependent_quad_of_rank_le_three (F 20) _ _ _ _
        (hm 20 1 (by decide)) (hm 20 2 (by decide))
        (hm 20 3 (by decide)) (hm 20 5 (by decide)) (hplanes 13).le
    · exact dependent_quad_of_rank_le_three ((F 6 ⊔ F 7) ⊓ H) _ _ _ _
        ⟨Submodule.mem_sup_left (hm 6 1 (by decide)), h1⟩
        ⟨Submodule.mem_sup_left (hm 6 2 (by decide)), h2⟩ ⟨Submodule.mem_sup_right hwF7, hwH⟩
        ⟨Submodule.mem_sup_right (hm 7 4 (by decide)), h4⟩ hr67
    · exact dependent_quad_of_rank_le_three (F 17 ⊓ H) _ _ _ _
        ⟨hm 17 2 (by decide), h2⟩ ⟨hm 17 3 (by decide), h3⟩
        ⟨hwF17, hwH⟩ ⟨hm 17 6 (by decide), h6⟩ hr17
    · exact dependent_quad_of_rank_le_three ((F 8 ⊔ F 9) ⊓ H) _ _ _ _
        ⟨Submodule.mem_sup_left (hm 8 3 (by decide)), h3⟩
        ⟨Submodule.mem_sup_right (hm 9 4 (by decide)), h4⟩
        ⟨Submodule.mem_sup_left (hm 8 5 (by decide)), h5⟩
        ⟨Submodule.mem_sup_right (hm 9 6 (by decide)), h6⟩ hr89

end Papers.Nonrational.Seventeen

end
end
end BundlePart14

section BundlePart15
/- Source: Papers/NonrationalSeventeen.lean -/




@[expose] public section

/-!
# The seventeen-vertex field obstruction

The existence direction uses the explicit exact coordinates. The necessity
direction reconstructs the golden incidences in every realization of the
ordinary face lattice, over every real subfield.
-/

noncomputable section
namespace Papers.Nonrational.Seventeen
open Module
open Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open SeventeenRankData

theorem sqrt_five_of_realizable (K : Subfield ℝ) (h : RealizableOver polytope K) :
    Real.sqrt 5 ∈ K := by
  obtain ⟨Q, ⟨φ⟩, hK⟩ := h
  have hplanes (f : Fin 14) :
      finrank K (reconstructionSpan (fieldPoint φ K hK) (planeFace f)) = 3 := by
    change finrank K (fieldFaceSpan φ K hK (planeFace f)) = 3
    rw [fieldFaceSpan_rank, plane_face_dimension]
  have hfacets (f : Fin 7) :
      finrank K (reconstructionSpan (fieldPoint φ K hK) (facetFace f)) = 4 := by
    change finrank K (fieldFaceSpan φ K hK (facetFace f)) = 4
    rw [fieldFaceSpan_rank, facet_face_dimension]
  obtain ⟨t, ht⟩ := golden_root_of_face_ranks (fieldPoint φ K hK)
    (fieldPoint_triples φ K hK) hplanes hfacets (fieldPoint_notMem_faceSpan φ K hK)
  apply sqrt_five_mem_of_golden K (t : ℝ) t.property
  exact_mod_cast ht

/-- The full field-of-realization equivalence, with arbitrary real subfields. -/
theorem realizable_iff_sqrt_five (K : Subfield ℝ) :
    RealizableOver polytope K ↔ Real.sqrt 5 ∈ K :=
  ⟨sqrt_five_of_realizable K, realizable_of_sqrt_five K⟩

/-- Theorem 1 of the nonrational four-polytopes paper. -/
theorem seventeen_vertex_field_theorem : SeventeenVertexFieldClaim := by
  exact ⟨polytope, polytope_fullDim, polytope_card, realizable_iff_sqrt_five⟩

end Papers.Nonrational.Seventeen

end
end
end BundlePart15

section BundlePart16
/- Source: Papers/NonrationalSeventeenConsequences.lean -/





@[expose] public section

/-!
# Explicit irrationality consequence of the full realization-field theorem

The conclusion excludes every rational realization of the same face
lattice, rather than merely observing irrational coordinates in one model.
-/

noncomputable section
namespace Papers.Nonrational.Seventeen
open Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem sqrt_five_notMem_rationalSubfield :
    Real.sqrt 5 ∉ rationalSubfield := by
  have hi : Irrational (Real.sqrt 5) := by
    simpa using Nat.Prime.irrational_sqrt (show Nat.Prime 5 by decide)
  exact hi

theorem not_rationallyRealizable : ¬RationallyRealizable polytope := by
  intro h
  apply sqrt_five_notMem_rationalSubfield
  exact (realizable_iff_sqrt_five rationalSubfield).mp
    ((rationallyRealizable_iff_realizableOver polytope).mp h)

theorem exists_seventeen_vertex_nonrational_polytope :
    ∃ P : ConvexPolytope 4,
      P.IsFullDim ∧ P.vertices.card = 17 ∧ ¬RationallyRealizable P :=
  ⟨polytope, polytope_fullDim, polytope_card, not_rationallyRealizable⟩

end Papers.Nonrational.Seventeen

end
end
end BundlePart16
