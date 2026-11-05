module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push
public import Mathlib.Data.Finset.Max
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Quot
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.ByContra

@[expose] public section

/-!
# Rank-three algebra for coordinate projection areas

The four sections below establish the positive metric rank obstruction,
its weighted form including zero weights, the boundary equalities on
four coordinates, and the complete matrix quotient by zero entries.
They share a single compilation unit to avoid repeatedly loading the
same foundational matrix and ordered-field imports.
-/

noncomputable section

/-!
# Low rank positive metric matrices

This file proves the algebraic obstruction needed for Section 5 of
*Compatibility and realization of coordinate projection areas*.
Every positive hollow symmetric metric matrix on at least five labels has
rank at least four. The proof avoids circumcentres and cyclic ordering:
a singular positive four-point metric must have the rectangle relations,
and these relations cannot hold on all overlapping four-point subsets
of a positive five-point metric.

Recovered from the earlier `MetricObstruction.lean` checkpoint, with the algebraic certificate shortened
to a sum of nonnegative products. No statement about convex bodies
or Lebesgue area is assumed in this algebraic result.
-/


namespace ProjectionAreaRankThree

/-- The determinant of a symmetric hollow four-by-four matrix, listed by its six edges. -/
def hollowDet (a b c d e f : ℝ) : ℝ :=
  a^2*f^2 + b^2*e^2 + c^2*d^2 - 2*a*b*e*f - 2*a*c*d*f - 2*b*c*d*e

/-- Six nonnegative cut weights in the four-point metric decomposition. -/
def cutDet (x1 x2 x3 x4 y z : ℝ) : ℝ :=
  hollowDet (x1+x2+y+z) (x1+x3+z) (x1+x4+y)
    (x2+x3+y) (x2+x4+z) (x3+x4+y+z)

private theorem cutDet_negative_first
    (x1 x2 x3 x4 y z : ℝ)
    (h1 : 0 < x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3) (h4 : 0 ≤ x4)
    (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hd : 0 < x2+x3+y) (he : 0 < x2+x4+z) (hf : 0 < x3+x4+y+z) :
    cutDet x1 x2 x3 x4 y z < 0 := by
  let S : ℝ := x3 + x4 + y + z
  let R : ℝ :=
    x1 * (x2^2*S +
      x2*(x3^2 + x4^2 + 2*(x3+x4)*(y+z) + (y+z)^2 + 2*y*z) +
      (x3+y)*(x4+z)*S) +
    x2^2*(x3+z)*(x4+y) + x2*(x3+z)*(x4+y)*S +
    S*(x3*x4*(y+z) + y*z*(x3+x4))
  have hR : 0 ≤ R := by dsimp [R, S]; positivity
  have hS : 0 < x2*(x3+x4+y+z) + (x3+y)*(x4+z) := by
    rcases eq_or_lt_of_le h2 with hx2 | hx2
    · have hx20 : x2 = 0 := hx2.symm
      subst x2
      simpa only [zero_mul, zero_add] using mul_pos hd he
    · exact add_pos_of_pos_of_nonneg (mul_pos hx2 hf) (mul_nonneg (by positivity) (by positivity))
  have hprod : 0 < x1^2*(x2*(x3+x4+y+z) + (x3+y)*(x4+z)) :=
    mul_pos (sq_pos_of_pos h1) hS
  have hid : cutDet x1 x2 x3 x4 y z =
      -4 * (x1^2*(x2*(x3+x4+y+z) + (x3+y)*(x4+z)) + R) := by
    dsimp [cutDet, hollowDet, R, S]
    ring
  rw [hid]
  nlinarith

private theorem cutDet_swap12 (x1 x2 x3 x4 y z : ℝ) :
    cutDet x2 x1 x4 x3 y z = cutDet x1 x2 x3 x4 y z := by
  dsimp [cutDet, hollowDet]
  ring

private theorem cutDet_swap13 (x1 x2 x3 x4 y z : ℝ) :
    cutDet x3 x4 x1 x2 y z = cutDet x1 x2 x3 x4 y z := by
  dsimp [cutDet, hollowDet]
  ring

private theorem cutDet_swap14 (x1 x2 x3 x4 y z : ℝ) :
    cutDet x4 x3 x2 x1 y z = cutDet x1 x2 x3 x4 y z := by
  dsimp [cutDet, hollowDet]
  ring

/-- If a positive four-point metric has zero determinant, every singleton cut weight vanishes. -/
theorem cutDet_zero_singleton_weights
    (x1 x2 x3 x4 y z : ℝ)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3) (h4 : 0 ≤ x4)
    (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 < x1+x2+y+z) (hb : 0 < x1+x3+z) (hc : 0 < x1+x4+y)
    (hd : 0 < x2+x3+y) (he : 0 < x2+x4+z) (hf : 0 < x3+x4+y+z)
    (hdet : cutDet x1 x2 x3 x4 y z = 0) :
    x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ x4 = 0 := by
  have hx1 : x1 = 0 := by
    by_contra hx
    have hneg := cutDet_negative_first x1 x2 x3 x4 y z
      (lt_of_le_of_ne h1 (Ne.symm hx)) h2 h3 h4 hy hz hd he hf
    linarith
  have hx2 : x2 = 0 := by
    by_contra hx
    have hneg := cutDet_negative_first x2 x1 x4 x3 y z
      (lt_of_le_of_ne h2 (Ne.symm hx)) h1 h4 h3 hy hz hc hb (by linarith)
    rw [cutDet_swap12] at hneg
    linarith
  have hx3 : x3 = 0 := by
    by_contra hx
    have hneg := cutDet_negative_first x3 x4 x1 x2 y z
      (lt_of_le_of_ne h3 (Ne.symm hx)) h4 h1 h2 hy hz (by linarith) (by linarith) ha
    rw [cutDet_swap13] at hneg
    linarith
  have hx4 : x4 = 0 := by
    by_contra hx
    have hneg := cutDet_negative_first x4 x3 x2 x1 y z
      (lt_of_le_of_ne h4 (Ne.symm hx)) h3 h2 h1 hy hz (by linarith) (by linarith) (by linarith)
    rw [cutDet_swap14] at hneg
    linarith
  exact ⟨hx1,hx2,hx3,hx4⟩

/-- Four-point classification when the first pair of opposite-edge sums is maximal. -/
theorem four_point_rectangle_ordered
    (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (ht1 : f ≤ b+c) (ht2 : f ≤ d+e) (ht3 : a ≤ b+d) (ht4 : a ≤ c+e)
    (hm1 : b+e ≤ a+f) (hm2 : c+d ≤ a+f)
    (hdet : hollowDet a b c d e f = 0) :
    a = f ∧ b = e ∧ c = d ∧ a = b+c := by
  let x1 := (b+c-f)/2
  let x2 := (d+e-f)/2
  let x3 := (b+d-a)/2
  let x4 := (c+e-a)/2
  let y := (a+f-b-e)/2
  let z := (a+f-c-d)/2
  have h1 : 0 ≤ x1 := by dsimp [x1]; linarith
  have h2 : 0 ≤ x2 := by dsimp [x2]; linarith
  have h3 : 0 ≤ x3 := by dsimp [x3]; linarith
  have h4 : 0 ≤ x4 := by dsimp [x4]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have ea : x1+x2+y+z = a := by dsimp [x1,x2,y,z]; ring
  have eb : x1+x3+z = b := by dsimp [x1,x3,z]; ring
  have ec : x1+x4+y = c := by dsimp [x1,x4,y]; ring
  have ed : x2+x3+y = d := by dsimp [x2,x3,y]; ring
  have ee : x2+x4+z = e := by dsimp [x2,x4,z]; ring
  have ef : x3+x4+y+z = f := by dsimp [x3,x4,y,z]; ring
  have hzero : cutDet x1 x2 x3 x4 y z = 0 := by
    simpa only [cutDet,ea,eb,ec,ed,ee,ef] using hdet
  obtain ⟨hx1,hx2,hx3,hx4⟩ := cutDet_zero_singleton_weights
    x1 x2 x3 x4 y z h1 h2 h3 h4 hy hz
    (ea.symm ▸ ha) (eb.symm ▸ hb) (ec.symm ▸ hc)
    (ed.symm ▸ hd) (ee.symm ▸ he) (ef.symm ▸ hf) hzero
  dsimp [x1,x2,x3,x4] at hx1 hx2 hx3 hx4
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩


/-- All triangle inequalities on four labelled points. -/
def Triangle6 (a b c d e f : ℝ) : Prop :=
  a ≤ b+d ∧ b ≤ a+d ∧ d ≤ a+b ∧
  a ≤ c+e ∧ c ≤ a+e ∧ e ≤ a+c ∧
  b ≤ c+f ∧ c ≤ b+f ∧ f ≤ b+c ∧
  d ≤ e+f ∧ e ≤ d+f ∧ f ≤ d+e

/-- A positive four-point metric of rank at most three has precisely the distance
relations of the squared distances between the vertices of a rectangle. -/
theorem four_point_rectangle
    (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (ht : Triangle6 a b c d e f) (hdet : hollowDet a b c d e f = 0) :
    a = f ∧ b = e ∧ c = d ∧ (a = b+c ∨ b = a+c ∨ c = a+b) := by
  rcases ht with ⟨habd,hbad,hdab,hace,hcae,heac,hbcf,hcbf,hfbc,hdef,hedf,hfde⟩
  by_cases hm1 : b+e ≤ a+f
  · by_cases hm2 : c+d ≤ a+f
    · obtain ⟨h1,h2,h3,h4⟩ := four_point_rectangle_ordered
        a b c d e f ha hb hc hd he hf hfbc hfde habd hace hm1 hm2 hdet
      exact ⟨h1,h2,h3,Or.inl h4⟩
    · have hm3 : a+f ≤ c+d := le_of_not_ge hm2
      have hdet' : hollowDet c a b e f d = 0 := by
        calc hollowDet c a b e f d = hollowDet a b c d e f := by unfold hollowDet; ring
             _ = 0 := hdet
      obtain ⟨h1,h2,h3,h4⟩ := four_point_rectangle_ordered
        c a b e f d hc ha hb he hf hd hdab (by linarith) hcae hcbf hm3
        (hm1.trans hm3) hdet'
      exact ⟨h2,h3,h1,Or.inr (Or.inr h4)⟩
  · have hm1' : a+f ≤ b+e := le_of_not_ge hm1
    by_cases hm2 : c+d ≤ b+e
    · have hdet' : hollowDet b a c d f e = 0 := by
        calc hollowDet b a c d f e = hollowDet a b c d e f := by unfold hollowDet; ring
             _ = 0 := hdet
      obtain ⟨h1,h2,h3,h4⟩ := four_point_rectangle_ordered
        b a c d f e hb ha hc hd hf he heac hedf hbad hbcf hm1' hm2 hdet'
      exact ⟨h2,h1,h3,Or.inr (Or.inl h4)⟩
    · have hm3 : b+e ≤ c+d := le_of_not_ge hm2
      have hdet' : hollowDet c a b e f d = 0 := by
        calc hollowDet c a b e f d = hollowDet a b c d e f := by unfold hollowDet; ring
             _ = 0 := hdet
      obtain ⟨h1,h2,h3,h4⟩ := four_point_rectangle_ordered
        c a b e f d hc ha hb he hf hd hdab (by linarith) hcae hcbf
        (hm1'.trans hm3) hm3 hdet'
      exact ⟨h2,h3,h1,Or.inr (Or.inr h4)⟩

/-- Literal hollow matrix used in the determinant correspondence. -/
def hollowMatrix4 (a b c d e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,a,b,c; a,0,d,e; b,d,0,f; c,e,f,0]

theorem det_hollowMatrix4 (a b c d e f : ℝ) :
    (hollowMatrix4 a b c d e f).det = hollowDet a b c d e f := by
  rw [Matrix.det_succ_row_zero]
  norm_num [hollowMatrix4, Matrix.det_fin_three, Matrix.submatrix,
    Fin.sum_univ_four, Fin.succAbove, hollowDet]
  <;> ring

/-- The geometric positivity and metric hypotheses are separate from the rank hypothesis. -/
structure PositiveMetricMatrix (n : ℕ) where
  entries : Matrix (Fin n) (Fin n) ℝ
  hollow : ∀ i, entries i i = 0
  symmetric : ∀ i j, entries i j = entries j i
  positive : ∀ i j, i ≠ j → 0 < entries i j
  triangle : ∀ i j k, entries i j ≤ entries i k + entries k j

namespace PositiveMetricMatrix

variable {n : ℕ} (D : PositiveMetricMatrix n)

theorem four_triangle (i j k l : Fin n) :
    Triangle6 (D.entries i j) (D.entries i k) (D.entries i l)
      (D.entries j k) (D.entries j l) (D.entries k l) := by
  have h1 := D.triangle i j k
  have h2 := D.triangle i k j
  have h3 := D.triangle j k i
  have h4 := D.triangle i j l
  have h5 := D.triangle i l j
  have h6 := D.triangle j l i
  have h7 := D.triangle i k l
  have h8 := D.triangle i l k
  have h9 := D.triangle k l i
  have h10 := D.triangle j k l
  have h11 := D.triangle j l k
  have h12 := D.triangle k l j
  dsimp [Triangle6]
  simp only [D.symmetric k j, D.symmetric j i, D.symmetric l j,
    D.symmetric l k, D.symmetric k i] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩

theorem selected_det (i j k l : Fin n) :
    (D.entries.submatrix ![i,j,k,l] ![i,j,k,l]).det =
      hollowDet (D.entries i j) (D.entries i k) (D.entries i l)
        (D.entries j k) (D.entries j l) (D.entries k l) := by
  have heq : D.entries.submatrix ![i,j,k,l] ![i,j,k,l] =
      hollowMatrix4 (D.entries i j) (D.entries i k) (D.entries i l)
        (D.entries j k) (D.entries j l) (D.entries k l) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.submatrix, hollowMatrix4, D.hollow, D.symmetric]
  rw [heq, det_hollowMatrix4]

theorem four_det_eq_zero (hrank : D.entries.rank ≤ 3) (i j k l : Fin n) :
    hollowDet (D.entries i j) (D.entries i k) (D.entries i l)
      (D.entries j k) (D.entries j l) (D.entries k l) = 0 := by
  rw [← D.selected_det i j k l]
  by_contra hdet
  have hb := (D.entries.rank_submatrix_le ![i,j,k,l] ![i,j,k,l]).trans hrank
  rw [Matrix.rank_of_det_ne_zero hdet] at hb
  norm_num at hb

/-- The rectangle relations, without an order on the four labels. -/
theorem four_rectangle (hrank : D.entries.rank ≤ 3)
    (i j k l : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    D.entries i j = D.entries k l ∧
    D.entries i k = D.entries j l ∧
    D.entries i l = D.entries j k ∧
    (D.entries i j = D.entries i k + D.entries i l ∨
     D.entries i k = D.entries i j + D.entries i l ∨
     D.entries i l = D.entries i j + D.entries i k) := by
  exact four_point_rectangle _ _ _ _ _ _
    (D.positive i j hij) (D.positive i k hik) (D.positive i l hil)
    (D.positive j k hjk) (D.positive j l hjl) (D.positive k l hkl)
    (D.four_triangle i j k l) (D.four_det_eq_zero hrank i j k l)

/-- Every positive five-point metric matrix has rank at least four. -/
theorem five_rank_not_le_three (D : PositiveMetricMatrix 5) : ¬ D.entries.rank ≤ 3 := by
  intro hrank
  have h0123 := D.four_rectangle hrank 0 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0124 := D.four_rectangle hrank 0 1 2 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0134 := D.four_rectangle hrank 0 1 3 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0234 := D.four_rectangle hrank 0 2 3 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨h1,h2,h3,h4⟩ := h0123
  obtain ⟨h5,h6,h7,-⟩ := h0124
  obtain ⟨h8,h9,h10,-⟩ := h0134
  obtain ⟨h11,h12,h13,-⟩ := h0234
  have hp := D.positive 0 1 (by decide)
  rcases h4 with h4 | h4 | h4 <;> linarith

/-- No positive metric matrix on at least five labels has rank at most three. -/
theorem rank_at_least_four (D : PositiveMetricMatrix n) (hn : 5 ≤ n) :
    4 ≤ D.entries.rank := by
  let emb : Fin 5 → Fin n := Fin.castLE hn
  let E : PositiveMetricMatrix 5 :=
    { entries := D.entries.submatrix emb emb
      hollow := fun i => D.hollow (emb i)
      symmetric := fun i j => D.symmetric (emb i) (emb j)
      positive := fun i j hij => D.positive (emb i) (emb j) (by
        intro h; exact hij (Fin.castLE_injective hn h))
      triangle := fun i j k => D.triangle (emb i) (emb j) (emb k) }
  have he := five_rank_not_le_three E
  have hr : E.entries.rank ≤ D.entries.rank := D.entries.rank_submatrix_le emb emb
  omega

end PositiveMetricMatrix
end ProjectionAreaRankThree

/-!
# Weighted triangle obstruction

This file formalizes Corollary 5.2 of *Compatibility and realization of
coordinate projection areas*, and its extension to every dimension at
least five. The weight vector is allowed to have zero coordinates.
The matrix assumptions are exactly positivity off the diagonal,
symmetry, zero diagonal, and rank at most three.
-/


namespace ProjectionAreaRankThree

/-- The hypotheses on a matrix are geometric and independent of any weight vector. -/
structure PositiveHollowMatrix (n : ℕ) where
  entries : Matrix (Fin n) (Fin n) ℝ
  hollow : ∀ i, entries i i = 0
  symmetric : ∀ i j, entries i j = entries j i
  positive : ∀ i j, i ≠ j → 0 < entries i j

namespace PositiveHollowMatrix

variable {n : ℕ} (P : PositiveHollowMatrix n)

/-- The inequalities of Corollary 5.2, with precisely the three distinct labels
specified in the paper. -/
def WeightedTriangles (x : Fin n → ℝ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    P.entries i j * x k ≤ P.entries i k * x j + P.entries j k * x i

theorem nonnegative (i j : Fin n) : 0 ≤ P.entries i j := by
  by_cases hij : i = j
  · subst j; simp [P.hollow]
  · exact (P.positive i j hij).le

theorem weighted_all (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (ht : P.WeightedTriangles x) (i j k : Fin n) :
    P.entries i j * x k ≤ P.entries i k * x j + P.entries j k * x i := by
  by_cases hij : i = j
  · subst j
    rw [P.hollow, zero_mul]
    exact add_nonneg (mul_nonneg (P.nonnegative i k) (hx i))
      (mul_nonneg (P.nonnegative i k) (hx i))
  by_cases hik : i = k
  · subst k
    simp only [P.hollow, zero_mul, zero_add, P.symmetric j i]
    exact le_rfl
  by_cases hjk : j = k
  · subst k
    simp [P.hollow]
  exact ht i j k hij hik hjk

/-- Positive weights turn the weighted inequalities into the ordinary metric
inequalities. The rank bound is proved by literal diagonal matrix multiplication. -/
theorem positive_weights_impossible (hn : 5 ≤ n) (hrank : P.entries.rank ≤ 3)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) : ¬ P.WeightedTriangles x := by
  intro ht
  let D : PositiveMetricMatrix n :=
    { entries := fun i j => P.entries i j / (x i*x j)
      hollow := by intro i; simp [P.hollow]
      symmetric := by intro i j; rw [P.symmetric i j, mul_comm (x i) (x j)]
      positive := by intro i j hij; exact div_pos (P.positive i j hij) (mul_pos (hx i) (hx j))
      triangle := by
        intro i j k
        have ht' := P.weighted_all x (fun a => (hx a).le) ht i j k
        have hprod : 0 < x i*x j*x k := mul_pos (mul_pos (hx i) (hx j)) (hx k)
        apply (mul_le_mul_iff_of_pos_right hprod).mp
        have hi := (hx i).ne'
        have hj := (hx j).ne'
        have hk := (hx k).ne'
        calc
          (P.entries i j / (x i*x j)) * (x i*x j*x k) = P.entries i j*x k := by
            field_simp [hi,hj,hk] <;> ring
          _ ≤ P.entries i k*x j + P.entries j k*x i := ht'
          _ = (P.entries i k/(x i*x k) + P.entries k j/(x k*x j))*(x i*x j*x k) := by
            rw [P.symmetric k j]
            field_simp [hi,hj,hk]
            <;> ring }
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => (x i)⁻¹)
  have heq : D.entries = M * P.entries * M := by
    ext i j
    simp [D, M, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv, mul_inv_rev]
    ring
  have hD : D.entries.rank ≤ P.entries.rank := by
    rw [heq]
    exact (Matrix.rank_mul_le_left (M * P.entries) M).trans
      (Matrix.rank_mul_le_right M P.entries)
  have hfour := D.rank_at_least_four hn
  omega

/-- A nonzero nonnegative solution has at most one zero coordinate. -/
theorem positive_away_from_zero (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hne : x ≠ 0) (ht : P.WeightedTriangles x)
    (z : Fin n) (hz : x z = 0) : ∀ i, i ≠ z → 0 < x i := by
  have hex : ∃ k, 0 < x k := by
    by_contra h
    push_neg at h
    apply hne
    funext k
    exact le_antisymm (h k) (hx k)
  obtain ⟨k,hk⟩ := hex
  intro i hiz
  by_contra hi
  have hix : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i)
  have hzk : z ≠ k := by intro h; subst k; rw [hz] at hk; exact (lt_irrefl 0 hk)
  have hik : i ≠ k := by intro h; subst k; rw [hix] at hk; exact (lt_irrefl 0 hk)
  have hineq := ht z i k hiz.symm hzk hik
  rw [hix,hz,mul_zero,mul_zero,add_zero] at hineq
  exact (not_le_of_gt (mul_pos (P.positive z i hiz.symm) hk)) hineq

private theorem exists_uniform_positive_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  classical
  let δ := Finset.univ.inf' Finset.univ_nonempty f
  refine ⟨δ, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff (f := f) Finset.univ_nonempty).mpr (fun i _ => hf i)
  · intro i
    exact Finset.inf'_le _ (Finset.mem_univ i)

/-- Filling a single zero coordinate with a sufficiently small positive number
preserves every weighted triangle inequality, with no positive-margin hypothesis. -/
theorem exists_positive_weights (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hne : x ≠ 0) (ht : P.WeightedTriangles x) :
    ∃ y : Fin n → ℝ, (∀ i, 0 < y i) ∧ P.WeightedTriangles y := by
  classical
  by_cases hzero : ∃ z, x z = 0
  · obtain ⟨z,hz⟩ := hzero
    have hxpos := P.positive_away_from_zero x hx hne ht z hz
    let f : Fin n × Fin n → ℝ := fun ij =>
      if ij.1 = ij.2 ∨ ij.1 = z ∨ ij.2 = z then 1
      else (P.entries ij.1 z*x ij.2 + P.entries ij.2 z*x ij.1)/P.entries ij.1 ij.2
    have hf : ∀ ij, 0 < f ij := by
      intro ⟨i,j⟩
      dsimp [f]
      split_ifs with h
      · norm_num
      · push_neg at h
        exact div_pos (add_pos (mul_pos (P.positive i z h.2.1) (hxpos j h.2.2))
          (mul_pos (P.positive j z h.2.2) (hxpos i h.2.1))) (P.positive i j h.1)
    haveI : Nonempty (Fin n) := ⟨z⟩
    obtain ⟨δ,hδ,hbound⟩ := exists_uniform_positive_bound f hf
    let y : Fin n → ℝ := fun i => if i = z then δ else x i
    have hypos : ∀ i, 0 < y i := by
      intro i
      by_cases hiz : i = z
      · simp [y,hiz,hδ]
      · simpa [y,hiz] using hxpos i hiz
    have hxy : ∀ i, x i ≤ y i := by
      intro i
      by_cases hiz : i = z
      · subst i; simpa [y,hz] using hδ.le
      · simp [y,hiz]
    refine ⟨y,hypos,?_⟩
    intro i j k hij hik hjk
    by_cases hkz : k = z
    · subst k
      have hb := hbound (i,j)
      have hnot : ¬ (i = j ∨ i = z ∨ j = z) := by simp [hij,hik,hjk]
      simp only [f,hnot,if_false] at hb
      simp only [y,hik,hjk,if_false,if_pos rfl]
      simpa only [mul_comm] using (le_div_iff₀ (P.positive i j hij)).mp hb
    · calc
        P.entries i j * y k = P.entries i j*x k := by simp [y,hkz]
        _ ≤ P.entries i k*x j + P.entries j k*x i := ht i j k hij hik hjk
        _ ≤ P.entries i k*y j + P.entries j k*y i :=
          add_le_add (mul_le_mul_of_nonneg_left (hxy j) (P.nonnegative i k))
            (mul_le_mul_of_nonneg_left (hxy i) (P.nonnegative j k))
  · refine ⟨x,?_,ht⟩
    intro i
    exact lt_of_le_of_ne (hx i) (by intro h; exact hzero ⟨i,h.symm⟩)

/-- Corollary 5.2, in full: no nonzero nonnegative weight vector can satisfy the
inequalities on five labels. Rank at most three is enough for the contradiction. -/
theorem weighted_triangles_obstruction (hn : 5 ≤ n) (hrank : P.entries.rank ≤ 3) :
    ¬ ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ x ≠ 0 ∧ P.WeightedTriangles x := by
  rintro ⟨x,hx,hne,ht⟩
  obtain ⟨y,hy,hyt⟩ := P.exists_positive_weights x hx hne ht
  exact P.positive_weights_impossible hn hrank y hy hyt

end PositiveHollowMatrix
end ProjectionAreaRankThree

/-!
# Boundary quartets at rank three

For a positive hollow symmetric matrix of rank at most three, every
four-label principal matrix has determinant zero. The determinant's
Heron factorization then gives a boundary equality between the three
opposite root products. This is the algebraic input used in Section 2
and Theorem 1.1 of *Compatibility and realization of coordinate projection
areas*. No geometric realization or eigenvalue criterion is assumed.
-/


namespace ProjectionAreaRankThree

theorem hollowDet_root_factor (a b c d e f A B C : ℝ)
    (hA : A^2 = a*f) (hB : B^2 = b*e) (hC : C^2 = c*d) :
    hollowDet a b c d e f =
      -(A+B+C)*(A+B-C)*(A-B+C)*(-A+B+C) := by
  have hid : -(A+B+C)*(A+B-C)*(A-B+C)*(-A+B+C) =
      (A^2)^2 + (B^2)^2 + (C^2)^2 -
        2*(A^2)*(B^2) - 2*(A^2)*(C^2) - 2*(B^2)*(C^2) := by ring
  rw [hid, hA, hB, hC]
  unfold hollowDet
  ring

theorem root_boundary_of_hollowDet_zero (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hdet : hollowDet a b c d e f = 0) :
    Real.sqrt (a*f) = Real.sqrt (b*e) + Real.sqrt (c*d) ∨
    Real.sqrt (b*e) = Real.sqrt (a*f) + Real.sqrt (c*d) ∨
    Real.sqrt (c*d) = Real.sqrt (a*f) + Real.sqrt (b*e) := by
  have hA := Real.sqrt_pos.mpr (mul_pos ha hf)
  have hB := Real.sqrt_pos.mpr (mul_pos hb he)
  have hC := Real.sqrt_pos.mpr (mul_pos hc hd)
  rw [hollowDet_root_factor a b c d e f
    (Real.sqrt (a*f)) (Real.sqrt (b*e)) (Real.sqrt (c*d))
    (Real.sq_sqrt (mul_pos ha hf).le)
    (Real.sq_sqrt (mul_pos hb he).le)
    (Real.sq_sqrt (mul_pos hc hd).le)] at hdet
  rcases mul_eq_zero.mp hdet with hdet | hlast
  · rcases mul_eq_zero.mp hdet with hdet | hthird
    · rcases mul_eq_zero.mp hdet with hfirst | hsecond
      · linarith
      · exact Or.inr (Or.inr (by linarith))
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inl (by linarith)

namespace PositiveHollowMatrix

variable {n : ℕ} (P : PositiveHollowMatrix n)

theorem selected_det (i j k l : Fin n) :
    (P.entries.submatrix ![i,j,k,l] ![i,j,k,l]).det =
      hollowDet (P.entries i j) (P.entries i k) (P.entries i l)
        (P.entries j k) (P.entries j l) (P.entries k l) := by
  have heq : P.entries.submatrix ![i,j,k,l] ![i,j,k,l] =
      hollowMatrix4 (P.entries i j) (P.entries i k) (P.entries i l)
        (P.entries j k) (P.entries j l) (P.entries k l) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.submatrix, hollowMatrix4, P.hollow, P.symmetric]
  rw [heq, det_hollowMatrix4]

theorem four_det_eq_zero (hrank : P.entries.rank ≤ 3) (i j k l : Fin n) :
    hollowDet (P.entries i j) (P.entries i k) (P.entries i l)
      (P.entries j k) (P.entries j l) (P.entries k l) = 0 := by
  rw [← P.selected_det i j k l]
  by_contra hdet
  have hb := (P.entries.rank_submatrix_le ![i,j,k,l] ![i,j,k,l]).trans hrank
  rw [Matrix.rank_of_det_ne_zero hdet] at hb
  norm_num at hb

/-- Every four-label restriction is on the boundary of the four-dimensional
projection-area criterion. -/
theorem four_root_boundary (hrank : P.entries.rank ≤ 3)
    (i j k l : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Real.sqrt (P.entries i j * P.entries k l) =
      Real.sqrt (P.entries i k * P.entries j l) + Real.sqrt (P.entries i l * P.entries j k) ∨
    Real.sqrt (P.entries i k * P.entries j l) =
      Real.sqrt (P.entries i j * P.entries k l) + Real.sqrt (P.entries i l * P.entries j k) ∨
    Real.sqrt (P.entries i l * P.entries j k) =
      Real.sqrt (P.entries i j * P.entries k l) + Real.sqrt (P.entries i k * P.entries j l) := by
  exact root_boundary_of_hollowDet_zero _ _ _ _ _ _
    (P.positive i j hij) (P.positive i k hik) (P.positive i l hil)
    (P.positive j k hjk) (P.positive j l hjl) (P.positive k l hkl)
    (P.four_det_eq_zero hrank i j k l)

end PositiveHollowMatrix
end ProjectionAreaRankThree

/-!
# Zero entries at rank at most three

This file proves the matrix part of the zero-area reduction in Section 6
of *Compatibility and realization of coordinate projection areas*.
The rank assumption makes every four-by-four minor vanish. When one
off-diagonal entry is zero, the principal four-by-four determinant is a
square, so the two corresponding rows are proportional whenever both
are nonzero.

The result concerns actual matrix rank. It does not assume a spectral
criterion, a quotient construction, or any convex-body realization claim.
-/


namespace ProjectionAreaRankThree

private theorem nonnegative_rows_positively_proportional {ι : Type*}
    (r s : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 ≤ s i)
    (hrne : r ≠ 0) (hsne : s ≠ 0)
    (hminors : ∀ i j, r i * s j = r j * s i) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ i, s i = rho * r i := by
  classical
  have hrex : ∃ i, r i ≠ 0 := by
    by_contra! h
    apply hrne
    funext i
    exact h i
  have hsex : ∃ i, s i ≠ 0 := by
    by_contra! h
    apply hsne
    funext i
    exact h i
  obtain ⟨k, hk⟩ := hrex
  obtain ⟨j, hj⟩ := hsex
  have hrk : 0 < r k := lt_of_le_of_ne (hr k) hk.symm
  have hsj : 0 < s j := lt_of_le_of_ne (hs j) hj.symm
  have hsk : 0 < s k := by
    by_contra! hnonpos
    have hz : s k = 0 := le_antisymm hnonpos (hs k)
    have hm := hminors k j
    rw [hz, mul_zero] at hm
    have hp := mul_pos hrk hsj
    linarith
  refine ⟨s k / r k, div_pos hsk hrk, ?_⟩
  intro i
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hk).mpr
  nlinarith [hminors k i]


/-- A nonnegative symmetric hollow matrix, including zero rows. -/
structure NonnegativeHollowMatrix (n : ℕ) where
  entries : Matrix (Fin n) (Fin n) ℝ
  hollow : ∀ i, entries i i = 0
  symmetric : ∀ i j, entries i j = entries j i
  nonnegative : ∀ i j, 0 ≤ entries i j

namespace NonnegativeHollowMatrix

variable {n : ℕ} (Q : NonnegativeHollowMatrix n)

theorem selected_det (i j k l : Fin n) :
    (Q.entries.submatrix ![i,j,k,l] ![i,j,k,l]).det =
      hollowDet (Q.entries i j) (Q.entries i k) (Q.entries i l)
        (Q.entries j k) (Q.entries j l) (Q.entries k l) := by
  have heq : Q.entries.submatrix ![i,j,k,l] ![i,j,k,l] =
      hollowMatrix4 (Q.entries i j) (Q.entries i k) (Q.entries i l)
        (Q.entries j k) (Q.entries j l) (Q.entries k l) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.submatrix, hollowMatrix4, Q.hollow, Q.symmetric]
  rw [heq, det_hollowMatrix4]

theorem four_det_eq_zero (hrank : Q.entries.rank ≤ 3) (i j k l : Fin n) :
    hollowDet (Q.entries i j) (Q.entries i k) (Q.entries i l)
      (Q.entries j k) (Q.entries j l) (Q.entries k l) = 0 := by
  rw [← Q.selected_det i j k l]
  by_contra hdet
  have hb := (Q.entries.rank_submatrix_le ![i,j,k,l] ![i,j,k,l]).trans hrank
  rw [Matrix.rank_of_det_ne_zero hdet] at hb
  norm_num at hb

/-- A zero entry forces every cross minor of the corresponding rows to vanish. -/
theorem cross_minor_eq_zero (hrank : Q.entries.rank ≤ 3)
    (i j : Fin n) (hij : Q.entries i j = 0) (k l : Fin n) :
    Q.entries i k * Q.entries j l = Q.entries i l * Q.entries j k := by
  have hdet := Q.four_det_eq_zero hrank i j k l
  rw [hij] at hdet
  have hsq : (Q.entries i k * Q.entries j l - Q.entries i l * Q.entries j k)^2 = 0 := by
    convert hdet using 1 <;> unfold hollowDet <;> ring
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

/-- Vanishing cross minors suffice for the zero-row proportionality
criterion; the hypothesis can come from either low rank or local spectra. -/
theorem zero_iff_positive_proportional_of_cross_minors
    (hcross : ∀ i j : Fin n, Q.entries i j = 0 → ∀ k l : Fin n,
      Q.entries i k * Q.entries j l = Q.entries i l * Q.entries j k)
    (i j : Fin n) (hi : Q.entries i ≠ 0) (hj : Q.entries j ≠ 0) :
    Q.entries i j = 0 ↔
      ∃ r : ℝ, 0 < r ∧ ∀ k, Q.entries j k = r * Q.entries i k := by
  constructor
  · intro hij
    exact nonnegative_rows_positively_proportional
      (Q.entries i) (Q.entries j) (Q.nonnegative i) (Q.nonnegative j) hi hj
      (hcross i j hij)
  · rintro ⟨r, hr, hrow⟩
    have h := hrow j
    rw [Q.hollow] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hr.ne'

/-- On nonzero rows, zero entries are precisely positive proportionality. -/
theorem zero_iff_positive_proportional (hrank : Q.entries.rank ≤ 3)
    (i j : Fin n) (hi : Q.entries i ≠ 0) (hj : Q.entries j ≠ 0) :
    Q.entries i j = 0 ↔
      ∃ r : ℝ, 0 < r ∧ ∀ k, Q.entries j k = r * Q.entries i k :=
  Q.zero_iff_positive_proportional_of_cross_minors (Q.cross_minor_eq_zero hrank) i j hi hj

/-- The coordinate labels remaining after deleting zero rows. -/
abbrev ActiveLabels := {i : Fin n // Q.entries i ≠ 0}

/-- Zero mutual entries form an equivalence relation on the active labels. -/
def zeroSetoid (hrank : Q.entries.rank ≤ 3) : Setoid Q.ActiveLabels where
  r i j := Q.entries i.val j.val = 0
  iseqv := {
    refl := fun i => Q.hollow i.val
    symm := by
      intro i j hij
      simpa only [Q.symmetric j.val i.val] using hij
    trans := by
      intro i j k hij hjk
      obtain ⟨r, hr, hrow⟩ :=
        (Q.zero_iff_positive_proportional hrank i.val j.val i.property j.property).mp hij
      have h := hrow k.val
      rw [hjk] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hr.ne' }

/-- Distinct zero-area equivalence classes have strictly positive mutual entries. -/
theorem positive_of_not_zero_related (i j : Q.ActiveLabels)
    (hij : Q.entries i.val j.val ≠ 0) : 0 < Q.entries i.val j.val := by
  exact lt_of_le_of_ne (Q.nonnegative _ _) hij.symm


/-- The actual quotient of nonzero rows by zero mutual entry. -/
abbrev Classes (hrank : Q.entries.rank ≤ 3) := Quotient (Q.zeroSetoid hrank)

instance activeLabelsFintype : Fintype Q.ActiveLabels := Fintype.ofFinite _

instance classesFintype (hrank : Q.entries.rank ≤ 3) : Fintype (Q.Classes hrank) :=
  Fintype.ofFinite _

/-- The class of an active coordinate. -/
def activeClass (hrank : Q.entries.rank ≤ 3) (i : Q.ActiveLabels) : Q.Classes hrank :=
  Quotient.mk (Q.zeroSetoid hrank) i

/-- One actual original coordinate is selected from each class. -/
def quotientRep (hrank : Q.entries.rank ≤ 3) (c : Q.Classes hrank) : Fin n := c.out.val

/-- The quotient is literally a principal matrix of the original matrix. -/
def quotientEntries (hrank : Q.entries.rank ≤ 3) :
    Matrix (Q.Classes hrank) (Q.Classes hrank) ℝ :=
  Q.entries.submatrix (Q.quotientRep hrank) (Q.quotientRep hrank)

theorem quotientEntries_hollow (hrank : Q.entries.rank ≤ 3) (c : Q.Classes hrank) :
    Q.quotientEntries hrank c c = 0 := Q.hollow _

theorem quotientEntries_symmetric (hrank : Q.entries.rank ≤ 3)
    (c d : Q.Classes hrank) :
    Q.quotientEntries hrank c d = Q.quotientEntries hrank d c := Q.symmetric _ _

theorem quotientEntries_positive (hrank : Q.entries.rank ≤ 3)
    (c d : Q.Classes hrank) (hcd : c ≠ d) :
    0 < Q.quotientEntries hrank c d := by
  apply lt_of_le_of_ne (Q.nonnegative _ _)
  intro hzero
  apply hcd
  have hrel : (Q.zeroSetoid hrank).r c.out d.out := hzero.symm
  have hclasses := Quotient.sound hrel
  simpa only [Quotient.out_eq] using hclasses

theorem row_factor_exists (hrank : Q.entries.rank ≤ 3) (i : Q.ActiveLabels) :
    ∃ r : ℝ, 0 < r ∧ ∀ k,
      Q.entries i.val k = r * Q.entries (Q.quotientRep hrank (Q.activeClass hrank i)) k := by
  have hzero : Q.entries (Q.quotientRep hrank (Q.activeClass hrank i)) i.val = 0 :=
    Quotient.mk_out (s := Q.zeroSetoid hrank) i
  exact (Q.zero_iff_positive_proportional hrank
    (Q.quotientRep hrank (Q.activeClass hrank i)) i.val
    (Q.activeClass hrank i).out.property i.property).mp hzero

/-- The positive scalar relating a nonzero row to its chosen representative. -/
def rowFactor (hrank : Q.entries.rank ≤ 3) (i : Q.ActiveLabels) : ℝ :=
  Classical.choose (row_factor_exists Q hrank i)

theorem rowFactor_pos (hrank : Q.entries.rank ≤ 3) (i : Q.ActiveLabels) :
    0 < Q.rowFactor hrank i := (Classical.choose_spec (row_factor_exists Q hrank i)).1

theorem rowFactor_spec (hrank : Q.entries.rank ≤ 3) (i : Q.ActiveLabels) (k : Fin n) :
    Q.entries i.val k = Q.rowFactor hrank i *
      Q.entries (Q.quotientRep hrank (Q.activeClass hrank i)) k :=
  (Classical.choose_spec (row_factor_exists Q hrank i)).2 k

theorem activeClass_out (hrank : Q.entries.rank ≤ 3) (c : Q.Classes hrank) :
    Q.activeClass hrank c.out = c := Quotient.out_eq c

/-- The scalar at each chosen representative is exactly one. -/
theorem rowFactor_out (hrank : Q.entries.rank ≤ 3) (c : Q.Classes hrank) :
    Q.rowFactor hrank c.out = 1 := by
  have hex : ∃ k, Q.entries c.out.val k ≠ 0 := by
    by_contra! h
    apply c.out.property
    funext k
    exact h k
  obtain ⟨k, hk⟩ := hex
  have hf := Q.rowFactor_spec hrank c.out k
  rw [Q.activeClass_out hrank c] at hf
  change Q.entries c.out.val k = Q.rowFactor hrank c.out * Q.entries c.out.val k at hf
  apply mul_right_cancel₀ hk
  simpa only [one_mul] using hf.symm

/-- Reconstruction of every entry between two active coordinates. -/
theorem entries_factor (hrank : Q.entries.rank ≤ 3) (i j : Q.ActiveLabels) :
    Q.entries i.val j.val = Q.rowFactor hrank i * Q.rowFactor hrank j *
      Q.quotientEntries hrank (Q.activeClass hrank i) (Q.activeClass hrank j) := by
  rw [Q.rowFactor_spec hrank i j.val]
  rw [Q.symmetric (Q.quotientRep hrank (Q.activeClass hrank i)) j.val]
  rw [Q.rowFactor_spec hrank j (Q.quotientRep hrank (Q.activeClass hrank i))]
  rw [Q.symmetric (Q.quotientRep hrank (Q.activeClass hrank j))
    (Q.quotientRep hrank (Q.activeClass hrank i))]
  dsimp [quotientEntries, Matrix.submatrix]
  ring

/-- The linear coordinate-replication matrix, with zero rows restored. -/
def replicationMatrix (hrank : Q.entries.rank ≤ 3) :
    Matrix (Fin n) (Q.Classes hrank) ℝ := by
  classical
  exact fun i c => if hi : Q.entries i ≠ 0 then
    if Q.activeClass hrank ⟨i, hi⟩ = c then Q.rowFactor hrank ⟨i, hi⟩ else 0
    else 0

/-- The quotient reconstruction as a literal matrix product. -/
theorem matrix_factorization (hrank : Q.entries.rank ≤ 3) :
    Q.entries = Q.replicationMatrix hrank * Q.quotientEntries hrank *
      (Q.replicationMatrix hrank).transpose := by
  classical
  ext i j
  by_cases hi : Q.entries i ≠ 0
  · by_cases hj : Q.entries j ≠ 0
    · simp only [Matrix.mul_apply, Matrix.transpose_apply]
      simp only [replicationMatrix, dif_pos hi, dif_pos hj]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, mul_ite, mul_zero, Finset.sum_ite_eq']
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        Q.entries_factor hrank ⟨i, hi⟩ ⟨j, hj⟩
    · have hz : Q.entries j = 0 := not_not.mp hj
      have he : Q.entries i j = 0 := by
        simpa only [hz, Pi.zero_apply] using Q.symmetric i j
      simp [he, Matrix.mul_apply, Matrix.transpose_apply, replicationMatrix, hj]
  · have hz : Q.entries i = 0 := not_not.mp hi
    simp [hz, Matrix.mul_apply, Matrix.transpose_apply, replicationMatrix, hi]

/-- Deleting the zero rows and identifying proportional rows preserves rank. -/
theorem quotientEntries_rank (hrank : Q.entries.rank ≤ 3) :
    (Q.quotientEntries hrank).rank = Q.entries.rank := by
  apply le_antisymm
  · exact Q.entries.rank_submatrix_le (Q.quotientRep hrank) (Q.quotientRep hrank)
  · conv_lhs => rw [Q.matrix_factorization hrank]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)


/-- The quotient matrix with the usual `Fin m` index type. -/
def quotientPositive (hrank : Q.entries.rank ≤ 3) :
    PositiveHollowMatrix (Fintype.card (Q.Classes hrank)) where
  entries := (Q.quotientEntries hrank).submatrix
    (Fintype.equivFin (Q.Classes hrank)).symm
    (Fintype.equivFin (Q.Classes hrank)).symm
  hollow := fun i => Q.quotientEntries_hollow hrank _
  symmetric := fun i j => Q.quotientEntries_symmetric hrank _ _
  positive := by
    intro i j hij
    exact Q.quotientEntries_positive hrank _ _ (fun h =>
      hij ((Fintype.equivFin (Q.Classes hrank)).symm.injective h))

theorem quotientPositive_rank (hrank : Q.entries.rank ≤ 3) :
    (Q.quotientPositive hrank).entries.rank = Q.entries.rank := by
  change ((Q.quotientEntries hrank).submatrix
    (Fintype.equivFin (Q.Classes hrank)).symm
    (Fintype.equivFin (Q.Classes hrank)).symm).rank = Q.entries.rank
  rw [Matrix.rank_submatrix, Q.quotientEntries_rank hrank]

/-- A quotient with five or more classes has the full weighted obstruction. -/
theorem quotient_weighted_obstruction (hrank : Q.entries.rank ≤ 3)
    (hclasses : 5 ≤ Fintype.card (Q.Classes hrank)) :
    ¬ ∃ x : Fin (Fintype.card (Q.Classes hrank)) → ℝ,
      (∀ i, 0 ≤ x i) ∧ x ≠ 0 ∧ (Q.quotientPositive hrank).WeightedTriangles x := by
  apply (Q.quotientPositive hrank).weighted_triangles_obstruction hclasses
  rw [Q.quotientPositive_rank hrank]
  exact hrank

end NonnegativeHollowMatrix
end ProjectionAreaRankThree

/-! ## Module audit

The following commands display the complete types and transitive axiom
dependencies of the Section 5 obstruction and the Section 6 quotient algebra.
-/

#check @ProjectionAreaRankThree.PositiveMetricMatrix.rank_at_least_four
#print axioms ProjectionAreaRankThree.PositiveMetricMatrix.rank_at_least_four

#check @ProjectionAreaRankThree.PositiveHollowMatrix.weighted_triangles_obstruction
#print axioms ProjectionAreaRankThree.PositiveHollowMatrix.weighted_triangles_obstruction

#check @ProjectionAreaRankThree.PositiveHollowMatrix.four_root_boundary
#print axioms ProjectionAreaRankThree.PositiveHollowMatrix.four_root_boundary

#check @ProjectionAreaRankThree.NonnegativeHollowMatrix.zero_iff_positive_proportional
#print axioms ProjectionAreaRankThree.NonnegativeHollowMatrix.zero_iff_positive_proportional

#check @ProjectionAreaRankThree.NonnegativeHollowMatrix.matrix_factorization
#print axioms ProjectionAreaRankThree.NonnegativeHollowMatrix.matrix_factorization

#check @ProjectionAreaRankThree.NonnegativeHollowMatrix.quotientEntries_rank
#print axioms ProjectionAreaRankThree.NonnegativeHollowMatrix.quotientEntries_rank
