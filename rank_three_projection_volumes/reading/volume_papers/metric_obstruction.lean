module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace VolumePapers.RankThree

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
  let R : ℝ :=
    x1 * ((x2 ^ 2 + (x3 + y) * (x4 + z)) * (x3 + x4 + y + z) +
      x2 * (x3 ^ 2 + x4 ^ 2 + 2 * (x3 + x4) * (y + z) +
        (y + z) ^ 2 + 2 * y * z)) +
    x2 * x3 * x4 * (x2 + x3 + x4) +
    y * (x2 + x3 + x4 + y) * x3 * (x2 + x4) +
    z * (x2 + x3 + x4 + z) * x4 * (x2 + x3) +
    y * z * (x2 + x3 + x4) * (x2 + x3 + x4 + y + z) +
    2 * y * z * x3 * x4
  have hR : 0 ≤ R := by dsimp [R]; positivity
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
    dsimp [cutDet, hollowDet, R]
    ring
  rw [hid]
  exact mul_neg_of_neg_of_pos (by norm_num)
    (add_pos_of_pos_of_nonneg hprod hR)

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
    rw [hdet] at hneg
    exact (lt_irrefl (0 : ℝ)) hneg
  have hx2 : x2 = 0 := by
    by_contra hx
    have hneg := cutDet_negative_first x2 x1 x4 x3 y z
      (lt_of_le_of_ne h2 (Ne.symm hx)) h1 h4 h3 hy hz hc hb (by linarith)
    rw [cutDet_swap12] at hneg
    rw [hdet] at hneg
    exact (lt_irrefl (0 : ℝ)) hneg
  have hx3 : x3 = 0 := by
    by_contra hx
    have hneg := cutDet_negative_first x3 x4 x1 x2 y z
      (lt_of_le_of_ne h3 (Ne.symm hx)) h4 h1 h2 hy hz (by linarith) (by linarith) ha
    rw [cutDet_swap13] at hneg
    rw [hdet] at hneg
    exact (lt_irrefl (0 : ℝ)) hneg
  have hx4 : x4 = 0 := by
    by_contra hx
    have hneg := cutDet_negative_first x4 x3 x2 x1 y z
      (lt_of_le_of_ne h4 (Ne.symm hx)) h3 h2 h1 hy hz (by linarith) (by linarith) (by linarith)
    rw [cutDet_swap14] at hneg
    rw [hdet] at hneg
    exact (lt_irrefl (0 : ℝ)) hneg
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
  have h1 : 0 ≤ x1 := by dsimp [x1]; linarith only [ht1]
  have h2 : 0 ≤ x2 := by dsimp [x2]; linarith only [ht2]
  have h3 : 0 ≤ x3 := by dsimp [x3]; linarith only [ht3]
  have h4 : 0 ≤ x4 := by dsimp [x4]; linarith only [ht4]
  have hy : 0 ≤ y := by dsimp [y]; linarith only [hm1]
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hm2]
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
  exact ⟨by linarith only [hx1, hx2, hx3, hx4],
    by linarith only [hx1, hx2, hx3, hx4],
    by linarith only [hx1, hx2, hx3, hx4],
    by linarith only [hx1, hx2, hx3, hx4]⟩


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
  simp [hollowMatrix4, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Fin.sum_univ_succ, Fin.succAbove, hollowDet]
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
  have hr : (D.entries.submatrix ![i,j,k,l] ![i,j,k,l]).rank = 4 := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hdet
  have hb := (D.entries.rank_submatrix_le ![i,j,k,l] ![i,j,k,l]).trans hrank
  omega

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
        intro h; apply hij; exact Fin.ext (congrArg (fun a : Fin n => a.val) h))
      triangle := fun i j k => D.triangle (emb i) (emb j) (emb k) }
  have he := five_rank_not_le_three E
  have hr : E.entries.rank ≤ D.entries.rank := D.entries.rank_submatrix_le emb emb
  omega

end PositiveMetricMatrix
end VolumePapers.RankThree
