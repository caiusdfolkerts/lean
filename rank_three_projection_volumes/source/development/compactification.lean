module

public import Lean.Elab.Print
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.Matrix
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.Logic.Equiv.Set
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Sequences
public import volume_polynomials.mixed_volume_basis_part01
public import volume_polynomials.mixed_volume_basis_part02

set_option autoImplicit false

/- Source module: VolumePapers.MetricObstruction. SHA256: 33a23f32b0cad5a8340a810f9693761916bca9448566a79d20ceb4f320c49e61 -/
section DevelopmentSource0













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
end
end
end DevelopmentSource0

/- Source module: VolumePapers.WeightedTriangles. SHA256: 86c6e8a6d22e0b7fbea256dc0371340e6d01a5d4d310bfb329751ae701358ea9 -/
section DevelopmentSource1







set_option autoImplicit false

@[expose] public section
noncomputable section

namespace VolumePapers.RankThree

/-- The hypotheses on a matrix are geometric and independent of any weight vector. -/
structure PositiveHollowMatrix (n : ℕ) where
  entries : Matrix (Fin n) (Fin n) ℝ
  hollow : ∀ i, entries i i = 0
  symmetric : ∀ i j, entries i j = entries j i
  positive : ∀ i j, i ≠ j → 0 < entries i j

namespace PositiveHollowMatrix

variable {n : ℕ} (P : PositiveHollowMatrix n)

/-- The inequalities of Corollary 2.3, with precisely the three distinct labels
specified in the paper. -/
def WeightedTriangles (x : Fin n → ℝ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    P.entries i j * x k ≤ P.entries i k * x j + P.entries j k * x i

theorem nonnegative (i j : Fin n) : 0 ≤ P.entries i j := by
  by_cases hij : i = j
  · subst j; rw [P.hollow]
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
    simp [D, M, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv, mul_inv_rev] <;>
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
  · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hf i)
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

/-- Corollary 2.3, in full: no nonzero nonnegative weight vector can satisfy the
inequalities on five labels. Rank at most three is enough for the contradiction. -/
theorem weighted_triangles_obstruction (hn : 5 ≤ n) (hrank : P.entries.rank ≤ 3) :
    ¬ ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ x ≠ 0 ∧ P.WeightedTriangles x := by
  rintro ⟨x,hx,hne,ht⟩
  obtain ⟨y,hy,hyt⟩ := P.exists_positive_weights x hx hne ht
  exact P.positive_weights_impossible hn hrank y hy hyt

end PositiveHollowMatrix
end VolumePapers.RankThree

namespace VolumePapers.RankThree

/-- Matrix-form interface to Corollary 2.3. The number of labels is arbitrary,
provided it is at least five. No geometric realization is assumed. -/
theorem no_nonnegative_weighted_triangles {n : ℕ} (hn : 5 ≤ n)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hollow : ∀ i, P i i = 0)
    (symmetric : ∀ i j, P i j = P j i)
    (positive : ∀ i j, i ≠ j → 0 < P i j)
    (rank : P.rank ≤ 3)
    (x : Fin n → ℝ) (nonnegative : ∀ i, 0 ≤ x i) (nonzero : x ≠ 0) :
    ¬ (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      P i j * x k ≤ P i k * x j + P j k * x i) := by
  let Q : PositiveHollowMatrix n := ⟨P, hollow, symmetric, positive⟩
  intro weighted
  exact Q.weighted_triangles_obstruction hn rank
    ⟨x, nonnegative, nonzero, weighted⟩

/-- Exactly the five-label, rank-three assertion of the paper's Corollary 2.3. -/
theorem corollary_two_three
    (P : Matrix (Fin 5) (Fin 5) ℝ)
    (hollow : ∀ i, P i i = 0)
    (symmetric : ∀ i j, P i j = P j i)
    (positive : ∀ i j, i ≠ j → 0 < P i j)
    (rank : P.rank = 3) :
    ¬ ∃ x : Fin 5 → ℝ, (∀ i, 0 ≤ x i) ∧ x ≠ 0 ∧
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        P i j * x k ≤ P i k * x j + P j k * x i := by
  rintro ⟨x, hx, hne, hweighted⟩
  exact no_nonnegative_weighted_triangles (by omega) P hollow symmetric positive
    rank.le x hx hne hweighted

end VolumePapers.RankThree
end
end
end DevelopmentSource1

/- Source module: Projection.Normalization.MinorMaximum. SHA256: 9738f6ced4a88dbb019274639ce70d6cdae142e3fb15e6dd4fd08b5b601cca5c -/
section DevelopmentSource2






/-!
# Finite maxima of actual matrix minors

The maximum ranges over all row and column selections, including repeated
indices. Repeated rows or columns have determinant zero; allowing them makes
replacement-column and bordered-minor bounds direct finite-maximum statements.
A positive maximizing minor is proved to have injective row and column maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset
open scoped NNReal

namespace ProjectionVolumes

/-- Largest absolute determinant of an `r × r` submatrix. -/
def minorMaximum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : ℝ :=
  ((Finset.univ : Finset ((Fin r → Fin n) × (Fin r → Fin n))).sup
    (fun maps => NNReal.mk |(M.submatrix maps.1 maps.2).det| (abs_nonneg _)) : ℝ≥0)

lemma minorMaximum_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    0 ≤ minorMaximum M r := by
  exact NNReal.coe_nonneg _

lemma minorMaximum_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    minorMaximum M 0 = 1 := by
  simp [minorMaximum]
  exact Finset.sup_const ⟨(Fin.elim0, Fin.elim0), Finset.mem_univ _⟩ 1

lemma minor_le_maximum {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin r → Fin n) :
    |(M.submatrix rows cols).det| ≤ minorMaximum M r := by
  have h := Finset.le_sup
    (f := fun maps : (Fin r → Fin n) × (Fin r → Fin n) =>
      NNReal.mk |(M.submatrix maps.1 maps.2).det| (abs_nonneg _))
    (Finset.mem_univ (rows, cols))
  simpa only [minorMaximum, NNReal.coe_mk] using (NNReal.coe_le_coe.mpr h)

/-- A positive maximum is attained by one row and column selection. -/
theorem exists_maximal_minor {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hpos : 0 < minorMaximum M r) :
    ∃ rows cols : Fin r → Fin n,
      |(M.submatrix rows cols).det| = minorMaximum M r := by
  let s : Finset ((Fin r → Fin n) × (Fin r → Fin n)) := Finset.univ
  let f : ((Fin r → Fin n) × (Fin r → Fin n)) → ℝ≥0 :=
    fun maps => NNReal.mk |(M.submatrix maps.1 maps.2).det| (abs_nonneg _)
  have hpos' : (0 : ℝ≥0) < s.sup f := hpos
  obtain ⟨maps, hm, hle⟩ := (Finset.le_sup_iff hpos').mp (le_refl (s.sup f))
  have heq : f maps = s.sup f := le_antisymm (Finset.le_sup hm) hle
  exact ⟨maps.1, maps.2, congrArg (fun x : ℝ≥0 => (x : ℝ)) heq⟩

/-- A nonzero minor has no repeated row. -/
lemma injective_rows_of_minor_ne_zero {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (hdet : (M.submatrix rows cols).det ≠ 0) : Function.Injective rows := by
  intro i j hij
  by_contra hne
  apply hdet
  apply Matrix.det_zero_of_row_eq hne
  funext a
  simp only [Matrix.submatrix_apply, hij]

/-- A nonzero minor has no repeated column. -/
lemma injective_cols_of_minor_ne_zero {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (hdet : (M.submatrix rows cols).det ≠ 0) : Function.Injective cols := by
  intro i j hij
  by_contra hne
  apply hdet
  apply Matrix.det_zero_of_column_eq hne
  intro a
  simp only [Matrix.submatrix_apply, hij]

/-- Replacing a pivot column by any original column stays within the maximum
of minors of the same order. -/
lemma replacement_column_minor_bound {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (i : Fin r) (j : Fin n) :
    |((M.submatrix rows cols).updateCol i (fun a => M (rows a) j)).det| ≤
      minorMaximum M r := by
  have hmat : (M.submatrix rows cols).updateCol i (fun a => M (rows a) j) =
      M.submatrix rows (Function.update cols i j) := by
    ext a b
    by_cases h : b = i <;> simp [Matrix.updateCol_apply, h]
  rw [hmat]
  exact minor_le_maximum M rows _

/-- The analogous replacement-row bound. -/
lemma replacement_row_minor_bound {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (i : Fin r) (j : Fin n) :
    |((M.submatrix rows cols).updateRow i (fun a => M j (cols a))).det| ≤
      minorMaximum M r := by
  have hmat : (M.submatrix rows cols).updateRow i (fun a => M j (cols a)) =
      M.submatrix (Function.update rows i j) cols := by
    ext a b
    by_cases h : a = i <;> simp [Matrix.updateRow_apply, h]
  rw [hmat]
  exact minor_le_maximum M _ cols

/-- Reindexing allows the same bound for a minor with any finite index type. -/
lemma minor_le_maximum_card {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : ι → Fin n) :
    |(M.submatrix rows cols).det| ≤ minorMaximum M (Fintype.card ι) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  calc
    |(M.submatrix rows cols).det| =
        |((M.submatrix rows cols).submatrix e e).det| :=
      congrArg abs (Matrix.det_submatrix_equiv_self e (M.submatrix rows cols)).symm
    _ ≤ minorMaximum M (Fintype.card ι) :=
      minor_le_maximum M (rows ∘ e) (cols ∘ e)

/-- A cofactor of a pivot is an actual minor of the preceding order. -/
lemma cofactor_minor_bound {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin (r + 1) → Fin n)
    (i j : Fin (r + 1)) :
    |((M.submatrix rows cols).submatrix j.succAbove i.succAbove).det| ≤
      minorMaximum M r :=
  minor_le_maximum M (rows ∘ j.succAbove) (cols ∘ i.succAbove)

/-- A bordered pivot is an actual minor of the following order, including when
the appended row or column repeats an existing one. -/
lemma bordered_minor_bound {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (i j : Fin n) :
    |(Matrix.fromBlocks (M.submatrix rows cols)
        (fun a (_ : Unit) => M (rows a) j)
        (fun (_ : Unit) b => M i (cols b))
        (fun (_ _ : Unit) => M i j)).det| ≤ minorMaximum M (r + 1) := by
  have h := minor_le_maximum_card M (Sum.elim rows (fun _ : Unit => i))
    (Sum.elim cols (fun _ : Unit => j))
  have hmat : M.submatrix (Sum.elim rows (fun _ : Unit => i))
      (Sum.elim cols (fun _ : Unit => j)) =
      Matrix.fromBlocks (M.submatrix rows cols)
        (fun a (_ : Unit) => M (rows a) j)
        (fun (_ : Unit) b => M i (cols b))
        (fun (_ _ : Unit) => M i j) := by
    ext a b
    cases a <;> cases b <;> rfl
  rw [hmat] at h
  simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique] using h

end ProjectionVolumes
end
end
end DevelopmentSource2

/- Source module: Projection.Normalization.MinorScales. SHA256: e49b728721e87964ecc9ee004308dee3f3f632bf8eadea12393ff47e978f79df -/
section DevelopmentSource3





/-!
# Selecting a scale from maximal minors

This is the finite scalar step in the maximal-minor alternative to the proof of
Theorem 3.1. The sequence `d j` is intended to be the largest absolute `j`-minor;
the theorem only needs its nonnegativity and `d 0 = 1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
open Finset

namespace ProjectionVolumes

/-- A finite family of minor bounds admits a scale and an active order below
`k`, with exact equality at that order and weak bounds at every smaller order. -/
theorem exists_minor_scale {k : ℕ} (hk : 0 < k)
    (d : ℕ → ℝ) (hd : ∀ j < k, 0 ≤ d j) (hzero : d 0 = 1) :
    ∃ r < k, ∃ g : ℝ, 1 ≤ g ∧
      d r = g ^ (k - r) ∧
      (∀ j < k, d j ≤ g ^ (k - j)) := by
  let root : ℕ → ℝ := fun j => (d j) ^ ((k - j : ℕ) : ℝ)⁻¹
  obtain ⟨r, hr, hmax⟩ :=
    Finset.exists_max_image (Finset.range k) root (Finset.nonempty_range_iff.mpr hk.ne')
  have hrk : r < k := Finset.mem_range.mp hr
  have hg : 1 ≤ root r := by
    have h := hmax 0 (Finset.mem_range.mpr hk)
    simpa only [root, hzero, Real.one_rpow] using h
  refine ⟨r, hrk, root r, hg, ?_, ?_⟩
  · exact (Real.rpow_inv_natCast_pow (hd r hrk) (by omega)).symm
  · intro j hj
    calc
      d j = root j ^ (k - j) :=
        (Real.rpow_inv_natCast_pow (hd j hj) (by omega)).symm
      _ ≤ root r ^ (k - j) :=
        pow_le_pow_left₀ (Real.rpow_nonneg (hd j hj) _) (hmax j (Finset.mem_range.mpr hj)) _

/-- The chosen pivot determinant is strictly positive, even if some other
minor maxima vanish. -/
lemma active_minor_pos {k r : ℕ} {d : ℕ → ℝ} {g : ℝ}
    (hg : 1 ≤ g) (hexact : d r = g ^ (k - r)) : 0 < d r := by
  rw [hexact]
  exact pow_pos (lt_of_lt_of_le zero_lt_one hg) _

/-- The cofactor bound needed for the inverse pivot block. -/
lemma previous_minor_le {k r : ℕ} {d : ℕ → ℝ} {g : ℝ}
    (hr : 0 < r) (hrk : r < k)
    (hexact : d r = g ^ (k - r))
    (hmax : ∀ j < k, d j ≤ g ^ (k - j)) : d (r - 1) ≤ g * d r := by
  have h := hmax (r - 1) (by omega)
  have he : k - (r - 1) = (k - r) + 1 := by omega
  simpa only [he, pow_succ, ← hexact, mul_comm] using h

/-- The bordered-minor bound needed for the Schur complement, away from its
last possible order. -/
lemma next_minor_le {k r : ℕ} {d : ℕ → ℝ} {g : ℝ}
    (hg : 0 ≤ g) (hrk : r + 1 < k)
    (hexact : d r = g ^ (k - r))
    (hmax : ∀ j < k, d j ≤ g ^ (k - j)) : g * d (r + 1) ≤ d r := by
  have h := mul_le_mul_of_nonneg_left (hmax (r + 1) hrk) hg
  have he : k - r = (k - (r + 1)) + 1 := by omega
  calc
    g * d (r + 1) ≤ g * g ^ (k - (r + 1)) := h
    _ = g ^ (k - r) := by rw [he, pow_succ, mul_comm]
    _ = d r := hexact.symm

/-- At the last possible pivot order, the pivot determinant equals the scale. -/
lemma last_active_minor_eq_scale {k r : ℕ} {d : ℕ → ℝ} {g : ℝ}
    (hr : r + 1 = k) (hexact : d r = g ^ (k - r)) : d r = g := by
  have he : k - r = 1 := by omega
  simpa only [he, pow_one] using hexact

end ProjectionVolumes
end
end
end DevelopmentSource3

/- Source module: Projection.Normalization.PivotNormalizer. SHA256: 79e775d4bcc3ace1c20123881f6cef4a10d70e3cb233220001dec467be9f4d7d -/
section DevelopmentSource4




/-!
# The block transformation in maximal-minor normalization

The statements in this file are matrix identities and quantitative consequences
of explicitly stated pivot-minor bounds. No geometric realization assertion is
assumed or encoded in these hypotheses.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace ProjectionVolumes

variable {m n p : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The row transformation determined by an invertible pivot block. -/
def pivotNormalizer (g : ℝ) (B : Matrix m m ℝ) (C : Matrix n m ℝ) :
    Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  Matrix.fromBlocks (g⁻¹ • B⁻¹) 0 (-(C * B⁻¹)) 1

/-- Applying the normalizer leaves an identity pivot block and a scaled Schur
complement. -/
theorem pivotNormalizer_mul (g : ℝ) (hg : g ≠ 0)
    (B : Matrix m m ℝ) (A : Matrix m p ℝ) (C : Matrix n m ℝ)
    (D : Matrix n p ℝ) (hB : B.det ≠ 0) :
    g • (pivotNormalizer g B C * Matrix.fromBlocks B A C D) =
      Matrix.fromBlocks 1 (B⁻¹ * A) 0 (g • (D - C * B⁻¹ * A)) := by
  have hinv : B⁻¹ * B = 1 := B.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hB)
  simp [pivotNormalizer, Matrix.fromBlocks_multiply, Matrix.smul_mul,
    Matrix.mul_assoc, hinv, Matrix.fromBlocks_smul, smul_smul, hg,
    sub_eq_add_neg, add_comm]

/-- The exact determinant of the row transformation. -/
theorem pivotNormalizer_det (g : ℝ) (B : Matrix m m ℝ) (C : Matrix n m ℝ) :
    (pivotNormalizer g B C).det = (g⁻¹) ^ Fintype.card m * B.det⁻¹ := by
  simp [pivotNormalizer, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

/-- The exact absolute determinant, in the positive-scale case. -/
theorem pivotNormalizer_abs_det (g : ℝ) (hg : 0 < g)
    (B : Matrix m m ℝ) (C : Matrix n m ℝ) :
    |(pivotNormalizer g B C).det| = (g⁻¹) ^ Fintype.card m * |B.det|⁻¹ := by
  rw [pivotNormalizer_det, abs_mul, abs_pow, abs_inv, abs_of_pos hg, abs_inv]

/-- The normalizer has the scaling factor required to preserve the marked
mixed-volume coefficients with `k` segment arguments. -/
theorem pivotNormalizer_scaling (g : ℝ) (hg : 0 < g)
    (B : Matrix m m ℝ) (C : Matrix n m ℝ) {k : ℕ}
    (hrk : Fintype.card m ≤ k) (hB : |B.det| = g ^ (k - Fintype.card m)) :
    g ^ k * |(pivotNormalizer g B C).det| = 1 := by
  rw [pivotNormalizer_abs_det g hg B C, hB, inv_pow, ← mul_inv, ← pow_add,
    Nat.add_sub_of_le hrk, mul_inv_cancel₀ (pow_ne_zero _ hg.ne')]

/-- Every vector with zero pivot coordinates is fixed exactly. -/
theorem pivotNormalizer_fixes (g : ℝ) (B : Matrix m m ℝ) (C : Matrix n m ℝ)
    (v : n → ℝ) :
    pivotNormalizer g B C *ᵥ Sum.elim (fun _ : m => 0) v =
      Sum.elim (fun _ : m => 0) v := by
  rw [pivotNormalizer, Matrix.fromBlocks_mulVec]
  change Sum.elim
      ((g⁻¹ • B⁻¹) *ᵥ (0 : m → ℝ) + (0 : Matrix m n ℝ) *ᵥ v)
      ((-(C * B⁻¹)) *ᵥ (0 : m → ℝ) + (1 : Matrix n n ℝ) *ᵥ v) =
    Sum.elim (0 : m → ℝ) v
  simp only [Matrix.mulVec_zero, Matrix.zero_mulVec, Matrix.one_mulVec,
    add_zero, zero_add]

/-- Cramer's rule turns maximality of replacement-column minors into the
entry bound for `B⁻¹ A`. -/
theorem inverse_mulVec_bound (B : Matrix m m ℝ) (v : m → ℝ)
    (hB : B.det ≠ 0)
    (hminor : ∀ i, |(B.updateCol i v).det| ≤ |B.det|) :
    ∀ i, |(B⁻¹ *ᵥ v) i| ≤ 1 := by
  intro i
  have h := congrFun (B.det_smul_inv_mulVec_eq_cramer v (isUnit_iff_ne_zero.mpr hB)) i
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] at h
  have hbound : |B.det| * |(B⁻¹ *ᵥ v) i| ≤ |B.det| * 1 := by
    rw [← abs_mul, h, mul_one]
    exact hminor i
  exact (mul_le_mul_iff_of_pos_left (abs_pos.mpr hB)).mp hbound

/-- The row version of Cramer's bound. -/
theorem vecMul_inverse_bound (B : Matrix m m ℝ) (v : m → ℝ)
    (hB : B.det ≠ 0)
    (hminor : ∀ i, |(B.updateRow i v).det| ≤ |B.det|) :
    ∀ i, |(v ᵥ* B⁻¹) i| ≤ 1 := by
  intro i
  have h := congrFun (B.det_smul_inv_vecMul_eq_cramer_transpose v
    (isUnit_iff_ne_zero.mpr hB)) i
  simp only [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply,
    Matrix.updateCol_transpose, Matrix.det_transpose] at h
  have hbound : |B.det| * |(v ᵥ* B⁻¹) i| ≤ |B.det| * 1 := by
    rw [← abs_mul, h, mul_one]
    exact hminor i
  exact (mul_le_mul_iff_of_pos_left (abs_pos.mpr hB)).mp hbound

/-- The inverse pivot entries are bounded by the previous-order minors divided
by the pivot determinant. -/
theorem inverse_entry_bound {r : ℕ}
    (B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (hB : B.det ≠ 0)
    (d : ℝ)
    (hminor : ∀ i j : Fin (r + 1), |(B.submatrix j.succAbove i.succAbove).det| ≤ d) :
    ∀ i j, |B⁻¹ i j| ≤ d / |B.det| := by
  intro i j
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_fin_succ_eq_det_submatrix, abs_mul, abs_inv, abs_pow,
    abs_neg, abs_one, one_pow, one_mul]
  rw [div_eq_mul_inv, mul_comm d]
  exact mul_le_mul_of_nonneg_left (hminor i j) (inv_nonneg.mpr (abs_nonneg B.det))

/-- The bordered determinant is the pivot determinant times the corresponding
Schur-complement entry. This is the exact identity used for the next-order
minor bound. -/
theorem bordered_pivot_det (B : Matrix m m ℝ) (A : Matrix m p ℝ)
    (C : Matrix n m ℝ) (D : Matrix n p ℝ) (hB : B.det ≠ 0)
    (i : n) (j : p) :
    (Matrix.fromBlocks B (fun a (_ : Unit) => A a j)
      (fun (_ : Unit) b => C i b) (fun (_ _ : Unit) => D i j)).det =
      B.det * (D - C * B⁻¹ * A) i j := by
  letI : Invertible B := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hB)
  have h := Matrix.det_fromBlocks₁₁ B
    (fun a (_ : Unit) => A a j) (fun (_ : Unit) b => C i b)
    (fun (_ _ : Unit) => D i j)
  rw [Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (n := Unit)] at h
  convert h using 1 <;> rfl

end ProjectionVolumes
end
end
end DevelopmentSource4

/- Source module: Projection.Normalization.MatrixNormalization. SHA256: ba1e23207c41d751c9c98f508f7a218d466905c93083d81b25d57062e9b128d0 -/
section DevelopmentSource5






/-!
# Normalization by maximal minors

The proof uses actual minors of the input matrix. A maximizing pivot of order
strictly below `k` determines a bounded change of rows. The change fixes every
vector supported outside the pivot coordinates and has exactly the determinant
factor required for the marked mixed volumes with `k` segment arguments.

No nonsingularity hypothesis on the input matrix is needed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace ProjectionVolumes

/-- Complete an injection by its set-theoretic complement, without choosing an
ordering of that complement. -/
def selectionEquiv {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    ι ⊕ {x : κ // x ∉ Set.range f} ≃ κ := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun x => x ∈ Set.range f))

@[simp] lemma selectionEquiv_inl {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) (i : ι) : selectionEquiv f hf (Sum.inl i) = f i := rfl

@[simp] lemma selectionEquiv_inr {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) (i : {x : κ // x ∉ Set.range f}) :
    selectionEquiv f hf (Sum.inr i) = i := rfl

/-- The entry of any matrix is a minor of order one. -/
lemma entry_le_minorMaximum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |M i j| ≤ minorMaximum M 1 := by
  simpa only [Matrix.det_fin_one, Matrix.submatrix_apply] using
    minor_le_maximum M (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)

/-- All quantitative bounds for the pivot transformation. The tail row and
column maps may be arbitrary; the eventual application uses their complements.
-/
theorem maximalMinor_block_bounds {n r k : ℕ} {τ κ : Type*}
    [Fintype τ] [DecidableEq τ]
    (M : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin (r + 1) → Fin n) (tailRows : τ → Fin n) (tailCols : κ → Fin n)
    (g : ℝ) (hg : 1 ≤ g) (hrk : r + 1 < k)
    (hpivot : |(M.submatrix rows cols).det| = minorMaximum M (r + 1))
    (hexact : minorMaximum M (r + 1) = g ^ (k - (r + 1)))
    (hmax : ∀ j < k, minorMaximum M j ≤ g ^ (k - j)) :
    let B := M.submatrix rows cols
    let A := M.submatrix rows tailCols
    let C := M.submatrix tailRows cols
    let D := M.submatrix tailRows tailCols
    (∀ i j, |pivotNormalizer g B C i j| ≤ 1) ∧
    (∀ i j, |(g • (pivotNormalizer g B C * Matrix.fromBlocks B A C D)) i j| ≤
      max 1 (minorMaximum M k)) ∧
    g ^ k * |(pivotNormalizer g B C).det| = 1 := by
  classical
  dsimp only
  let B := M.submatrix rows cols
  let A := M.submatrix rows tailCols
  let C := M.submatrix tailRows cols
  let D := M.submatrix tailRows tailCols
  have hgpos : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hp : |B.det| = minorMaximum M (r + 1) := hpivot
  have hdp : 0 < minorMaximum M (r + 1) := active_minor_pos hg hexact
  have hbpos : 0 < |B.det| := hp.symm ▸ hdp
  have hb : B.det ≠ 0 := abs_pos.mp hbpos
  have hprevious : minorMaximum M r ≤ g * minorMaximum M (r + 1) := by
    simpa only [Nat.add_sub_cancel] using
      previous_minor_le (d := minorMaximum M) (by omega) hrk hexact hmax
  have hBbound : ∀ i j, |B⁻¹ i j| ≤ g := by
    intro i j
    refine (inverse_entry_bound B hb (minorMaximum M r)
      (cofactor_minor_bound M rows cols) i j).trans ?_
    apply (div_le_iff₀ hbpos).mpr
    simpa only [hp] using hprevious
  have hAbound : ∀ i j, |(B⁻¹ * A) i j| ≤ 1 := by
    intro i j
    exact inverse_mulVec_bound B (fun a => M (rows a) (tailCols j)) hb
      (fun a => hp.symm ▸ replacement_column_minor_bound M rows cols a (tailCols j)) i
  have hCbound : ∀ i j, |(C * B⁻¹) i j| ≤ 1 := by
    intro i j
    exact vecMul_inverse_bound B (fun a => M (tailRows i) (cols a)) hb
      (fun a => hp.symm ▸ replacement_row_minor_bound M rows cols a (tailRows i)) j
  have hSchur : ∀ i j, |g * (D - C * B⁻¹ * A) i j| ≤ max 1 (minorMaximum M k) := by
    intro i j
    have hbminor : |(Matrix.fromBlocks B (fun a (_ : Unit) => A a j)
        (fun (_ : Unit) b => C i b) (fun (_ _ : Unit) => D i j)).det| ≤
        minorMaximum M (r + 1 + 1) := by
      simpa only [B, A, C, D, Matrix.submatrix_apply] using
        bordered_minor_bound M rows cols (tailRows i) (tailCols j)
    rw [bordered_pivot_det B A C D hb i j, abs_mul, hp] at hbminor
    rw [abs_mul, abs_of_pos hgpos]
    by_cases hnext : r + 1 + 1 < k
    · have hn := next_minor_le hgpos.le hnext hexact hmax
      have hbound : g * |(D - C * B⁻¹ * A) i j| ≤ 1 := by
        apply (mul_le_mul_iff_of_pos_left hdp).mp
        calc
          minorMaximum M (r + 1) * (g * |(D - C * B⁻¹ * A) i j|) =
              g * (minorMaximum M (r + 1) * |(D - C * B⁻¹ * A) i j|) := by
                rw [mul_left_comm]
          _ ≤ g * minorMaximum M (r + 1 + 1) :=
            mul_le_mul_of_nonneg_left hbminor hgpos.le
          _ ≤ minorMaximum M (r + 1) := hn
          _ = minorMaximum M (r + 1) * 1 := (mul_one _).symm
      exact hbound.trans (le_max_left _ _)
    · have hlast : r + 1 + 1 = k := by omega
      have hdg := last_active_minor_eq_scale hlast hexact
      rw [hdg, hlast] at hbminor
      exact hbminor.trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change |g⁻¹ * B⁻¹ i j| ≤ 1
        rw [abs_mul, abs_inv, abs_of_pos hgpos]
        have h := mul_le_mul_of_nonneg_left (hBbound i j) (inv_nonneg.mpr hgpos.le)
        simpa only [inv_mul_cancel₀ hgpos.ne'] using h
      | inr j => simp [pivotNormalizer]
    | inr i =>
      cases j with
      | inl j => simpa only [pivotNormalizer, Matrix.fromBlocks_apply₂₁,
          Matrix.neg_apply, abs_neg] using hCbound i j
      | inr j =>
        by_cases h : i = j <;> simp [pivotNormalizer, Matrix.one_apply, h]
  · rw [pivotNormalizer_mul g hgpos.ne' B A C D hb]
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hi : |(1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i j| ≤ 1 := by
          by_cases h : i = j <;> simp [Matrix.one_apply, h]
        exact hi.trans (le_max_left _ _)
      | inr j => exact (hAbound i j).trans (le_max_left _ _)
    | inr i =>
      cases j with
      | inl j =>
        simpa only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, abs_zero] using
          (zero_le_one.trans (le_max_left (1 : ℝ) (minorMaximum M k)))
      | inr j => exact hSchur i j
  · apply pivotNormalizer_scaling g hgpos B C
    · simpa only [Fintype.card_fin] using hrk.le
    · simpa only [Fintype.card_fin] using hp.trans hexact

/-- Every square real matrix admits a uniformly bounded row normalization
fixing the complement of fewer than `k` coordinates. The transformed entries
are controlled solely by its minors of order `k`.

The determinant identity is exact. In particular, the normalizing matrix is
invertible. This theorem applies to all `k > 0`, so it includes the entire
parameter range used in Theorem 3.1 of the paper.
-/
theorem exists_matrix_normalization {n k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (g : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)),
      1 ≤ g ∧ G.det ≠ 0 ∧ s.card < k ∧
      (∀ i j, |G i j| ≤ 1) ∧
      (∀ i j, |(g • (G * M)) i j| ≤ max 1 (minorMaximum M k)) ∧
      g ^ k * |G.det| = 1 ∧
      (∀ v : Fin n → ℝ, (∀ i ∈ s, v i = 0) → G *ᵥ v = v) := by
  classical
  obtain ⟨q, hqk, g, hg, hexact, hmax⟩ := exists_minor_scale hk (minorMaximum M)
    (fun j _ => minorMaximum_nonneg M j) (minorMaximum_zero M)
  cases q with
  | zero =>
    have hg1 : g = 1 := (pow_eq_one_iff_of_nonneg (zero_le_one.trans hg) hk.ne').mp
      (by simpa only [minorMaximum_zero, Nat.sub_zero] using hexact.symm)
    subst g
    refine ⟨1, 1, ∅, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simpa only [Finset.card_empty] using hk
    · intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · intro i j
      simp only [one_smul, Matrix.one_mul]
      by_cases hk1 : k = 1
      · simpa only [hk1] using
          (entry_le_minorMaximum M i j).trans (le_max_right 1 (minorMaximum M 1))
      · have h1 : 1 < k := by omega
        exact ((entry_le_minorMaximum M i j).trans
          (by simpa only [one_pow] using hmax 1 h1)).trans (le_max_left _ _)
    · simp
    · intro v _
      exact Matrix.one_mulVec v
  | succ r =>
    have hdp : 0 < minorMaximum M (r + 1) := active_minor_pos hg hexact
    obtain ⟨rows, cols, hpivot⟩ := exists_maximal_minor M hdp
    have hb : (M.submatrix rows cols).det ≠ 0 := abs_pos.mp (hpivot.symm ▸ hdp)
    have hrows := injective_rows_of_minor_ne_zero M rows cols hb
    have hcols := injective_cols_of_minor_ne_zero M rows cols hb
    let τ := {i : Fin n // i ∉ Set.range rows}
    let κ := {i : Fin n // i ∉ Set.range cols}
    let er : Fin (r + 1) ⊕ τ ≃ Fin n := selectionEquiv rows hrows
    let ec : Fin (r + 1) ⊕ κ ≃ Fin n := selectionEquiv cols hcols
    let B := M.submatrix rows cols
    let A := M.submatrix rows (fun i : κ => i.val)
    let C := M.submatrix (fun i : τ => i.val) cols
    let D := M.submatrix (fun i : τ => i.val) (fun i : κ => i.val)
    let Gb := pivotNormalizer g B C
    let G := Gb.submatrix er.symm er.symm
    let s := Finset.univ.image rows
    obtain ⟨hGb, hGbM, hscale⟩ := maximalMinor_block_bounds M rows cols
      (fun i : τ => i.val) (fun i : κ => i.val) g hg hqk hpivot hexact hmax
    have hblock : M.submatrix er ec = Matrix.fromBlocks B A C D := by
      ext i j
      cases i <;> cases j <;> rfl
    have hdet : G.det = Gb.det := Matrix.det_submatrix_equiv_self er.symm Gb
    have hscaleG : g ^ k * |G.det| = 1 := by rwa [hdet]
    have hne : G.det ≠ 0 := by
      intro hz
      rw [hz, abs_zero, mul_zero] at hscaleG
      exact zero_ne_one hscaleG
    have hGpull : G.submatrix er er = Gb := by
      ext i j
      exact congrArg₂ Gb (er.symm_apply_apply i) (er.symm_apply_apply j)
    have hproduct : (g • (G * M)).submatrix er ec =
        g • (Gb * Matrix.fromBlocks B A C D) := by
      simp only [Matrix.submatrix_smul, Pi.smul_apply]
      rw [← Matrix.submatrix_mul_equiv G M er er ec,
        hGpull, hblock]
    refine ⟨g, G, s, hg, hne, ?_, ?_, ?_, hscaleG, ?_⟩
    · simpa only [s, Finset.card_image_of_injective _ hrows,
        Finset.card_univ, Fintype.card_fin] using hqk
    · intro i j
      exact hGb (er.symm i) (er.symm j)
    · intro i j
      have h := hGbM (er.symm i) (ec.symm j)
      rw [← hproduct] at h
      simpa only [Matrix.submatrix_apply, er.apply_symm_apply, ec.apply_symm_apply] using h
    · intro v hv
      have hvrows : ∀ i, v (rows i) = 0 := fun i =>
        hv (rows i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have hvpull : v ∘ er = Sum.elim (fun _ => 0) (fun i : τ => v i.val) := by
        funext i
        cases i with
        | inl i => exact hvrows i
        | inr i => rfl
      change Gb.submatrix er.symm er.symm *ᵥ v = v
      rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hvpull, pivotNormalizer_fixes]
      funext i
      have h := congrFun hvpull (er.symm i)
      simpa only [Function.comp_apply, er.apply_symm_apply] using h.symm

end ProjectionVolumes
end
end
end DevelopmentSource5

/- Source module: Projection.Basic. SHA256: 3dbff99fd032d53fb0f82308f16dc4600dd32145e912085b05af031862beb0d2 -/
section DevelopmentSource6





@[expose] public section
set_option autoImplicit false

/-!
# Coordinate projection volumes of actual convex bodies

These definitions use Mathlib's nonempty compact convex sets and Lebesgue
measure on the retained coordinate space. Lower-dimensional bodies are allowed.
The topology on arrays is the ordinary finite product topology.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise

namespace RankThreeProjection

abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Body (n : ℕ) := ConvexBody (Space n)
abbrev Array (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Coordinates retained after deleting the finite set `I`. -/
abbrev Retained {n : ℕ} (I : Finset (Fin n)) := {j : Fin n // j ∉ I}

/-- The literal coordinate restriction map. -/
def deleteCoordinates {n : ℕ} (I : Finset (Fin n)) :
    Space n →L[ℝ] (Retained I → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.val)

/-- A projection body is the image under coordinate deletion. -/
def projectedBody {n : ℕ} (I : Finset (Fin n)) (K : Body n) :
    ConvexBody (Retained I → ℝ) :=
  VolumePolynomials.mapBody (deleteCoordinates I) K

/-- Ordinary Lebesgue volume in the retained coordinate space. -/
def coordinateVolume {n : ℕ} (I : Finset (Fin n)) (K : Body n) : ℝ :=
  volume.real (projectedBody I K : Set (Retained I → ℝ))

/-- The hollow complementary projection-volume array from the paper. -/
def projectionArray {n : ℕ} (K : Body n) : Array n := fun i j =>
  if i = j then 0 else coordinateVolume {i, j} K

/-- The actual realization locus; no geometric properties are built into it. -/
def projectionLocus (n : ℕ) : Set (Array n) := Set.range (projectionArray (n := n))

/-- The closure in the finite-dimensional space of all arrays. -/
def closedProjectionLocus (n : ℕ) : Set (Array n) := closure (projectionLocus n)

/-- The three elementary hypotheses appearing in the principal theorem. -/
def PositiveHollowSymmetric {n : ℕ} (P : Array n) : Prop :=
  (∀ i, P i i = 0) ∧ (∀ i j, P i j = P j i) ∧ (∀ i j, i ≠ j → 0 < P i j)

@[simp] theorem deleteCoordinates_apply {n : ℕ} (I : Finset (Fin n))
    (x : Space n) (j : Retained I) : deleteCoordinates I x j = x j.val := rfl

@[simp] theorem projectedBody_coe {n : ℕ} (I : Finset (Fin n)) (K : Body n) :
    (projectedBody I K : Set (Retained I → ℝ)) = deleteCoordinates I '' (K : Set (Space n)) := rfl

@[simp] theorem projectionArray_diagonal {n : ℕ} (K : Body n) (i : Fin n) :
    projectionArray K i i = 0 := by simp [projectionArray]

theorem projectionArray_symmetric {n : ℕ} (K : Body n) (i j : Fin n) :
    projectionArray K i j = projectionArray K j i := by
  by_cases h : i = j
  · subst j; rfl
  · simp only [projectionArray, if_neg h, if_neg (Ne.symm h)]
    congr 1
    exact Finset.pair_comm i j

theorem projectionArray_nonnegative {n : ℕ} (K : Body n) (i j : Fin n) :
    0 ≤ projectionArray K i j := by
  unfold projectionArray
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

theorem projectionArray_mem_closed {n : ℕ} (K : Body n) :
    projectionArray K ∈ closedProjectionLocus n :=
  subset_closure ⟨K, rfl⟩

theorem isClosed_closedProjectionLocus (n : ℕ) : IsClosed (closedProjectionLocus n) :=
  isClosed_closure

end RankThreeProjection
end
end
end DevelopmentSource6

/- Source module: Projection.Extrusion. SHA256: e59267d238ade8171636e9aa5900f9219bb4758c079d1702ba4f1968aa4d0ed7 -/
section DevelopmentSource7




@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise

namespace RankThreeProjection

open VolumePolynomials

section Segment
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual segment, including its degenerate case. -/
def segmentBody (a b : E) : ConvexBody E where
  carrier := segment ℝ a b
  convex' := convex_segment a b
  isCompact' := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  nonempty' := ⟨a, left_mem_segment ℝ a b⟩

/-- An origin-based segment; translation invariance relates it to the
centered segment used in the paper. -/
def originSegment (v : E) : ConvexBody E := segmentBody 0 v

def centeredSegment (v : E) : ConvexBody E :=
  segmentBody (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)

theorem map_segmentBody {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (a b : E) :
    mapBody L (segmentBody a b) = segmentBody (L a) (L b) := by
  apply ConvexBody.ext
  exact image_segment ℝ L.toLinearMap.toAffineMap a b

theorem map_centeredSegment {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (v : E) :
    mapBody L (centeredSegment v) = centeredSegment (L v) := by
  simp only [centeredSegment, map_segmentBody, map_smul]

theorem translate_segmentBody (v a b : E) :
    translateBody v (segmentBody a b) = segmentBody (v + a) (v + b) := by
  apply ConvexBody.ext
  rw [coe_translateBody]
  change v +ᵥ segment ℝ a b = segment ℝ (v + a) (v + b)
  simp only [vadd_segment, vadd_eq_add]

theorem centered_eq_translate_origin (v : E) :
    centeredSegment v = translateBody (-(1 / 2 : ℝ) • v) (originSegment v) := by
  rw [centeredSegment, originSegment, translate_segmentBody]
  congr 1
  · simp
  · calc
      (1 / 2 : ℝ) • v = (-(1 / 2 : ℝ) + 1) • v := by congr 1; norm_num
      _ = (-(1 / 2 : ℝ)) • v + v := by rw [add_smul, one_smul]

end Segment

section Product
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def axisBody : ConvexBody (ℝ × E) where
  carrier := PlanarExtrusion.horizontal 1
  convex' := (convex_Icc 0 1).prod (convex_singleton 0)
  isCompact' := PlanarExtrusion.horizontal_compact 1
  nonempty' := ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, rfl⟩⟩

theorem smul_axisBody_coe {r : ℝ} (hr : 0 ≤ r) :
    ((r • axisBody (E := E) : ConvexBody (ℝ × E)) : Set (ℝ × E)) =
      PlanarExtrusion.horizontal r := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    simp [body_zero_smul, axisBody, PlanarExtrusion.horizontal,
      Set.prod_singleton]
    exact (Set.singleton_zero : ({(0 : ℝ × E)} : Set (ℝ × E)) = 0).symm
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hq, hq0⟩
      change q.2 = 0 at hq0
      change (0 ≤ r * q.1 ∧ r * q.1 ≤ r) ∧ r • q.2 = 0
      exact ⟨⟨mul_nonneg hr.le hq.1,
        (mul_le_mul_of_nonneg_left hq.2 hr.le).trans_eq (mul_one r)⟩,
        by rw [hq0, smul_zero]⟩
    · intro hp
      rcases hp with ⟨hp, hp0⟩
      change p.2 = 0 at hp0
      refine ⟨(p.1 / r, 0), ?_, ?_⟩
      · exact ⟨⟨div_nonneg hp.1 hr.le, (div_le_one hr).mpr hp.2⟩, rfl⟩
      · apply Prod.ext
        · change r * (p.1 / r) = p.1
          field_simp [hr.ne']
        · simpa using hp0.symm

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Exact polynomial form of interval-fiber extrusion in every dimension. -/
theorem volumePolynomial_axis {d : ℕ} (K : Fin d → ConvexBody (ℝ × E)) :
    volumePolynomial volume (Fin.cons axisBody K) =
      MvPolynomial.rename Fin.succ (volumePolynomial volume K) +
      X 0 * MvPolynomial.rename Fin.succ
        (volumePolynomial volume (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ E) (K i))) := by
  apply volumePolynomial_eq_of_eval
  intro t ht
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename]
  rw [volumePolynomial_eval volume K (t ∘ Fin.succ) (fun i => ht i.succ),
    volumePolynomial_eval volume _ (t ∘ Fin.succ) (fun i => ht i.succ)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  let C : ConvexBody (ℝ × E) := ∑ i, t i.succ • K i
  have hmap : (∑ i, t i.succ • mapBody (ContinuousLinearMap.snd ℝ ℝ E) (K i)) =
      mapBody (ContinuousLinearMap.snd ℝ ℝ E) C := by
    simp only [C, ← mapBody_smul]
    exact (map_sum (mapBodyHom (ContinuousLinearMap.snd ℝ ℝ E)) _ _).symm
  rw [hmap]
  change volume.real (C : Set (ℝ × E)) + t 0 *
    volume.real (PlanarExtrusion.projection (C : Set (ℝ × E))) =
    volume.real ((t 0 • axisBody (E := E) + C : ConvexBody (ℝ × E)) : Set (ℝ × E))
  rw [add_comm (t 0 • axisBody (E := E)) C, ConvexBody.coe_add,
    smul_axisBody_coe (E := E) (ht 0)]
  exact (PlanarExtrusion.realVolume_add_horizontal C.isCompact C.convex (ht 0)).symm

theorem squarefree_succ (d : ℕ) :
    squarefreeExponent (d + 1) = Finsupp.single 0 1 +
      (squarefreeExponent d).mapDomain Fin.succ := by
  rw [← oldSquarefreeLift_eq_mapDomain]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem coeff_rename_succ_squarefree {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    (MvPolynomial.rename Fin.succ p).coeff (squarefreeExponent (d + 1)) = 0 := by
  apply MvPolynomial.coeff_rename_eq_zero
  intro u hu
  have hzero : (u.mapDomain Fin.succ) (0 : Fin (d + 1)) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨i, hi⟩
    exact Fin.succ_ne_zero i hi
  rw [hu, squarefreeExponent_apply] at hzero
  exact (Nat.one_ne_zero hzero).elim

/-- Deleting one coordinate by one actual segment has exactly the factorial
normalization of standard mixed volume. No dimension restriction is assumed
on the individual bodies. -/
theorem mixedVolume_axis {d : ℕ} (K : Fin d → ConvexBody (ℝ × E)) :
    (d + 1 : ℝ) * mixedVolume volume (Fin.cons axisBody K) =
      mixedVolume volume (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ E) (K i)) := by
  unfold mixedVolume
  rw [volumePolynomial_axis, MvPolynomial.coeff_add,
    coeff_rename_succ_squarefree, zero_add, squarefree_succ,
    MvPolynomial.coeff_X_mul, MvPolynomial.coeff_rename_mapDomain _ (Fin.succ_injective d)]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hd : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hn : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end Product
end RankThreeProjection
end
end
end DevelopmentSource7

/- Source module: Projection.Topology. SHA256: 47367206b02c1eaf9697bce0222900dc4ba55589cedf7e328e710dd3d92aa93c -/
section DevelopmentSource8






@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Module Filter
open scoped Pointwise Topology

namespace RankThreeProjection
open VolumePolynomials

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Simultaneous continuity in the linear map and the compact convex body. -/
theorem continuous_mapBody_joint :
    Continuous (fun p : (E →L[ℝ] F) × ConvexBody E => mapBody p.1 p.2) := by
  apply isometry_bodyToNonemptyCompacts.comp_continuous_iff.mp
  change Continuous (fun p : (E →L[ℝ] F) × ConvexBody E =>
    (bodyToNonemptyCompacts p.2).map p.1 p.1.continuous)
  apply Continuous.nonemptyCompacts_map'
    (continuous_bodyToNonemptyCompacts.comp continuous_snd)
  fun_prop

theorem continuous_mapBody_fixed (L : E →L[ℝ] F) : Continuous (mapBody L) :=
  continuous_mapBody_joint.comp (continuous_const.prodMk continuous_id)

theorem continuous_originSegment : Continuous (originSegment (E := E)) := by
  let L : E →L[ℝ] (ℝ →L[ℝ] E) :=
    ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)
  have he (v : E) : mapBody (L v) (segmentBody (0 : ℝ) 1) = originSegment v := by
    rw [map_segmentBody]
    simp [L, originSegment]
  have hc : Continuous (fun v : E => mapBody (L v) (segmentBody (0 : ℝ) 1)) := by
    simpa only [Function.comp_def] using
      continuous_mapBody_joint.comp
        (L.continuous.prodMk
          (continuous_const : Continuous (fun _ : E => segmentBody (0 : ℝ) 1)))
  simpa only [he] using hc

theorem continuous_centeredSegment : Continuous (centeredSegment (E := E)) := by
  have he (v : E) : mapBody
      (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ) v)
      (segmentBody (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) = centeredSegment v := by
    rw [map_segmentBody]
    rfl
  have hc : Continuous (fun v : E => mapBody
      (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ) v)
      (segmentBody (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) := by
    simpa only [Function.comp_def] using
      continuous_mapBody_joint.comp
        ((ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous.prodMk
          (continuous_const : Continuous
            (fun _ : E => segmentBody (-(1 / 2 : ℝ)) (1 / 2 : ℝ))))
  simpa only [he] using hc

theorem continuous_coordinateVolume {n : ℕ} (I : Finset (Fin n)) :
    Continuous (coordinateVolume I) :=
  (continuous_convexBody_realMeasure volume).comp (continuous_mapBody_fixed (deleteCoordinates I))

theorem continuous_projectionArray {n : ℕ} : Continuous (projectionArray (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · simpa only [projectionArray, if_pos hij] using (continuous_const : Continuous (fun _ : Body n => (0 : ℝ)))
  · simpa only [projectionArray, if_neg hij] using continuous_coordinateVolume {i, j}

/-- Exactly the subsets of coordinates deleted in a projection of codimension k. -/
abbrev Deleted (n k : ℕ) := {I : Finset (Fin n) // I.card = k}

def allProjectionArray {n k : ℕ} (K : Body n) : Deleted n k → ℝ :=
  fun I => coordinateVolume I.val K

def allProjectionLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  Set.range (allProjectionArray (n := n) (k := k))

/-- The repeated body and exactly k marked centered segments. The chosen order
is the increasing order on the deleted coordinate set. -/
def markedTuple {n k : ℕ} (K : Body n) (U : Fin n → Space n) (I : Deleted n k) :
    Fin (n - k + k) → Body n :=
  Fin.append (fun _ : Fin (n - k) => K)
    (fun j : Fin k => centeredSegment (U (I.val.orderEmbOfFin I.property j)))

def allMarkedArray {n k : ℕ} (K : Body n) (U : Fin n → Space n) : Deleted n k → ℝ :=
  fun I => (n.factorial : ℝ) / ((n - k).factorial : ℝ) *
    mixedVolume volume (markedTuple K U I)

/-- Affine dimension, taken from the actual affine span of the body. -/
def bodyDimension {n : ℕ} (K : Body n) : ℕ :=
  finrank ℝ (affineSpan ℝ (K : Set (Space n))).direction

theorem continuous_allProjectionArray {n k : ℕ} :
    Continuous (allProjectionArray (n := n) (k := k)) := by
  exact continuous_pi (fun I => continuous_coordinateVolume I.val)

theorem continuous_allMarkedArray {n k : ℕ} :
    Continuous (fun p : Body n × (Fin n → Space n) => allMarkedArray (k := k) p.1 p.2) := by
  apply continuous_pi
  intro I
  apply Continuous.const_mul
  apply (continuous_mixedVolume volume (n - k + k)).comp
  apply continuous_pi
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [markedTuple, Fin.append_left] using
      (continuous_fst : Continuous (fun p : Body n × (Fin n → Space n) => p.1))
  · intro j
    simpa only [markedTuple, Fin.append_right, Function.comp_def] using
      continuous_centeredSegment.comp ((continuous_apply _).comp continuous_snd)

end RankThreeProjection
end
end
end DevelopmentSource8

/- Source module: Projection.Normalization.Compactness. SHA256: 4413f58240f07ca76c9b818e389c8edb5140847990698b09585cab434a1bbc8c -/
section DevelopmentSource9






/-!
# Compactness with a retained coordinate disk

The maximal-minor normalization fixes the complement of fewer than `k`
coordinates. Consequently, every normalized body contains one of finitely many
fixed coordinate disks. This file proves that the resulting family of actual
bodies and marks is compact, and that every member has the dimension required
in Theorem 3.1. No compactness or dimension property is assumed as an axiom.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric Module MeasureTheory Filter
open scoped Topology Pointwise

namespace RankThreeProjection
open VolumePolynomials

/-- The closed disk in the coordinate subspace complementary to `s`. -/
def coordinateDisk {n : ℕ} (s : Finset (Fin n)) (ρ : ℝ) : Set (Space n) :=
  {x | ‖x‖ ≤ ρ ∧ ∀ i ∈ s, x i = 0}

theorem zero_mem_coordinateDisk {n : ℕ} (s : Finset (Fin n)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (0 : Space n) ∈ coordinateDisk s ρ := ⟨by simpa using hρ, by simp⟩

theorem coordinateDisk_subset_closedBall {n : ℕ} (s : Finset (Fin n)) (ρ : ℝ) :
    coordinateDisk s ρ ⊆ closedBall 0 ρ := fun _ hx => mem_closedBall_zero_iff.mpr hx.1

/-- A fixed coordinate disk forces the literal affine span to contain the
entire complementary coordinate subspace. -/
theorem coordinateDisk_dimension {n : ℕ} (s : Finset (Fin n))
    {ρ : ℝ} (hρ : 0 < ρ) (K : Body n)
    (hK : coordinateDisk s ρ ⊆ (K : Set (Space n))) :
    n - s.card ≤ bodyDimension K := by
  classical
  have hzero : (0 : Space n) ∈ K := hK (zero_mem_coordinateDisk s hρ.le)
  let v : Retained s → Space n := fun i => Pi.single i.val 1
  have hli : LinearIndependent ℝ v := by
    simpa only [v, Function.comp_def, Pi.basisFun_apply] using
      (Pi.basisFun ℝ (Fin n)).linearIndependent.comp
        (fun i : Retained s => i.val) Subtype.val_injective
  have hv : ∀ j, v j ∈ (affineSpan ℝ (K : Set (Space n))).direction := by
    intro j
    have hpoint : ρ • v j ∈ K := by
      apply hK
      refine ⟨?_, ?_⟩
      · simpa only [v, norm_smul, Pi.norm_single, norm_one, mul_one,
          Real.norm_of_nonneg hρ.le] using (le_rfl : ρ ≤ ρ)
      · intro i hi
        have hij : i ≠ j.val := by
          intro heq
          exact j.property (heq ▸ hi)
        simp [v, Pi.single_apply, hij, Ne.symm hij]
    have hd : ρ • v j ∈ (affineSpan ℝ (K : Set (Space n))).direction := by
      simpa only [vsub_eq_sub, sub_zero] using
        AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ (K : Set (Space n)) hpoint)
          (subset_affineSpan ℝ (K : Set (Space n)) hzero)
    have hh := (affineSpan ℝ (K : Set (Space n))).direction.smul_mem ρ⁻¹ hd
    simpa only [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul] using hh
  have hspan : Submodule.span ℝ (Set.range v) ≤
      (affineSpan ℝ (K : Set (Space n))).direction := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hv j
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli] at hdim
  simpa only [Retained, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_coe, bodyDimension] using hdim

/-- Containing an arbitrary fixed set is a closed condition on convex bodies
in the Hausdorff topology. -/
theorem isClosed_bodies_containing {n : ℕ} (A : Set (Space n)) :
    IsClosed {K : Body n | A ⊆ (K : Set (Space n))} := by
  simp only [Set.subset_def, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _hx =>
    (isClosed_compacts_contains x).preimage continuous_bodyToNonemptyCompacts

/-- Bodies between a fixed coordinate disk and a fixed ambient ball. -/
def normalizedBodies {n : ℕ} (s : Finset (Fin n)) (ρ R : ℝ) : Set (Body n) :=
  {K | coordinateDisk s ρ ⊆ (K : Set (Space n)) ∧
    (K : Set (Space n)) ⊆ closedBall 0 R}

theorem isCompact_normalizedBodies {n : ℕ} (s : Finset (Fin n))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (R : ℝ) : IsCompact (normalizedBodies s ρ R) := by
  have hbase := isCompact_bodies_in_compact (isCompact_closedBall (0 : Space n) R)
  have heq : normalizedBodies s ρ R =
      {K : Body n | (0 : Space n) ∈ K ∧ (K : Set (Space n)) ⊆ closedBall 0 R} ∩
      {K : Body n | coordinateDisk s ρ ⊆ (K : Set (Space n))} := by
    ext K
    constructor
    · intro h
      exact ⟨⟨h.1 (zero_mem_coordinateDisk s hρ), h.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, h.1.2⟩
  rw [heq]
  exact hbase.inter_right (isClosed_bodies_containing (coordinateDisk s ρ))

/-- The bounded family used after maximal-minor normalization. The finite
union includes every possible set of fewer than `k` pivot coordinates. -/
def normalizedMarkedFamily (n k : ℕ) (ρ R D : ℝ) :
    Set (Body n × (Fin n → Space n)) :=
  ⋃ s : {s : Finset (Fin n) // s.card < k},
    normalizedBodies s.val ρ R ×ˢ closedBall 0 D

theorem mem_normalizedMarkedFamily_iff {n k : ℕ} {ρ R D : ℝ}
    {p : Body n × (Fin n → Space n)} :
    p ∈ normalizedMarkedFamily n k ρ R D ↔
      ∃ s : Finset (Fin n), s.card < k ∧
        coordinateDisk s ρ ⊆ (p.1 : Set (Space n)) ∧
        (p.1 : Set (Space n)) ⊆ closedBall 0 R ∧ ‖p.2‖ ≤ D := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
    exact ⟨s.val, s.property, hs.1.1, hs.1.2, mem_closedBall_zero_iff.mp hs.2⟩
  · rintro ⟨s, hs, hdisk, houter, hmarks⟩
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩,
      ⟨⟨hdisk, houter⟩, mem_closedBall_zero_iff.mpr hmarks⟩⟩

theorem isCompact_normalizedMarkedFamily (n k : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (R D : ℝ) : IsCompact (normalizedMarkedFamily n k ρ R D) := by
  apply isCompact_iUnion
  intro s
  exact (isCompact_normalizedBodies s.val hρ R).prod
    (isCompact_closedBall (0 : Fin n → Space n) D)

/-- The normalized image is compact because the marked mixed-volume map is
continuous on actual bodies and actual segment vectors. -/
theorem isCompact_normalizedMarkedImage (n k : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (R D : ℝ) :
    IsCompact ((fun p : Body n × (Fin n → Space n) => allMarkedArray (k := k) p.1 p.2) ''
      normalizedMarkedFamily n k ρ R D) :=
  (isCompact_normalizedMarkedFamily n k hρ R D).image continuous_allMarkedArray

/-- Every limit of uniformly normalized marked arrays has an actual marked
representation whose body has affine dimension at least `n - k + 1`.

The hypotheses specify concrete bounds and a literal contained coordinate disk;
they will be supplied by affine normalization and the maximal-minor theorem.
-/
theorem marked_limit_of_bounded_representations {n k : ℕ} (hkn : k ≤ n)
    {ρ R D : ℝ} (hρ : 0 < ρ)
    (p : ℕ → Deleted n k → ℝ) (P : Deleted n k → ℝ)
    (hp : Tendsto p atTop (𝓝 P))
    (hrep : ∀ m, ∃ (K : Body n) (U : Fin n → Space n) (s : Finset (Fin n)),
      s.card < k ∧ coordinateDisk s ρ ⊆ (K : Set (Space n)) ∧
      (K : Set (Space n)) ⊆ closedBall 0 R ∧ ‖U‖ ≤ D ∧ allMarkedArray K U = p m) :
    ∃ (K : Body n) (U : Fin n → Space n),
      n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  let S := (fun q : Body n × (Fin n → Space n) => allMarkedArray (k := k) q.1 q.2) ''
    normalizedMarkedFamily n k ρ R D
  have hS : IsClosed S := (isCompact_normalizedMarkedImage n k hρ.le R D).isClosed
  have hpS : ∀ m, p m ∈ S := by
    intro m
    obtain ⟨K, U, s, hs, hdisk, houter, hmarks, heq⟩ := hrep m
    exact ⟨(K, U), mem_normalizedMarkedFamily_iff.mpr ⟨s, hs, hdisk, houter, hmarks⟩, heq⟩
  obtain ⟨⟨K, U⟩, hKU, heq⟩ := hS.mem_of_tendsto hp (Eventually.of_forall hpS)
  obtain ⟨s, hs, hdisk, _houter, _hmarks⟩ := mem_normalizedMarkedFamily_iff.mp hKU
  refine ⟨K, U, ?_, heq⟩
  exact (by omega : n - k + 1 ≤ n - s.card).trans
    (coordinateDisk_dimension s hρ K hdisk)

end RankThreeProjection
end
end
end DevelopmentSource9

/- Source module: VolumePolynomials.ProjectionMonotonicity. SHA256: 416fbbb0e9de087ce0540b6c8dd251c4e0c72bd87ceab82d6c23c7f543d485fa -/
section DevelopmentSource10


/- Exact supplemental source closure; generated by generate_volume_supplements.py.
   The original theorem statements and proof bodies are unchanged. -/



set_option Elab.async false

/- BEGIN SOURCE: VolumePolynomials/MixedVolumeMonotonicity.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Monotonicity of genuine mixed volume for arbitrary convex bodies

The finite-polytope first-variation formula is extended first by a positive
finite-simplex thickening, then by finite-hull approximation and continuity.
All reference bodies and approximations are constructed in the actual space.
-/

noncomputable section
open Set Filter MeasureTheory Module
open scoped BigOperators Pointwise Topology

namespace VolumePolynomials

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finiteHull_with_zero_interior :
    ∃ P : ConvexBody E, IsFiniteHull (P : Set E) ∧ (0 : E) ∈ interior (P : Set E) := by
  first
  | classical
    let b := Module.finBasis ℝ E
    let V : Set E := insert 0 (Set.range b)
    have hV : V.Finite := (Set.finite_range b).insert 0
    have hVne : V.Nonempty := ⟨0, Set.mem_insert _ _⟩
    let Q := finiteHullBody V hV hVne
    have hspan : affineSpan ℝ (Q : Set E) = ⊤ := by
      first
      | change affineSpan ℝ (convexHull ℝ (insert 0 (Set.range b))) = ⊤
        rw [affineSpan_convexHull, affineSpan_insert_zero, b.span_eq]
        ext x <;> rfl
    obtain ⟨q, hq⟩ := Q.convex.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
    refine ⟨translateBody (-q) Q,
      isFiniteHull_translateBody (finiteHullBody_isFiniteHull V hV hVne) (-q), ?_⟩
    rw [coe_translateBody, interior_vadd]
    exact ⟨q, hq, neg_add_cancel q⟩

section Measure

variable [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem mixedVolume_mono_first_finite_background {n : ℕ}
    (K : Fin n → ConvexBody E) (hn : 0 < n)
    (hK : ∀ i, IsFiniteHull (K i : Set E))
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume μ (Fin.cons A K) ≤ mixedVolume μ (Fin.cons B K) := by
  first
  | classical
    letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) := inferInstanceAs (Measure.IsAddHaarMeasure μ)
    choose p hp using fun i => (K i).nonempty
    let L : Fin n → ConvexBody E := fun i => translateBody (-p i) (K i)
    have hL0 : ∀ i, (0 : E) ∈ L i := fun i => zero_mem_translateBody_neg (hp i)
    have hLpoly : ∀ i, IsFiniteHull (L i : Set E) :=
      fun i => isFiniteHull_translateBody (hK i) (-p i)
    obtain ⟨P, hPpoly, hPint⟩ := exists_finiteHull_with_zero_interior (E := E)
    have hP0 : (0 : E) ∈ P := interior_subset hPint
    let Q : ℝ → Fin n → ConvexBody E := fun r i => L i + r • P
    have hQ0 (r : ℝ) (i : Fin n) : (0 : E) ∈ Q r i :=
      ⟨0, hL0 i, 0, ⟨0, hP0, by simp⟩, zero_add 0⟩
    have hQpoly (r : ℝ) (i : Fin n) : IsFiniteHull (Q r i : Set E) :=
      (hLpoly i).add (hPpoly.smul r)
    have hQint {r : ℝ} (hr : 0 < r) :
        (0 : E) ∈ interior (∑ i, (Q r i : Set E)) := by
      first
      | have hsmall : (0 : E) ∈ interior (r • (P : Set E)) := by
          rw [interior_smul₀ hr.ne']
          exact ⟨0, hPint, by simp⟩
        have hsub : r • (P : Set E) ⊆ (↑(∑ i, Q r i) : Set E) := by
          intro x hx
          apply body_le_sum_of_zero_mem (Q r) (hQ0 r) (⟨0, hn⟩ : Fin n)
          exact ⟨0, hL0 _, x, hx, zero_add x⟩
        simpa only [coe_sum_body] using interior_mono hsub hsmall
    have hmono : ∀ᶠ r : ℝ in 𝓝[>] 0,
        mixedVolume μ (Fin.cons A (Q r)) ≤ mixedVolume μ (Fin.cons B (Q r)) := by
      first
      | filter_upwards [self_mem_nhdsWithin] with r hr
        exact mixedVolume_mono_first_of_finite_polytopes (Q r) (hQpoly r)
          (hQ0 r) (hQint hr) A B hAB
    have hcont (C : ConvexBody E) :
        Continuous (fun r : ℝ => mixedVolume μ (Fin.cons C (Q r))) := by
      first
      | apply (continuous_mixedVolume μ (n + 1)).comp
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero] using (continuous_const : Continuous (fun _ : ℝ => C))
        · simp only [Fin.cons_succ, Q]
          fun_prop
    have hlim (C : ConvexBody E) :
        Tendsto (fun r : ℝ => mixedVolume μ (Fin.cons C (Q r)))
          (𝓝[>] 0) (𝓝 (mixedVolume μ (Fin.cons C L))) := by
      first
      | simpa only [Q, body_zero_smul, add_zero] using
          ((hcont C).tendsto 0).mono_left nhdsWithin_le_nhds
    have hL := le_of_tendsto_of_tendsto (hlim A) (hlim B) hmono
    have htranslate (C : ConvexBody E) :
        mixedVolume μ (Fin.cons C L) = mixedVolume μ (Fin.cons C K) := by
      first
      | have h := mixedVolume_translate μ (Fin.cons C K) (Fin.cons (0 : E) (fun i => -p i))
        have he : (fun i : Fin (n + 1) =>
            (translateBody ((Fin.cons (0 : E) (fun j : Fin n => -p j) :
                Fin (n + 1) → E) i)
              ((Fin.cons C K : Fin (n + 1) → ConvexBody E) i) : ConvexBody E)) =
            (Fin.cons C L : Fin (n + 1) → ConvexBody E) := by
          funext i
          refine Fin.cases ?_ (fun j => rfl) i
          simp only [Fin.cons_zero, translateBody_zero]
        rwa [he] at h
    simpa only [htranslate] using hL

/-- Monotonicity in a genuine argument of dimension-matched mixed volume.
There is no full-dimensional, polytope, smoothness, or centering restriction
on any of the bodies. The background is nonempty, as in every dimension at
least two. -/
theorem mixedVolume_mono_first {n : ℕ}
    (K : Fin n → ConvexBody E) (hn : 0 < n) (_hdim : finrank ℝ E = n + 1)
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume μ (Fin.cons A K) ≤ mixedVolume μ (Fin.cons B K) := by
  first
  | let S : Set (Fin n → ConvexBody E) :=
      {L | mixedVolume μ (Fin.cons A L) ≤ mixedVolume μ (Fin.cons B L)}
    have hcont (C : ConvexBody E) :
        Continuous (fun L : Fin n → ConvexBody E => mixedVolume μ (Fin.cons C L)) := by
      first
      | apply (continuous_mixedVolume μ (n + 1)).comp
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact continuous_const
        · exact continuous_apply j
    have hclosed : IsClosed S := isClosed_le (hcont A) (hcont B)
    have hsub : {L : Fin n → ConvexBody E | ∀ i, IsFiniteHull (L i : Set E)} ⊆ S := by
      first
      | intro L hL
        exact mixedVolume_mono_first_finite_background μ L hn hL A B hAB
    exact closure_minimal hsub hclosed (dense_finiteHullBodyTuples (E := E) n K)

/-- The dimension-matched monotonicity theorem also includes the one-dimensional
case, where there are no background bodies and mixed volume is ordinary Haar
length. -/
theorem mixedVolume_mono_first_all {n : ℕ}
    (K : Fin n → ConvexBody E) (hdim : finrank ℝ E = n + 1)
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume μ (Fin.cons A K) ≤ mixedVolume μ (Fin.cons B K) := by
  first
  | cases n with
    | zero =>
        have hcons (C : ConvexBody E) : Fin.cons C K = fun _ : Fin 1 => C := by
          first
          | funext i
            exact Fin.cases rfl (fun j => Fin.elim0 j) i
        rw [hcons A, hcons B, mixedVolume_diagonal μ hdim A,
          mixedVolume_diagonal μ hdim B]
        exact measureReal_mono hAB B.isCompact.measure_ne_top
    | succ n =>
        exact mixedVolume_mono_first μ K (Nat.succ_pos n) hdim A B hAB

end Measure
end VolumePolynomials
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedVolumeMonotonicity.lean -/
end DevelopmentSource10

/- Source module: Projection.SegmentSeminorm. SHA256: ab98f4d2e1bef003e8d49846e350054e64ef317e2767d685181bbfc27247045f -/
section DevelopmentSource11





@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The actual segment mixed-volume seminorm

The seminorm used in Lemma 5.1 follows directly from Minkowski additivity,
monotonicity, and the inclusion `S_(u+v) ⊆ S_u + S_v`.  No Cauchy projection
formula is assumed.  The extrusion identity identifying the complementary
projection array with this seminorm remains a separate geometric theorem.
-/
namespace RankThreeProjection
open Set MeasureTheory Module VolumePolynomials
open scoped Pointwise BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smul_segmentBody (r : ℝ) (a b : E) :
    r • segmentBody a b = segmentBody (r • a) (r • b) := by
  apply ConvexBody.ext
  change (fun x : E => r • x) '' segment ℝ a b = segment ℝ (r • a) (r • b)
  exact image_segment ℝ (r • (LinearMap.id : E →ₗ[ℝ] E)).toAffineMap a b

theorem centeredSegment_smul (r : ℝ) (v : E) :
    centeredSegment (r • v) = r • centeredSegment v := by
  unfold centeredSegment
  rw [smul_segmentBody]
  congr 1 <;> simp only [smul_smul, mul_comm]

theorem centeredSegment_neg (v : E) :
    centeredSegment (-v) = centeredSegment v := by
  apply ConvexBody.ext
  change segment ℝ (-(1 / 2 : ℝ) • (-v)) ((1 / 2 : ℝ) • (-v)) =
    segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)
  simpa only [smul_neg, neg_smul, neg_neg] using
    segment_symm ℝ ((1 / 2 : ℝ) • v) (-((1 / 2 : ℝ) • v))

theorem centeredSegment_abs_smul (r : ℝ) (v : E) :
    centeredSegment (r • v) = |r| • centeredSegment v := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, centeredSegment_smul]
  · rw [abs_of_nonpos hr, ← centeredSegment_smul]
    simp only [neg_smul, centeredSegment_neg]

theorem centeredSegment_add_le (u v : E) :
    centeredSegment (u + v) ≤ centeredSegment u + centeredSegment v := by
  change segment ℝ (-(1 / 2 : ℝ) • (u + v)) ((1 / 2 : ℝ) • (u + v)) ⊆
    ((centeredSegment u + centeredSegment v : ConvexBody E) : Set E)
  apply (centeredSegment u + centeredSegment v).convex.segment_subset
  · rw [smul_add]
    exact Set.add_mem_add
      (left_mem_segment ℝ (-(1 / 2 : ℝ) • u) ((1 / 2 : ℝ) • u))
      (left_mem_segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v))
  · rw [smul_add]
    exact Set.add_mem_add
      (right_mem_segment ℝ (-(1 / 2 : ℝ) • u) ((1 / 2 : ℝ) • u))
      (right_mem_segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v))

section MixedVolume
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- `dim(E) * V(S_v, K₁, …, K_(dim(E)-1))` as a genuine Mathlib seminorm.
The background bodies are arbitrary compact convex bodies. -/
def segmentMixedVolumeSeminorm {n : ℕ} (K : Fin n → ConvexBody E)
    (hdim : finrank ℝ E = n + 1) : Seminorm ℝ E := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  refine Seminorm.of
    (fun v => (n + 1 : ℝ) * mixedVolume μ (Fin.cons (centeredSegment v) K)) ?_ ?_
  · intro u v
    have h := mixedVolume_mono_first_all μ K hdim _ _ (centeredSegment_add_le u v)
    have hadd : mixedVolume μ (Fin.cons (centeredSegment u + centeredSegment v) K) =
        mixedVolume μ (Fin.cons (centeredSegment u) K) +
          mixedVolume μ (Fin.cons (centeredSegment v) K) := by
      simpa only [Fin.update_cons_zero] using
        mixedVolume_add μ (Fin.cons (centeredSegment u) K) 0
          (centeredSegment u) (centeredSegment v)
    rw [hadd] at h
    simpa only [mul_add] using
      mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (n + 1 : ℝ))
  · intro r v
    rw [centeredSegment_abs_smul]
    have hsmul : mixedVolume μ (Fin.cons (|r| • centeredSegment v) K) =
        |r| * mixedVolume μ (Fin.cons (centeredSegment v) K) := by
      simpa only [Fin.update_cons_zero] using
        mixedVolume_smul μ (Fin.cons (centeredSegment v) K) 0
          (centeredSegment v) (abs_nonneg r)
    rw [hsmul, Real.norm_eq_abs]
    ring

@[simp] theorem segmentMixedVolumeSeminorm_apply {n : ℕ}
    (K : Fin n → ConvexBody E) (hdim : finrank ℝ E = n + 1) (v : E) :
    segmentMixedVolumeSeminorm μ K hdim v =
      (n + 1 : ℝ) * mixedVolume μ (Fin.cons (centeredSegment v) K) := rfl

end MixedVolume

/-- The vector identity behind the hyperplane weighted triangle inequalities.
It holds for every seminorm and all labels, with no nonzero-weight assumption. -/
theorem seminorm_weighted_triangle {ι : Type*}
    (N : Seminorm ℝ E) (α : ι → ℝ) (b : ι → E) (i j k : ι) :
    N (α i • b j - α j • b i) * |α k| ≤
      N (α i • b k - α k • b i) * |α j| +
        N (α j • b k - α k • b j) * |α i| := by
  have he : α k • (α i • b j - α j • b i) =
      α j • (α i • b k - α k • b i) -
        α i • (α j • b k - α k • b j) := by module
  have h := map_sub_le_add N
    (α j • (α i • b k - α k • b i))
    (α i • (α j • b k - α k • b j))
  rw [← he, map_smul_eq_mul, map_smul_eq_mul, map_smul_eq_mul] at h
  simpa only [Real.norm_eq_abs, mul_comm] using h

end RankThreeProjection
end
end
end DevelopmentSource11

/- Source module: VolumePolynomials.ProjectionMixedVolumeTransport. SHA256: f6bfbfdb8a255721ef2da1cbf89d14eea2e1f5995c047f7873cfb729dcff1f97 -/
section DevelopmentSource12


/- Exact supplemental source closure; generated by generate_volume_supplements.py.
   The original theorem statements and proof bodies are unchanged. -/


set_option Elab.async false

/- BEGIN SOURCE: VolumePolynomials/MixedVolumeTransport.lean -/
section


@[expose] public section

set_option autoImplicit false

/-! # Exact transport of actual mixed volume through measure-preserving frames -/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators NNReal

namespace VolumePolynomials

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  (ν : Measure F) [Measure.IsAddHaarMeasure ν]

theorem measureReal_image_measurePreserving (T : E ≃L[ℝ] F)
    (hT : MeasurePreserving T μ ν) (S : Set E) : ν.real (T '' S) = μ.real S := by
  first
  | have h := hT.measure_preimage_emb T.toHomeomorph.measurableEmbedding (T '' S)
    rw [Set.preimage_image_eq S T.injective] at h
    exact congrArg ENNReal.toReal h.symm

theorem volumePolynomial_map_measurePreserving {n : ℕ}
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T μ ν) (K : Fin n → ConvexBody E) :
    volumePolynomial ν (fun i => mapBody T.toContinuousLinearMap (K i)) = volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • mapBody T.toContinuousLinearMap (K i)) =
        mapBody T.toContinuousLinearMap (∑ i, t i • K i) := by
      first
      | calc
          _ = ∑ i, mapBody T.toContinuousLinearMap (t i • K i) := by
            first
            | exact Finset.sum_congr rfl (fun i _ => (mapBody_smul T.toContinuousLinearMap (t i) (K i)).symm)
          _ = _ := (map_sum (mapBodyHom T.toContinuousLinearMap) (fun i => t i • K i) Finset.univ).symm
    rw [hsum]
    exact (measureReal_image_measurePreserving μ ν T hT _).symm

theorem mixedVolume_map_measurePreserving {n : ℕ}
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T μ ν) (K : Fin n → ConvexBody E) :
    mixedVolume ν (fun i => mapBody T.toContinuousLinearMap (K i)) = mixedVolume μ K := by
  first
  | simp only [mixedVolume, volumePolynomial_map_measurePreserving μ ν T hT K]

/-- The actual Haar conversion factor; it is positive and is not supplied as
an unverified Jacobian hypothesis. -/
def mixedVolumeFrameFactor (T : E ≃L[ℝ] F) : ℝ≥0 :=
  Measure.addHaarScalarFactor (μ.map T) ν

theorem mixedVolumeFrameFactor_pos (T : E ≃L[ℝ] F) :
    0 < mixedVolumeFrameFactor μ ν T :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem measureReal_eq_frameFactor_mul_image (T : E ≃L[ℝ] F) (S : Set E) :
    μ.real S = (mixedVolumeFrameFactor μ ν T : ℝ) * ν.real (T '' S) := by
  first
  | have hm : (μ.map T) (T '' S) = μ S := by
      first
      | change (μ.map T.toHomeomorph) (T.toHomeomorph '' S) = μ S
        rw [T.toHomeomorph.measurableEmbedding.map_apply,
          Set.preimage_image_eq S T.toHomeomorph.injective]
    have hs : μ.map T = mixedVolumeFrameFactor μ ν T • ν :=
      Measure.isAddLeftInvariant_eq_smul _ _
    have he := congrArg ENNReal.toReal hm.symm
    rw [hs, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul] at he
    simpa only [ENNReal.coe_toReal, measureReal_def] using he

theorem volumePolynomial_eq_frameFactor_mul {n : ℕ}
    (T : E ≃L[ℝ] F) (K : Fin n → ConvexBody E) :
    volumePolynomial μ K = MvPolynomial.C (mixedVolumeFrameFactor μ ν T : ℝ) *
      volumePolynomial ν (fun i => mapBody T.toContinuousLinearMap (K i)) := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [map_mul, MvPolynomial.eval_C, volumePolynomial_eval ν _ t ht]
    have hsum : (∑ i, t i • mapBody T.toContinuousLinearMap (K i)) =
        mapBody T.toContinuousLinearMap (∑ i, t i • K i) := by
      first
      | calc
          _ = ∑ i, mapBody T.toContinuousLinearMap (t i • K i) := by
            first
            | exact Finset.sum_congr rfl (fun i _ => (mapBody_smul T.toContinuousLinearMap (t i) (K i)).symm)
          _ = _ := (map_sum (mapBodyHom T.toContinuousLinearMap) (fun i => t i • K i) Finset.univ).symm
    rw [hsum]
    exact (measureReal_eq_frameFactor_mul_image μ ν T _).symm

theorem mixedVolume_eq_frameFactor_mul {n : ℕ}
    (T : E ≃L[ℝ] F) (K : Fin n → ConvexBody E) :
    mixedVolume μ K = (mixedVolumeFrameFactor μ ν T : ℝ) *
      mixedVolume ν (fun i => mapBody T.toContinuousLinearMap (K i)) := by
  first
  | rw [mixedVolume, volumePolynomial_eq_frameFactor_mul μ ν T K, MvPolynomial.coeff_C_mul,
      mixedVolume]
    ring

theorem volumePolynomial_map_linear {n : ℕ} (L : E →L[ℝ] E) (K : Fin n → ConvexBody E) :
    volumePolynomial μ (fun i => mapBody L (K i)) =
      MvPolynomial.C |LinearMap.det L.toLinearMap| * volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [map_mul, MvPolynomial.eval_C, volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • mapBody L (K i)) = mapBody L (∑ i, t i • K i) := by
      first
      | calc
          _ = ∑ i, mapBody L (t i • K i) := by
            first
            | exact Finset.sum_congr rfl (fun i _ => (mapBody_smul L (t i) (K i)).symm)
          _ = _ := (map_sum (mapBodyHom L) (fun i => t i • K i) Finset.univ).symm
    rw [hsum]
    have h := congrArg ENNReal.toReal (Measure.addHaar_image_linearMap μ L.toLinearMap
      ((∑ i, t i • K i : ConvexBody E) : Set E))
    simpa only [coe_mapBody, ContinuousLinearMap.coe_coe, measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)] using h.symm

/-- Full determinant transport, including singular linear maps. -/
theorem mixedVolume_map_linear {n : ℕ} (L : E →L[ℝ] E) (K : Fin n → ConvexBody E) :
    mixedVolume μ (fun i => mapBody L (K i)) =
      |LinearMap.det L.toLinearMap| * mixedVolume μ K := by
  first
  | rw [mixedVolume, volumePolynomial_map_linear μ L K, MvPolynomial.coeff_C_mul, mixedVolume]
    ring

end VolumePolynomials
end -- closes the original EOF section from source line 14
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedVolumeTransport.lean -/
end DevelopmentSource12

/- Source module: Projection.SegmentDeterminant. SHA256: 0a5ee345d74b889b67d50527ce00c9b62991e4648de1c6a8a17f85b03e848864 -/
section DevelopmentSource13






@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module MvPolynomial
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

variable {n : ℕ}

/-- The matrix has the marked vectors as its columns. -/
def columnsMatrix (U : Fin n → Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => U j i

def columnsLinear (U : Fin n → Space n) : Space n →L[ℝ] Space n :=
  (Matrix.toLin' (columnsMatrix U)).toContinuousLinearMap

@[simp] theorem columnsLinear_basis (U : Fin n → Space n) (i : Fin n) :
    columnsLinear U (Pi.single i 1) = U i := by
  ext j
  simp only [columnsLinear, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply, columnsMatrix]

@[simp] theorem columnsLinear_det (U : Fin n → Space n) :
    LinearMap.det (columnsLinear U).toLinearMap = (columnsMatrix U).det :=
  LinearMap.det_toLin' _

theorem smul_originSegment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (v : E) : r • originSegment v = originSegment (r • v) := by
  simp only [originSegment, smul_segmentBody, smul_zero]

theorem squarefree_support (n : ℕ) : (squarefreeExponent n).support = Finset.univ := by
  ext i
  simp [Finsupp.mem_support_iff, squarefreeExponent_apply]

/-- The polynomial of the standard coordinate segments is the squarefree
monomial, proved from the volume of the actual coordinate box. -/
theorem volumePolynomial_basis_segments (n : ℕ) :
    volumePolynomial volume (fun i : Fin n => originSegment (Pi.single i (1 : ℝ))) =
      MvPolynomial.monomial (squarefreeExponent n) 1 := by
  apply volumePolynomial_eq_of_eval
  intro t ht
  have hsum : ((∑ i : Fin n, t i • originSegment (Pi.single i (1 : ℝ)) :
      Body n) : Set (Space n)) = parallelepiped (fun i => Pi.single i (t i)) := by
    rw [coe_sum_body, parallelepiped_eq_sum_segment]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_originSegment]
    change segment ℝ 0 (t i • Pi.single i (1 : ℝ)) = segment ℝ 0 (Pi.single i (t i))
    congr 1
    ext j
    by_cases hij : i = j <;> simp [hij]
  rw [hsum, parallelepiped_single, uIcc_of_le (show (0 : Fin n → ℝ) ≤ t from ht)]
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod,
    squarefree_support, squarefreeExponent_apply, pow_one]
  simpa only [measureReal_def, Pi.zero_def, Pi.zero_apply, sub_zero] using
    (Real.volume_Icc_pi_toReal (a := (0 : Fin n → ℝ)) (b := t) ht).symm

theorem mixedVolume_basis_segments (n : ℕ) :
    mixedVolume volume (fun i : Fin n => originSegment (Pi.single i (1 : ℝ))) =
      1 / (n.factorial : ℝ) := by
  simp only [mixedVolume, volumePolynomial_basis_segments,
    MvPolynomial.coeff_monomial, if_pos rfl, ite_true]

theorem mixedVolume_origin_segments (U : Fin n → Space n) :
    mixedVolume volume (fun i => originSegment (U i)) =
      |(columnsMatrix U).det| / (n.factorial : ℝ) := by
  have hm (i : Fin n) : mapBody (columnsLinear U) (originSegment (Pi.single i 1)) =
      originSegment (U i) := by
    simp only [originSegment, map_segmentBody, map_zero, columnsLinear_basis]
  have h := mixedVolume_map_linear volume (columnsLinear U)
    (fun i : Fin n => originSegment (Pi.single i 1))
  simpa only [hm, columnsLinear_det, mixedVolume_basis_segments, mul_one_div] using h

/-- The full determinant identity includes dependent and zero directions. -/
theorem mixedVolume_centered_segments (U : Fin n → Space n) :
    (n.factorial : ℝ) * mixedVolume volume (fun i => centeredSegment (U i)) =
      |(columnsMatrix U).det| := by
  have h := mixedVolume_translate volume (fun i => originSegment (U i))
    (fun i => -(1 / 2 : ℝ) • U i)
  simp only [← centered_eq_translate_origin] at h
  rw [h, mixedVolume_origin_segments]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

end RankThreeProjection
end
end
end DevelopmentSource13

/- Source module: TauCeti.LinearAlgebra.AffineSpace.Basis. SHA256: f70ae2ef3d56232398b90c7baf5c90ea822d9a06ef71972adf3848487db11608 -/
section DevelopmentSource14
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/




/-!
# Affine equivalences between affine bases

Two affine bases indexed by the same type are related by an affine equivalence: there is an affine
equivalence sending the points of one basis to the corresponding points of the other
(`AffineBasis.exists_affineEquiv_apply_eq`), and every affine map that does so preserves
barycentric coordinates (`AffineBasis.coord_apply_of_forall_apply_eq`). This is how a statement
about barycentric coordinates relative to an arbitrary affine basis is reduced to one about a
fixed reference basis.

The file also computes the barycentric coordinates of a point after a homothety about the centroid
of an affine basis (`AffineBasis.coord_homothety_centroid`), which describes the homothetic images
of the simplex spanned by the basis.

## Main statements

* `AffineBasis.coord_apply_of_forall_apply_eq`: an affine map sending the affine basis `b` to the
  affine basis `b₂` carries barycentric coordinates relative to `b` to those relative to `b₂`;
* `AffineBasis.exists_affineEquiv_apply_eq`: there is an affine equivalence sending `b` to `b₂`;
* `AffineBasis.coord_homothety_centroid`: the barycentric coordinates of the image of a point under
  a homothety about the centroid of an affine basis.
-/

public section

namespace AffineBasis

variable {ι k V P V₂ P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] (b : AffineBasis ι k P)
  (b₂ : AffineBasis ι k P₂)

/-- An affine map sending each point `b i` of an affine basis to the point `b₂ i` of another affine
basis preserves barycentric coordinates. -/
theorem coord_apply_of_forall_apply_eq {f : P →ᵃ[k] P₂} (hf : ∀ i, f (b i) = b₂ i) (i : ι)
    (x : P) : b₂.coord i (f x) = b.coord i x := by
  have h : (b₂.coord i).comp f = b.coord i := by
    refine AffineMap.ext_on b.tot ?_
    rintro - ⟨j, rfl⟩
    rcases eq_or_ne i j with rfl | hij
    · simp [hf, coord_apply_eq]
    · simp [hf, coord_apply_ne _ hij]
  exact congr($h x)

/-- Two affine bases indexed by the same type are related by an affine equivalence sending each
point of the first basis to the corresponding point of the second. -/
theorem exists_affineEquiv_apply_eq : ∃ T : P ≃ᵃ[k] P₂, ∀ i, T (b i) = b₂ i := by
  obtain ⟨i₀⟩ := b.nonempty
  -- Translate `b i₀` to the origin, map the linear basis `b.basisOf i₀` to `b₂.basisOf i₀`, and
  -- translate the origin to `b₂ i₀`.
  let L : V ≃ₗ[k] V₂ := (b.basisOf i₀).equiv (b₂.basisOf i₀) (Equiv.refl _)
  refine ⟨((AffineEquiv.vaddConst k (b i₀)).symm.trans L.toAffineEquiv).trans
    (AffineEquiv.vaddConst k (b₂ i₀)), fun i => ?_⟩
  rcases eq_or_ne i i₀ with rfl | hi
  · simp
  · have hL : L (b i -ᵥ b i₀) = b₂ i -ᵥ b₂ i₀ := by
      rw [← b.basisOf_apply i₀ ⟨i, hi⟩, Module.Basis.equiv_apply, Equiv.refl_apply,
        basisOf_apply]
    simp [hL]

end AffineBasis

namespace AffineBasis

variable {ι k V P : Type*} [Fintype ι] [Field k] [CharZero k] [AddCommGroup V] [Module k V]
  [AddTorsor V P] (b : AffineBasis ι k P)

/-- The barycentric coordinates relative to an affine basis `b` of the image of a point `z` under
the homothety of ratio `t` about the centroid of `b`: the homothety moves each coordinate
`b.coord i z` towards the centroid's coordinate `1 / card ι` by the factor `t`. -/
theorem coord_homothety_centroid (t : k) (z : P) (i : ι) :
    b.coord i (AffineMap.homothety (Finset.univ.centroid k b) t z) =
      (1 - t) / Fintype.card ι + t * b.coord i z := by
  rw [AffineMap.homothety_eq_lineMap, AffineMap.apply_lineMap,
    b.coord_apply_centroid (Finset.mem_univ i), Finset.card_univ, AffineMap.lineMap_apply_ring']
  ring

end AffineBasis
end
end DevelopmentSource14

/- Source module: TauCeti.LinearAlgebra.AffineSpace.Matrix. SHA256: 46025d09711a4d089cc300c468f3e4f8f1bdaaa46b2dc5458762a43aa6dd9dd2 -/
section DevelopmentSource15
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/




/-!
# Determinants of matrices of barycentric coordinates

Fix an affine basis `b` of an affine space `P`. For a family `q` of points of `P`, the matrix
`b.toMatrix q` has the barycentric coordinates of `q i` with respect to `b` as its rows, and when
`q` is indexed like `b` its determinant is the signed (oriented) volume of the simplex with vertices
`q i`, measured relative to the simplex of `b`; the unsigned relative volume is its absolute value.

Replacing the vertex `q i` of an affine basis `q` by a point `x` scales this determinant by the
barycentric coordinate of `x` at `i` with respect to `q`
(`AffineBasis.det_toMatrix_update`). This is Cramer's rule for barycentric coordinates
(`AffineBasis.det_smul_coords_eq_cramer_coords`) read as a statement about volumes, and it is the
reason a simplex of maximal volume inside a set controls the barycentric coordinates of all points
of the set.

## Main statements

* `AffineBasis.toMatrix_update`: replacing a point of the family replaces the corresponding row by
  its barycentric coordinates;
* `AffineBasis.det_toMatrix_update`: replacing the vertex `q i` of an affine basis `q` by `x`
  multiplies the determinant by `q.coord i x`.
-/

public section

open Matrix

namespace AffineBasis

variable {ι ι' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

/-- Replacing the point `q i` of a family by `x` replaces the `i`-th row of the matrix of
barycentric coordinates by the coordinates of `x`. -/
@[simp]
theorem toMatrix_update [DecidableEq ι'] (q : ι' → P) (i : ι') (x : P) :
    b.toMatrix (Function.update q i x) = (b.toMatrix q).updateRow i (b.coords x) := by
  ext j l
  rcases eq_or_ne j i with rfl | hj
  · simp [toMatrix_apply]
  · simp [toMatrix_apply, hj]

end Ring

section CommRing

variable [CommRing k] [Module k V] [Fintype ι] [DecidableEq ι] (b b₂ : AffineBasis ι k P)

/-- Replacing the vertex `b₂ i` of the affine basis `b₂` by a point `x` multiplies the determinant
of the matrix of barycentric coordinates relative to `b` by the barycentric coordinate of `x` at
`i` with respect to `b₂`. -/
theorem det_toMatrix_update (i : ι) (x : P) :
    (b.toMatrix (Function.update b₂ i x)).det = (b.toMatrix b₂).det * b₂.coord i x := by
  have h := congr_fun (b.det_smul_coords_eq_cramer_coords b₂ x) i
  rw [Pi.smul_apply, coords_apply, smul_eq_mul, cramer_apply, updateCol_transpose,
    det_transpose] at h
  rw [toMatrix_update, h]

end CommRing

end AffineBasis
end
end DevelopmentSource15

/- Source module: TauCeti.Analysis.Convex.AffineNormalization. SHA256: d3ed2e1924b35a51677a32c947975efa69f4863a518b30955d3f31c841e532fb -/
section DevelopmentSource16
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/









/-!
# Affine normalization of convex bodies

A convex body in an `n`-dimensional real affine space can be moved by an affine equivalence to a
position between two balls whose radii depend only on the space. This is the normalization that
lets estimates for convex sets be proved for sets of unit size and transferred back; in the
regularity theory of the Monge–Ampère equation it is applied to the sections
`{y | u y < u x + ⟪p, y - x⟫ + h}` of a convex function `u`.

The normalization comes from a simplex of maximal volume. Let `K` be a compact set whose affine
span is the whole `n`-dimensional space, and choose `n + 1` points of `K` spanning a simplex of
maximal volume, where volume is measured by the absolute value of the determinant of the matrix of
barycentric coordinates relative to a fixed affine basis (the determinant itself is the signed
volume). Replacing the vertex `b i` by a point `x` multiplies this determinant by the barycentric
coordinate `b.coord i x` (`AffineBasis.det_toMatrix_update`), so maximality of its absolute value
forces `|b.coord i x| ≤ 1` for every `x ∈ K`
(`IsCompact.exists_affineBasis_abs_coord_le_one`).

In terms of the simplex `Δ = convexHull (range b)` with centroid `c`, the points whose barycentric
coordinates are all at most `1` form the image of `Δ` under the homothety of ratio `-n` about `c`
(`AffineBasis.mem_image_homothety_convexHull_iff`). Thus every compact spanning `K` contains the
vertices of a simplex `Δ` and lies inside its homothetic image of ratio `-n`
(`IsCompact.exists_affineBasis_subset_image_homothety_convexHull`); when `K` is convex it contains
`Δ` itself. Mapping `Δ` to a fixed reference simplex by an affine equivalence then gives the
normalization by balls (`TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`).

John's theorem gives the sharper statement in which the simplex is replaced by the ellipsoid of
maximal volume and the ratio `-n` by `n`, or by `√n` for centrally symmetric bodies. For the
normalization, a ratio depending only on the dimension suffices.

## Main statements

* `IsCompact.exists_affineBasis_abs_coord_le_one`: a compact set spanning a finite-dimensional real
  affine space contains an affine basis relative to which all its points have barycentric
  coordinates in `[-1, 1]`;
* `AffineBasis.mem_image_homothety_convexHull_iff`: the image of the simplex of an affine basis
  under the homothety of ratio `-n` about its centroid is the set of points whose barycentric
  coordinates are at most `1`;
* `IsCompact.exists_affineBasis_subset_image_homothety_convexHull`: a compact spanning set contains
  the vertices of a simplex and lies in the image of that simplex under the homothety of ratio `-n`
  about its centroid;
* `TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`: in a finite-dimensional real normed
  space there is `r > 0` such that every bounded convex set with nonempty interior is mapped by
  some affine equivalence to a set between the balls of radii `r` and `1` about `0`.

## References

* F. John, *Extremum problems with inequalities as subsidiary conditions*, Studies and Essays
  Presented to R. Courant on his 60th Birthday, Interscience, 1948, 187–204.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.8 (normalized convex sets).
* K. Ball, *An elementary introduction to modern convex geometry*, in *Flavors of Geometry*,
  MSRI Publications 31, Cambridge University Press, 1997, Lecture 3.
-/

public section

open Set Module Metric

/-! ### A simplex of maximal volume -/

section Compact

variable {ι V P : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [PseudoMetricSpace P] [NormedAddTorsor V P]

/-- **Affine bases with bounded barycentric coordinates.** A compact set `K` whose affine span is
the whole finite-dimensional real affine space contains an affine basis `b`, indexed by any type
with `finrank + 1` elements, such that every point of `K` has all its barycentric coordinates
relative to `b` in `[-1, 1]`. -/
theorem IsCompact.exists_affineBasis_abs_coord_le_one {K : Set P} (hK : IsCompact K)
    (hspan : affineSpan ℝ K = ⊤) (hι : Fintype.card ι = finrank ℝ V + 1) :
    ∃ b : AffineBasis ι ℝ P, (∀ i, b i ∈ K) ∧ ∀ x ∈ K, ∀ i, |b.coord i x| ≤ 1 := by
  classical
  -- A reference affine basis with vertices in `K`.
  obtain ⟨s, hsK, b₀, hb₀⟩ := AffineBasis.exists_affine_subbasis hspan
  lift s to Finset P using b₀.setFinite
  let b₁ : AffineBasis ι ℝ P :=
    b₀.reindex (Fintype.equivOfCardEq (by rw [hι, ← b₀.card_eq_finrank_add_one]))
  have hb₁ : ∀ i, b₁ i ∈ K := fun i => by
    simp only [b₁, AffineBasis.reindex_apply, hb₀]
    exact hsK (Subtype.prop _)
  -- Choose vertices in `K` maximizing the volume `|det|` relative to `b₁`.
  let f : (ι → P) → ℝ := fun q => |(b₁.toMatrix q).det|
  -- Continuity goes through the linear part: Mathlib's `continuous_barycentric_coord` assumes
  -- `MetricSpace P`, which this pseudometric setting does not provide.
  have hcoord : ∀ j, Continuous (b₁.coord j) := fun j =>
    AffineMap.continuous_linear_iff.1 (b₁.coord j).linear.continuous_of_finiteDimensional
  have hf : Continuous f :=
    ((continuous_matrix fun i j => (hcoord j).comp (continuous_apply i)).matrix_det).abs
  obtain ⟨q, hqK, hq⟩ := (isCompact_univ_pi fun _ => hK).exists_isMaxOn
    ⟨b₁, fun i _ => hb₁ i⟩ hf.continuousOn
  have hfq : 0 < f q := by
    have hb₁K : (b₁ : ι → P) ∈ univ.pi fun _ => K := fun i _ => hb₁ i
    have := hq hb₁K
    simp only [mem_ofPred_eq, b₁.toMatrix_self, Matrix.det_one, abs_one, f] at this
    linarith
  -- A family of points of nonzero volume is an affine basis.
  obtain ⟨hind, htot⟩ := (b₁.isUnit_toMatrix_iff q).1 <|
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (abs_pos.1 hfq))
  let b : AffineBasis ι ℝ P := ⟨q, hind, htot⟩
  have hbq : (b : ι → P) = q := rfl
  have hbK : ∀ j, b j ∈ K := fun j => hbq ▸ hqK j (mem_univ j)
  refine ⟨b, hbK, fun x hx i => ?_⟩
  -- Replacing the vertex `b i` by `x` multiplies the volume by `|b.coord i x|`.
  have hle : f (Function.update b i x) ≤ f b := by
    rw [hbq]
    refine hq fun j _ => ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hx
    · simpa [hj, hbq] using hbK j
  have hupdate : f (Function.update b i x) = f b * |b.coord i x| := by
    simp only [f, b₁.det_toMatrix_update b, abs_mul]
  rw [hupdate] at hle
  exact (mul_le_iff_le_one_right (hbq ▸ hfq)).1 hle

end Compact

/-! ### The homothetic image of a simplex -/

section Homothety

variable {ι k E : Type*} [Fintype ι] [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [Module k E] (b : AffineBasis ι k E)

/-- The image of the simplex spanned by an affine basis of an `n`-dimensional space under the
homothety of ratio `-n` about its centroid is the set of points whose barycentric coordinates are
all at most `1`. -/
theorem AffineBasis.mem_image_homothety_convexHull_iff {x : E} :
    x ∈ AffineMap.homothety (Finset.univ.centroid k b) (-(finrank k E : k)) ''
        convexHull k (range b) ↔ ∀ i, b.coord i x ≤ 1 := by
  have hn : (0 : k) ≤ finrank k E := Nat.cast_nonneg _
  have hn1 : (finrank k E : k) + 1 ≠ 0 := by positivity
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    rw [b.convexHull_eq_nonneg_coord] at hz
    rw [b.coord_homothety_centroid, b.card_eq_finrank_add_one, Nat.cast_add_one,
      div_eq_one_iff_eq hn1 |>.2 (by ring)]
    nlinarith [hz i]
  · intro hx
    rcases hn.eq_or_lt with h0 | hpos
    · -- In dimension zero the homothety is constant and the space is a point.
      have : Subsingleton E := by
        have := b.finiteDimensional
        exact finrank_zero_iff.1 (by exact_mod_cast h0.symm)
      obtain ⟨i⟩ := b.nonempty
      exact ⟨b i, subset_convexHull k _ (mem_range_self i), Subsingleton.elim _ _⟩
    · refine ⟨AffineMap.homothety (Finset.univ.centroid k b) (-(finrank k E : k)⁻¹) x, ?_, ?_⟩
      · rw [b.convexHull_eq_nonneg_coord]
        intro i
        rw [b.coord_homothety_centroid, b.card_eq_finrank_add_one, Nat.cast_add_one]
        have := hx i
        field_simp
        nlinarith
      · rw [← AffineMap.homothety_mul_apply, neg_mul_neg, mul_inv_cancel₀ hpos.ne',
          AffineMap.homothety_one, AffineMap.id_apply]

end Homothety

section CompactHomothety

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Affine normalization of compact sets.** A compact set `K` whose affine span is the whole
`n`-dimensional real normed space contains the vertices of a simplex `Δ` and lies in the image of
`Δ` under the homothety of ratio `-n` about the centroid of `Δ`. When `K` is convex, it also
contains `Δ`, by `convexHull_min`. -/
theorem IsCompact.exists_affineBasis_subset_image_homothety_convexHull {K : Set E}
    (hK : IsCompact K) (hspan : affineSpan ℝ K = ⊤) (hι : Fintype.card ι = finrank ℝ E + 1) :
    ∃ b : AffineBasis ι ℝ E, (∀ i, b i ∈ K) ∧
      K ⊆ AffineMap.homothety (Finset.univ.centroid ℝ b) (-(finrank ℝ E : ℝ)) ''
        convexHull ℝ (range b) := by
  obtain ⟨b, hbK, hb⟩ := hK.exists_affineBasis_abs_coord_le_one hspan hι
  exact ⟨b, hbK, fun x hx => b.mem_image_homothety_convexHull_iff.2 fun i =>
    (le_abs_self _).trans (hb x hx i)⟩

end CompactHomothety

/-! ### Normalization by balls -/

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- **Normalization of convex bodies.** In a finite-dimensional real normed space `E` there is a
radius `r > 0`, depending only on `E`, such that every bounded convex set `s` with nonempty
interior is mapped by some affine equivalence `T` to a set between the balls of radii `r` and `1`
about `0`. -/
theorem exists_affineEquiv_ball_subset_image_subset_ball :
    ∃ r > 0, ∀ s : Set E, Convex ℝ s → Bornology.IsBounded s → (interior s).Nonempty →
      ∃ T : E ≃ᵃ[ℝ] E, ball 0 r ⊆ T '' s ∧ T '' s ⊆ ball 0 1 := by
  -- A reference simplex: its interior contains a ball about its centroid `c`, and the points with
  -- barycentric coordinates in `[-1, 1]` lie in the ball of radius `∑ i, ‖b₁ i‖` about `0`.
  let ι := Fin (finrank ℝ E + 1)
  have hι : Fintype.card ι = finrank ℝ E + 1 := Fintype.card_fin _
  obtain ⟨b₁⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional (k := ℝ) (P := E) hι
  set c := Finset.univ.centroid ℝ b₁
  have hc : c ∈ interior (convexHull ℝ (range b₁)) := b₁.centroid_mem_interior_convexHull
  rw [b₁.interior_convexHull] at hc
  have hopen : IsOpen {y | ∀ i, 0 < b₁.coord i y} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (continuous_barycentric_coord b₁ i)
  obtain ⟨ρ, hρ, hball⟩ := isOpen_iff.1 hopen c hc
  have hbound : ∀ y, (∀ i, |b₁.coord i y| ≤ 1) → ‖y‖ ≤ ∑ i, ‖b₁ i‖ := fun y hy => by
    conv_lhs => rw [← b₁.linear_combination_coord_eq_self y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hy i)
  set R := ∑ i, ‖b₁ i‖ + ‖c‖ + 1
  have hR : 0 < R := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => norm_nonneg (b₁ i)
    have := norm_nonneg c
    linarith
  refine ⟨ρ / R, div_pos hρ hR, fun s hs hsb hsi => ?_⟩
  -- An affine basis in the closure of `s` relative to which the barycentric coordinates of the
  -- points of the closure lie in `[-1, 1]`.
  have hspan : affineSpan ℝ (closure s) = ⊤ :=
    top_unique <| (isOpen_interior.affineSpan_eq_top hsi).symm.le.trans
      (affineSpan_mono ℝ (interior_subset.trans subset_closure))
  obtain ⟨b, hbs, hb⟩ := hsb.isCompact_closure.exists_affineBasis_abs_coord_le_one hspan hι
  -- Move it onto the reference simplex, then recentre at `0` and rescale by `R⁻¹`.
  obtain ⟨T₀, hT₀⟩ := b.exists_affineEquiv_apply_eq b₁
  have hcoord : ∀ x i, b₁.coord i (T₀ x) = b.coord i x := fun x i =>
    b.coord_apply_of_forall_apply_eq b₁ (f := T₀.toAffineMap) hT₀ i x
  let T : E ≃ᵃ[ℝ] E := (T₀.trans (AffineEquiv.constVAdd ℝ E (-c))).trans
    (AffineEquiv.homothetyUnitsMulHom (0 : E) (Units.mk0 R⁻¹ (inv_ne_zero hR.ne')))
  have hT : ∀ x, T x = R⁻¹ • (T₀ x - c) := fun x => by
    simp [T, AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply,
      neg_add_eq_sub]
  refine ⟨T, fun y hy => ?_, ?_⟩
  · -- The preimage of a small ball lies in the interior of the simplex of `b`, inside `s`.
    have hy' : T₀.symm (c + R • y) ∈ s := by
      have hpos : ∀ i, 0 < b.coord i (T₀.symm (c + R • y)) := fun i => by
        rw [← hcoord, AffineEquiv.apply_symm_apply]
        refine hball ?_ i
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
        rw [mem_ball_zero_iff, lt_div_iff₀ hR] at hy
        linarith
      have hhull : convexHull ℝ (range b) ⊆ closure s :=
        convexHull_min (range_subset_iff.2 hbs) hs.closure
      have hmem : T₀.symm (c + R • y) ∈ interior (convexHull ℝ (range b)) := by
        rw [b.interior_convexHull]
        exact hpos
      exact interior_subset (hs.interior_closure_eq_interior_of_nonempty_interior hsi ▸
        interior_mono hhull hmem)
    refine ⟨_, hy', ?_⟩
    rw [hT, AffineEquiv.apply_symm_apply, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ hR.ne', one_smul]
  · -- The image of `s` lies within distance `R - 1` of `c` before rescaling.
    rintro - ⟨x, hx, rfl⟩
    have hle := hbound (T₀ x) fun i => by
      rw [hcoord]
      exact hb x (subset_closure hx) i
    rw [mem_ball_zero_iff, hT, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
      inv_mul_lt_iff₀ hR, mul_one]
    linarith [norm_sub_le (T₀ x) c]

end TauCeti
end
end DevelopmentSource16

/- Source module: Projection.Normalization.Transforms. SHA256: c1498a0ccd323e002f00788c710cc5f90de007fbd76dab38f94afa9ee6d35b4b -/
section DevelopmentSource17






/-!
# Actual transformations of marked bodies

The first normalization is affine and places an arbitrary body with nonempty
interior between fixed concentric balls. The second is the maximal-minor row
normalization. Every transformation of the marks is accompanied by its exact
mixed-volume factor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Metric Module MeasureTheory
open scoped Pointwise BigOperators Matrix

namespace RankThreeProjection
open VolumePolynomials

/-- The continuous linear map represented by a real matrix in the coordinate
basis. -/
def matrixLinear {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Space n →L[ℝ] Space n :=
  (Matrix.toLin' M).toContinuousLinearMap

@[simp] theorem matrixLinear_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : matrixLinear M x = M *ᵥ x := rfl

@[simp] theorem matrixLinear_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (matrixLinear M).toLinearMap = M.det := LinearMap.det_toLin' M

theorem allMarkedArray_smul_marks {n k : ℕ} (K : Body n) (U : Fin n → Space n)
    (g : ℝ) (hg : 0 ≤ g) (I : Deleted n k) :
    allMarkedArray K (fun i => g • U i) I = g ^ k * allMarkedArray K U I := by
  let c : Fin (n - k + k) → ℝ :=
    Fin.append (fun _ : Fin (n - k) => 1) (fun _ : Fin k => g)
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [c, Fin.append_left] using (zero_le_one : (0 : ℝ) ≤ 1)
    · intro j
      simpa only [c, Fin.append_right] using hg
  have htuple : markedTuple K (fun i => g • U i) I =
      fun j => c j • markedTuple K U I j := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [markedTuple, c, Fin.append_left, one_smul]
    · intro i
      simp only [markedTuple, c, Fin.append_right, centeredSegment_smul]
  have hprod : (∏ j, c j) = g ^ k := by
    rw [Fin.prod_univ_add]
    simp only [c, Fin.append_left, Fin.append_right, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, one_pow, one_mul]
  unfold allMarkedArray
  rw [htuple, mixedVolume_independent_smul volume _ c hc, hprod]
  rw [mul_left_comm]

theorem allMarkedArray_smul_body {n k : ℕ} (K : Body n) (U : Fin n → Space n)
    (g : ℝ) (hg : 0 ≤ g) (I : Deleted n k) :
    allMarkedArray (g • K) U I = g ^ (n - k) * allMarkedArray K U I := by
  let c : Fin (n - k + k) → ℝ :=
    Fin.append (fun _ : Fin (n - k) => g) (fun _ : Fin k => 1)
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [c, Fin.append_left] using hg
    · intro j
      simpa only [c, Fin.append_right] using (zero_le_one : (0 : ℝ) ≤ 1)
  have htuple : markedTuple (g • K) U I = fun j => c j • markedTuple K U I j := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [markedTuple, c, Fin.append_left]
    · intro i
      simp only [markedTuple, c, Fin.append_right, one_smul]
  have hprod : (∏ j, c j) = g ^ (n - k) := by
    rw [Fin.prod_univ_add]
    simp only [c, Fin.append_left, Fin.append_right, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, one_pow, mul_one]
  unfold allMarkedArray
  rw [htuple, mixedVolume_independent_smul volume _ c hc, hprod]
  rw [mul_left_comm]

theorem allMarkedArray_map {n k : ℕ} (K : Body n) (U : Fin n → Space n)
    (L : Space n →L[ℝ] Space n) (I : Deleted n k) :
    allMarkedArray (mapBody L K) (fun i => L (U i)) I =
      |LinearMap.det L.toLinearMap| * allMarkedArray K U I := by
  have htuple : markedTuple (mapBody L K) (fun i => L (U i)) I =
      fun j => mapBody L (markedTuple K U I j) := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [markedTuple, Fin.append_left]
    · intro i
      simp only [markedTuple, Fin.append_right, map_centeredSegment]
  unfold allMarkedArray
  rw [htuple, mixedVolume_map_linear volume L]
  rw [mul_left_comm]

theorem allMarkedArray_map_smul {n k : ℕ} (K : Body n) (U : Fin n → Space n)
    (L : Space n →L[ℝ] Space n) (g : ℝ) (hg : 0 ≤ g) (I : Deleted n k) :
    allMarkedArray (mapBody L K) (fun i => g • L (U i)) I =
      (g ^ k * |LinearMap.det L.toLinearMap|) * allMarkedArray K U I := by
  rw [allMarkedArray_smul_marks _ _ g hg, allMarkedArray_map, mul_assoc]

theorem allMarkedArray_translate_body {n k : ℕ} (K : Body n)
    (U : Fin n → Space n) (v : Space n) :
    allMarkedArray (k := k) (translateBody v K) U = allMarkedArray K U := by
  funext I
  let w : Fin (n - k + k) → Space n :=
    Fin.append (fun _ : Fin (n - k) => v) (fun _ : Fin k => 0)
  have htuple : markedTuple (translateBody v K) U I =
      fun j => translateBody (w j) (markedTuple K U I j) := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [markedTuple, w, Fin.append_left]
    · intro i
      simp only [markedTuple, w, Fin.append_right, translateBody_zero]
  unfold allMarkedArray
  rw [htuple, mixedVolume_translate]

/-- Entrywise bounded matrices have a uniform operator bound in the actual
coordinate sup norm. -/
theorem norm_matrixLinear_le {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, |G i j| ≤ 1) (x : Space n) :
    ‖matrixLinear G x‖ ≤ (n : ℝ) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg x))).mpr
  intro i
  change ‖∑ j, G i j * x j‖ ≤ (n : ℝ) * ‖x‖
  calc
    ‖∑ j, G i j * x j‖ ≤ ∑ j, ‖G i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖x j‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg (x j)) (hG i j)
    _ ≤ (n : ℝ) * ‖x‖ := by
      simpa only [Fintype.card_fin, nsmul_eq_mul] using Pi.sum_norm_apply_le_norm x

/-- Exact geometric use of the matrix normalizer. The hypothesis on the
`k`-minors is a concrete bound on determinants of the actual marked vectors.
-/
theorem normalize_marked_pair {n k : ℕ} (hk : 0 < k) {ρ D : ℝ}
    (K : Body n) (U : Fin n → Space n)
    (hinner : closedBall 0 ρ ⊆ (K : Set (Space n)))
    (houter : (K : Set (Space n)) ⊆ closedBall 0 1)
    (hminor : ProjectionVolumes.minorMaximum (columnsMatrix U) k ≤ D) :
    ∃ (L : Body n) (V : Fin n → Space n) (s : Finset (Fin n)),
      s.card < k ∧ coordinateDisk s ρ ⊆ (L : Set (Space n)) ∧
      (L : Set (Space n)) ⊆ closedBall 0 (n : ℝ) ∧ ‖V‖ ≤ max 1 D ∧
      allMarkedArray (k := k) L V = allMarkedArray K U := by
  obtain ⟨g, G, s, hg, _hdet, hs, hG, hGU, hscale, hfix⟩ :=
    ProjectionVolumes.exists_matrix_normalization hk (columnsMatrix U)
  let L := mapBody (matrixLinear G) K
  let V : Fin n → Space n := fun i => g • matrixLinear G (U i)
  refine ⟨L, V, s, hs, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨x, hinner (mem_closedBall_zero_iff.mpr hx.1), ?_⟩
    exact hfix x hx.2
  · rintro y ⟨x, hx, rfl⟩
    apply mem_closedBall_zero_iff.mpr
    have hnorm := mem_closedBall_zero_iff.mp (houter hx)
    exact (norm_matrixLinear_le G hG x).trans
      ((mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg n)).trans_eq (mul_one _))
  · have hD : 0 ≤ max 1 D := zero_le_one.trans (le_max_left _ _)
    apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro i
    change |(g • (G * columnsMatrix U)) i j| ≤ max 1 D
    exact (hGU i j).trans (max_le_max le_rfl hminor)
  · funext I
    change allMarkedArray (mapBody (matrixLinear G) K)
      (fun i => g • matrixLinear G (U i)) I = _
    rw [allMarkedArray_map_smul K U (matrixLinear G) g (zero_le_one.trans hg),
      matrixLinear_det, hscale, one_mul]

/-- The affine image is represented using the existing literal linear image
and translation operations on convex bodies. -/
theorem affine_image_as_body {n : ℕ} (T : Space n ≃ᵃ[ℝ] Space n) (K : Body n) :
    T '' (K : Set (Space n)) =
      (translateBody (T 0) (mapBody T.linear.toContinuousLinearEquiv.toContinuousLinearMap K) :
        Set (Space n)) := by
  ext y
  simp only [coe_translateBody, coe_mapBody, Set.mem_vadd_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨T.linear x, ⟨x, hx, rfl⟩, ?_⟩
    simpa only [vadd_eq_add, add_zero, add_comm] using (T.map_vadd 0 x).symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    change T x = T 0 + T.linear x
    simpa only [vadd_eq_add, add_zero, add_comm] using T.map_vadd 0 x

/-- Uniform affine normalization with marked coefficients preserved exactly.
The inner radius depends only on the ambient coordinate space. -/
theorem exists_affine_normalized_marked_pairs (n : ℕ) :
    ∃ ρ > 0, ∀ (k : ℕ), 0 < k → ∀ (K : Body n) (U : Fin n → Space n),
      (interior (K : Set (Space n))).Nonempty →
      ∃ (L : Body n) (V : Fin n → Space n),
        closedBall 0 ρ ⊆ (L : Set (Space n)) ∧
        (L : Set (Space n)) ⊆ closedBall 0 1 ∧
        allMarkedArray (k := k) L V = allMarkedArray K U := by
  obtain ⟨r, hr, hnormal⟩ :=
    TauCeti.exists_affineEquiv_ball_subset_image_subset_ball (Space n)
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro k hk K U hKint
  obtain ⟨T, hinner, houter⟩ := hnormal (K : Set (Space n)) K.convex K.isBounded hKint
  let A := T.linear.toContinuousLinearEquiv.toContinuousLinearMap
  let d : ℝ := |LinearMap.det A.toLinearMap|
  have hd : 0 < d := abs_pos.mpr T.linear.isUnit_det'.ne_zero
  let a : ℝ := d ^ ((k : ℝ)⁻¹)
  have ha : 0 < a := Real.rpow_pos_of_pos hd _
  have hscale : (a⁻¹) ^ k * d = 1 := by
    rw [inv_pow, Real.rpow_inv_natCast_pow hd.le hk.ne', inv_mul_cancel₀ hd.ne']
  let L := translateBody (T 0) (mapBody A K)
  let V : Fin n → Space n := fun i => a⁻¹ • A (U i)
  have heq : T '' (K : Set (Space n)) = (L : Set (Space n)) := affine_image_as_body T K
  refine ⟨L, V, ?_, ?_, ?_⟩
  · rw [← heq]
    exact (closedBall_subset_ball (half_lt_self hr)).trans hinner
  · rw [← heq]
    exact houter.trans ball_subset_closedBall
  · rw [allMarkedArray_translate_body]
    funext I
    rw [allMarkedArray_map_smul K U A a⁻¹ (inv_nonneg.mpr ha.le), hscale, one_mul]

end RankThreeProjection
end
end
end DevelopmentSource17

/- Source module: Projection.Normalization.OrderedMinors. SHA256: 4cf429133b88b0d9bf437dcd42f5052b5a2bdc35a6dcee55db48d4db41ea4ab3 -/
section DevelopmentSource18




/-! # Ordered representatives of actual maximal minors -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace ProjectionVolumes

/-- An injective list enumerates its literal finite image bijectively. -/
def imageEnumeration {n k : ℕ} (f : Fin k → Fin n) (hf : Function.Injective f) :
    Fin k ≃ (Finset.univ.image f : Finset (Fin n)) :=
  Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j hij => hf (congrArg Subtype.val hij), by
      rintro ⟨x, hx⟩
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl⟩⟩

@[simp] theorem imageEnumeration_val {n k : ℕ} (f : Fin k → Fin n)
    (hf : Function.Injective f) (i : Fin k) :
    (imageEnumeration f hf i).val = f i := rfl

/-- Every injective enumeration differs from its increasing enumeration by a
permutation of its domain. -/
theorem exists_sorting_permutation {n k : ℕ} (f : Fin k → Fin n)
    (hf : Function.Injective f) :
    ∃ (s : Finset (Fin n)) (hs : s.card = k) (e : Equiv.Perm (Fin k)),
      (∀ i, f (e i) = s.orderEmbOfFin hs i) := by
  let s := Finset.univ.image f
  have hs : s.card = k := by
    simp only [s, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let e := (s.orderIsoOfFin hs).toEquiv.trans (imageEnumeration f hf).symm
  refine ⟨s, hs, e, ?_⟩
  intro i
  have h := congrArg Subtype.val
    ((imageEnumeration f hf).apply_symm_apply ((s.orderIsoOfFin hs) i))
  exact h

/-- The positive maximum of absolute minors is attained using the canonical
increasing row and column enumerations of two finite subsets. -/
theorem exists_ordered_maximal_minor {n k : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hpos : 0 < minorMaximum M k) :
    ∃ (I J : Finset (Fin n)) (hI : I.card = k) (hJ : J.card = k),
      |(M.submatrix (J.orderEmbOfFin hJ) (I.orderEmbOfFin hI)).det| =
        minorMaximum M k := by
  obtain ⟨rows, cols, hdet⟩ := exists_maximal_minor M hpos
  have hne : (M.submatrix rows cols).det ≠ 0 := abs_pos.mp (hdet.symm ▸ hpos)
  obtain ⟨J, hJ, er, her⟩ :=
    exists_sorting_permutation rows (injective_rows_of_minor_ne_zero M rows cols hne)
  obtain ⟨I, hI, ec, hec⟩ :=
    exists_sorting_permutation cols (injective_cols_of_minor_ne_zero M rows cols hne)
  refine ⟨I, J, hI, hJ, ?_⟩
  have hmat : (M.submatrix rows cols).submatrix er ec =
      M.submatrix (J.orderEmbOfFin hJ) (I.orderEmbOfFin hI) := by
    ext i j
    simp only [Matrix.submatrix_apply, her, hec]
  rw [← hmat, Matrix.abs_det_submatrix_equiv_equiv, hdet]

end ProjectionVolumes
end
end
end DevelopmentSource18

/- Source module: VolumePolynomials.ProjectionMixedVolumeOrder. SHA256: 65e5cb4f0530ac8464caf1543cd87c03bc0de4eadada3e08c6add3730c094822 -/
section DevelopmentSource19


/- Exact supplemental source closure; generated by generate_volume_supplements.py.
   The original theorem statements and proof bodies are unchanged. -/


set_option Elab.async false

/- BEGIN SOURCE: VolumePolynomials/MixedVolumeOrder.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! Coordinatewise monotonicity and strict positivity from a common
contained body. All inequalities concern the previously defined, actual
dimension-matched mixed volume. -/

open Set MeasureTheory Module
open scoped BigOperators Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem mixedVolume_mono_update {n : ℕ} (hdim : finrank ℝ E = n + 1)
    (K : Fin (n + 1) → ConvexBody E) (i : Fin (n + 1))
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume μ (Function.update K i A) ≤ mixedVolume μ (Function.update K i B) := by
  first
  | letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
    let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i
    let L : Fin n → ConvexBody E := fun j => K (e j.succ)
    have htuple (C : ConvexBody E) :
        (fun j => (Function.update K i C) (e j)) = Fin.cons C L := by
      first
      | funext j
        cases j using Fin.cases with
        | zero => simp [e]
        | succ j =>
            have hne : e j.succ ≠ i := by
              first
              | intro heq
                have he0 : e 0 = i := by simp [e]
                have hzero := e.injective (heq.trans he0.symm)
                exact Fin.succ_ne_zero j hzero
            simp only [Function.update_of_ne hne, Fin.cons_succ, L]
    rw [← mixedVolume_reindex μ (Function.update K i A) e,
      ← mixedVolume_reindex μ (Function.update K i B) e, htuple A, htuple B]
    exact mixedVolume_mono_first_all μ L hdim A B hAB

theorem mixedVolume_mono_all {n : ℕ} (hdim : finrank ℝ E = n + 1)
    (K L : Fin (n + 1) → ConvexBody E) (hKL : ∀ i, K i ≤ L i) :
    mixedVolume μ K ≤ mixedVolume μ L := by
  first
  | classical
    have haux (s : Finset (Fin (n + 1))) :
        mixedVolume μ K ≤ mixedVolume μ (s.piecewise L K) := by
      first
      | induction s using Finset.induction_on with
        | empty => simp only [Finset.piecewise_empty, le_refl]
        | @insert i s hi ih =>
            have hold : Function.update (s.piecewise L K) i (K i) = s.piecewise L K := by
              first
              | ext j
                by_cases hji : j = i
                · subst j
                  simp [Finset.piecewise, hi]
                · simp [hji]
            have hnew : Function.update (s.piecewise L K) i (L i) =
                (insert i s).piecewise L K := by
              first
              | ext j
                by_cases hji : j = i
                · subst j
                  simp [Finset.piecewise]
                · simp [Finset.piecewise, hji]
            have hm := mixedVolume_mono_update μ hdim (s.piecewise L K) i (K i) (L i) (hKL i)
            rw [hold, hnew] at hm
            exact ih.trans hm
    simpa only [Finset.piecewise_univ] using haux Finset.univ

theorem mixedVolume_ge_common_body {n : ℕ} (hdim : finrank ℝ E = n + 1)
    (K : Fin (n + 1) → ConvexBody E) (S : ConvexBody E)
    (p : Fin (n + 1) → E) (hcontain : ∀ i, translateBody (p i) S ≤ K i) :
    μ.real (S : Set E) ≤ mixedVolume μ K := by
  first
  | have h := mixedVolume_mono_all μ hdim (fun i => translateBody (p i) S) K hcontain
    rwa [mixedVolume_translate, mixedVolume_diagonal μ hdim] at h

theorem mixedVolume_pos_of_common_body {n : ℕ} (hdim : finrank ℝ E = n + 1)
    (K : Fin (n + 1) → ConvexBody E) (S : ConvexBody E)
    (hS : 0 < μ.real (S : Set E))
    (p : Fin (n + 1) → E) (hcontain : ∀ i, translateBody (p i) S ≤ K i) :
    0 < mixedVolume μ K :=
  hS.trans_le (mixedVolume_ge_common_body μ hdim K S p hcontain)

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedVolumeOrder.lean -/
end DevelopmentSource19

/- Source module: Projection.Normalization.MinorBounds. SHA256: b1f075d4d33aae16bcfc99042365ab209523b70180afc675be541c5aa2a9b3e8 -/
section DevelopmentSource20







/-!
# Bounds on actual minors from marked projection coefficients

Replace the repeated body arguments by short coordinate segments lying in its
inner ball. Monotonicity and the determinant formula for actual segment bodies
then bound each minor of the marked-vector matrix. The determinant reduction
uses a complementary coordinate frame, including the cases `k = 0` and `k = n`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Metric Module MeasureTheory
open scoped BigOperators Pointwise

namespace RankThreeProjection
open VolumePolynomials

/-- Renaming the finite index type along a numerical equality changes no
argument or value of the actual mixed-volume definition. -/
theorem mixedVolume_finCongr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {a b : ℕ} (h : a = b) (K : Fin a → ConvexBody E) :
    mixedVolume μ (fun i : Fin b => K ((finCongr h).symm i)) = mixedVolume μ K := by
  subst b
  rfl

/-- Dimension-matched monotonicity, also admitting the empty tuple. -/
theorem mixedVolume_mono_dimension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {d : ℕ} (hdim : finrank ℝ E = d) (K L : Fin d → ConvexBody E)
    (hKL : ∀ i, K i ≤ L i) : mixedVolume μ K ≤ mixedVolume μ L := by
  cases d with
  | zero =>
    have h : K = L := funext fun i => Fin.elim0 i
    rw [h]
  | succ d => exact mixedVolume_mono_all μ hdim K L hKL

theorem centeredSegment_subset_closedBall {n : ℕ} {ρ : ℝ} (v : Space n)
    (hv : ‖v‖ ≤ ρ) : (centeredSegment v : Set (Space n)) ⊆ closedBall 0 ρ := by
  apply (convex_closedBall (0 : Space n) ρ).segment_subset
  · apply mem_closedBall_zero_iff.mpr
    rw [norm_smul]
    norm_num only [Real.norm_eq_abs, abs_neg, abs_div, abs_one]
    exact (mul_le_of_le_one_left (norm_nonneg v) (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hv
  · apply mem_closedBall_zero_iff.mpr
    rw [norm_smul]
    norm_num only [Real.norm_eq_abs, abs_div, abs_one]
    exact (mul_le_of_le_one_left (norm_nonneg v) (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hv

/-- Completing the rows of a minor by the complementary coordinate vectors
turns its determinant into the volume of an actual tuple of `n` segments. -/
theorem complete_minor_by_coordinate_segments {n k : ℕ} (hkn : k ≤ n)
    (U : Fin n → Space n) (rows cols : Fin k → Fin n) (hrows : Function.Injective rows)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ W : Fin (n - k + k) → Space n,
      (∀ i : Fin (n - k), ‖W (Fin.castAdd k i)‖ ≤ ρ) ∧
      (∀ i : Fin k, W (Fin.natAdd (n - k) i) = U (cols i)) ∧
      (n.factorial : ℝ) * mixedVolume volume (fun i => centeredSegment (W i)) =
        ρ ^ (n - k) * |((columnsMatrix U).submatrix rows cols).det| := by
  classical
  let τ := {i : Fin n // i ∉ Set.range rows}
  let e₀ : Fin k ⊕ τ ≃ Fin n := ProjectionVolumes.selectionEquiv rows hrows
  have hcard : Fintype.card τ = n - k := by
    have h := Fintype.card_congr e₀
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega
  let et : Fin (n - k) ≃ τ := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, hcard])
  let er : Fin (n - k) ⊕ Fin k ≃ Fin n :=
    ((Equiv.sumCongr et (Equiv.refl (Fin k))).trans (Equiv.sumComm τ (Fin k))).trans e₀
  have her₁ (i : Fin (n - k)) : er (Sum.inl i) = (et i).val := rfl
  have her₂ (i : Fin k) : er (Sum.inr i) = rows i := rfl
  have hsum : n - k + k = n := Nat.sub_add_cancel hkn
  let ec : Fin (n - k) ⊕ Fin k ≃ Fin n := finSumFinEquiv.trans (finCongr hsum)
  let W : Fin (n - k + k) → Space n :=
    Fin.append (fun i : Fin (n - k) => ρ • Pi.single (et i).val 1)
      (fun i : Fin k => U (cols i))
  let V : Fin n → Space n := fun i => W ((finCongr hsum).symm i)
  have hV₁ (i : Fin (n - k)) : V (ec (Sum.inl i)) = ρ • Pi.single (et i).val 1 := by
    simp only [V, ec, Equiv.trans_apply, Equiv.symm_apply_apply,
      finSumFinEquiv_apply_left, W, Fin.append_left]
  have hV₂ (i : Fin k) : V (ec (Sum.inr i)) = U (cols i) := by
    simp only [V, ec, Equiv.trans_apply, Equiv.symm_apply_apply,
      finSumFinEquiv_apply_right, W, Fin.append_right]
  let B := (columnsMatrix U).submatrix rows cols
  let A : Matrix (Fin (n - k)) (Fin k) ℝ := fun i j => U (cols j) (et i).val
  have hblock : (columnsMatrix V).submatrix er ec =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin (n - k) => ρ)) A 0 B := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [Matrix.submatrix_apply, columnsMatrix, hV₁, her₁,
          Matrix.fromBlocks_apply₁₁]
        by_cases hij : i = j
        · subst j
          simp [Matrix.diagonal_apply]
        · have hne : (et i).val ≠ (et j).val := fun h => hij (et.injective (Subtype.ext h))
          simp [Pi.single_apply, Matrix.diagonal_apply, hij, Ne.symm hij, hne, Ne.symm hne]
      | inr j =>
        simp only [Matrix.submatrix_apply, columnsMatrix, hV₂, her₁,
          Matrix.fromBlocks_apply₁₂, A]
        rfl
    | inr i =>
      cases j with
      | inl j =>
        simp only [Matrix.submatrix_apply, columnsMatrix, hV₁, her₂,
          Matrix.fromBlocks_apply₂₁]
        have hne : rows i ≠ (et j).val := fun h => (et j).property ⟨i, h⟩
        simp [Pi.single_apply, hne, Ne.symm hne]
      | inr j =>
        simp only [Matrix.submatrix_apply, columnsMatrix, hV₂, her₂,
          Matrix.fromBlocks_apply₂₂, B]
  have hdet : |(columnsMatrix V).det| = ρ ^ (n - k) * |B.det| := by
    rw [← Matrix.abs_det_submatrix_equiv_equiv er ec (columnsMatrix V), hblock,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, abs_mul, abs_of_nonneg (pow_nonneg hρ _)]
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    simpa only [W, Fin.append_left, norm_smul, Pi.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg hρ] using (le_rfl : ρ ≤ ρ)
  · intro i
    exact Fin.append_right _ _ i
  · have hcast := mixedVolume_finCongr volume hsum (fun i => centeredSegment (W i))
    rw [← hcast, mixedVolume_centered_segments, hdet]

/-- A selected minor is bounded by its actual marked coefficient. No spanning
or invertibility condition is required on the marked vectors. -/
theorem ordered_minor_bound {n k : ℕ} (hkn : k ≤ n)
    (K : Body n) (U : Fin n → Space n) (I J : Deleted n k)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hinner : closedBall 0 ρ ⊆ (K : Set (Space n))) :
    ρ ^ (n - k) *
        |((columnsMatrix U).submatrix (J.val.orderEmbOfFin J.property)
          (I.val.orderEmbOfFin I.property)).det| ≤
      ((n - k).factorial : ℝ) * allMarkedArray K U I := by
  obtain ⟨W, hWnorm, hWmark, hWdet⟩ := complete_minor_by_coordinate_segments hkn U
    (J.val.orderEmbOfFin J.property) (I.val.orderEmbOfFin I.property)
    (J.val.orderEmbOfFin J.property).injective ρ hρ
  have hcontain : ∀ i, centeredSegment (W i) ≤ markedTuple K U I i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [markedTuple, Fin.append_left]
      apply SetLike.coe_subset_coe.mp
      exact (centeredSegment_subset_closedBall _ (hWnorm j)).trans hinner
    · intro j
      simp only [markedTuple, Fin.append_right, hWmark]
      exact le_rfl
  have hdim : finrank ℝ (Space n) = n - k + k := by
    simp only [Space, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Nat.sub_add_cancel hkn]
  have hmono := mixedVolume_mono_dimension volume hdim
    (fun i => centeredSegment (W i)) (markedTuple K U I) hcontain
  rw [← hWdet]
  refine (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n.factorial)).trans_eq ?_
  unfold allMarkedArray
  have hf : ((n - k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  field_simp

/-- A uniform bound on marked coefficients gives a uniform bound on all actual
`k`-minors once the repeated body contains a fixed inner ball. -/
theorem minorMaximum_bound {n k : ℕ} (hkn : k ≤ n)
    (K : Body n) (U : Fin n → Space n) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hinner : closedBall 0 ρ ⊆ (K : Set (Space n)))
    (hcoeff : ∀ I : Deleted n k, allMarkedArray K U I ≤ B) :
    ProjectionVolumes.minorMaximum (columnsMatrix U) k ≤
      ((n - k).factorial : ℝ) * B / ρ ^ (n - k) := by
  by_cases hzero : ProjectionVolumes.minorMaximum (columnsMatrix U) k = 0
  · rw [hzero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (pow_nonneg hρ.le _)
  have hpos : 0 < ProjectionVolumes.minorMaximum (columnsMatrix U) k :=
    lt_of_le_of_ne (ProjectionVolumes.minorMaximum_nonneg _ _) (Ne.symm hzero)
  obtain ⟨I, J, hI, hJ, hmax⟩ :=
    ProjectionVolumes.exists_ordered_maximal_minor (columnsMatrix U) hpos
  have h := ordered_minor_bound hkn K U ⟨I, hI⟩ ⟨J, hJ⟩ hρ.le hinner
  rw [hmax] at h
  apply (le_div_iff₀ (pow_pos hρ _)).mpr
  rw [mul_comm]
  exact h.trans (mul_le_mul_of_nonneg_left (hcoeff ⟨I, hI⟩) (Nat.cast_nonneg _))

end RankThreeProjection
end
end
end DevelopmentSource20

/- Source module: Projection.Normalization.Compactification. SHA256: fd0c56d07c7a560dc7f6ab635d2e76829448e3d0b505922271f50bf6281745d9 -/
section DevelopmentSource21






/-!
# Compactification of actual marked mixed-volume arrays

For every `0 < k ≤ n`, the marked image is closed. Moreover, every point in
that image has a representation whose repeated body has affine dimension at
least `n - k + 1`. These assertions concern the actual mixed volume, compact
convex bodies, and segment vectors from `Projection.Topology`.

To obtain Theorem 3.1 in its coordinate-projection form, the remaining
identification is between this marked image and the closure of coordinate
projection arrays. That identification uses coordinate extrusion and density
of invertible marked frames; neither is encoded as a hypothesis here.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric Module MeasureTheory Filter
open scoped Topology Pointwise

namespace RankThreeProjection
open VolumePolynomials

/-- Arrays obtained from actual bodies and arbitrary actual segment marks. -/
def markedArrayLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  Set.range (fun q : Body n × (Fin n → Space n) => allMarkedArray (k := k) q.1 q.2)

/-- The same marked construction with a repeated body having nonempty ambient
interior. No condition is imposed on the marked vectors. -/
def fullMarkedLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  {P | ∃ (K : Body n) (U : Fin n → Space n),
    (interior (K : Set (Space n))).Nonempty ∧ allMarkedArray K U = P}

/-- A positive thickening by a body with interior has nonempty interior even
when the original body is lower dimensional. -/
theorem interior_body_thickening {n : ℕ} (K Q : Body n)
    (hQ : (0 : Space n) ∈ interior (Q : Set (Space n))) {t : ℝ} (ht : 0 < t) :
    (interior ((K + t • Q : Body n) : Set (Space n))).Nonempty := by
  obtain ⟨x, hx⟩ := K.nonempty
  have htQ : (0 : Space n) ∈ interior ((t • Q : Body n) : Set (Space n)) := by
    rw [ConvexBody.coe_smul, interior_smul₀ ht.ne']
    exact ⟨0, hQ, smul_zero t⟩
  refine ⟨x, ?_⟩
  change x ∈ interior ((K : Set (Space n)) + ((t • Q : Body n) : Set (Space n)))
  exact subset_interior_add_right (Set.mem_add.mpr ⟨x, hx, 0, htQ, add_zero x⟩)

/-- Actual convex bodies with nonempty ambient interior are dense in all
nonempty compact convex bodies, in every dimension. -/
theorem dense_full_bodies (n : ℕ) :
    Dense {K : Body n | (interior (K : Set (Space n))).Nonempty} := by
  rw [Metric.dense_iff]
  intro K ε hε
  obtain ⟨Q, _hfinite, hQ⟩ := exists_finiteHull_with_zero_interior (E := Space n)
  have hc : Continuous (fun t : ℝ => K + t • Q) := by fun_prop
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := (0 : ℝ))) ε hε
  have ht : 0 < δ / 2 := half_pos hδ
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact half_lt_self hδ
  refine ⟨K + (δ / 2) • Q, ?_, interior_body_thickening K Q hQ ht⟩
  simpa only [mem_ball, body_zero_smul, add_zero] using hnear hdist

theorem marked_mem_closure_fullMarked {n k : ℕ} (K : Body n) (U : Fin n → Space n) :
    allMarkedArray (k := k) K U ∈ closure (fullMarkedLocus n k) := by
  let f : Body n → Deleted n k → ℝ := fun L => allMarkedArray L U
  have hf : Continuous f := by
    simpa only [f, Function.comp_def, id_eq] using
      (continuous_allMarkedArray (n := n) (k := k)).comp
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : Body n => U)))
  exact map_mem_closure (f := f) (x := K) hf ((dense_full_bodies n) K)
    (fun L hL => ⟨L, U, hL, rfl⟩)

/-- Uniform bounds for all full-dimensional marked representations whose
coefficients have one common upper bound. -/
theorem uniform_normalized_representations (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ ρ > 0, ∃ R D : ℝ, ∀ (K : Body n) (U : Fin n → Space n),
      (interior (K : Set (Space n))).Nonempty →
      (∀ I : Deleted n k, allMarkedArray K U I ≤ B) →
      ∃ (L : Body n) (V : Fin n → Space n) (s : Finset (Fin n)),
        s.card < k ∧ coordinateDisk s ρ ⊆ (L : Set (Space n)) ∧
        (L : Set (Space n)) ⊆ closedBall 0 R ∧ ‖V‖ ≤ D ∧
        allMarkedArray (k := k) L V = allMarkedArray K U := by
  obtain ⟨ρ, hρ, hAffine⟩ := exists_affine_normalized_marked_pairs n
  refine ⟨ρ, hρ, (n : ℝ), max 1 (((n - k).factorial : ℝ) * B / ρ ^ (n - k)), ?_⟩
  intro K U hfull hcoeff
  obtain ⟨L, V, hinner, houter, heq⟩ := hAffine k hk K U hfull
  have hcoeff' : ∀ I : Deleted n k, allMarkedArray L V I ≤ B := by
    intro I
    rw [heq]
    exact hcoeff I
  obtain ⟨N, W, s, hs, hdisk, hball, hmarks, harray⟩ :=
    normalize_marked_pair hk L V hinner houter
      (minorMaximum_bound hkn L V hρ hB hinner hcoeff')
  exact ⟨N, W, s, hs, hdisk, hball, hmarks, harray.trans heq⟩

/-- A convergent sequence of marked arrays with full-dimensional repeated
bodies has a marked limit retaining at least `n - k + 1` affine dimensions. -/
theorem fullMarked_limit {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (p : ℕ → Deleted n k → ℝ) (P : Deleted n k → ℝ)
    (hp : Tendsto p atTop (𝓝 P)) (hfull : ∀ m, p m ∈ fullMarkedLocus n k) :
    ∃ (K : Body n) (U : Fin n → Space n),
      n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  obtain ⟨B, hBpos, hB⟩ := (Metric.isBounded_range_of_tendsto p hp).exists_pos_norm_le
  obtain ⟨ρ, hρ, R, D, hnormal⟩ := uniform_normalized_representations n k hk hkn B hBpos.le
  apply marked_limit_of_bounded_representations hkn hρ p P hp
  intro m
  obtain ⟨K, U, hK, heq⟩ := hfull m
  have hcoeff : ∀ I : Deleted n k, allMarkedArray K U I ≤ B := by
    intro I
    rw [heq]
    exact (le_abs_self _).trans ((norm_le_pi_norm (p m) I).trans (hB (p m) ⟨m, rfl⟩))
  obtain ⟨L, V, s, hs, hdisk, houter, hmarks, harray⟩ := hnormal K U hK hcoeff
  exact ⟨L, V, s, hs, hdisk, houter, hmarks, harray.trans heq⟩

/-- The marked compactification, with the full affine-dimension conclusion. -/
theorem fullMarked_closure_representation {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {P : Deleted n k → ℝ} (hP : P ∈ closure (fullMarkedLocus n k)) :
    ∃ (K : Body n) (U : Fin n → Space n),
      n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hP
  exact fullMarked_limit hk hkn p P hlim hp

theorem closure_fullMarkedLocus_eq_markedArrayLocus {n k : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) :
    closure (fullMarkedLocus n k) = markedArrayLocus n k := by
  apply Set.Subset.antisymm
  · intro P hP
    obtain ⟨K, U, _hdim, heq⟩ := fullMarked_closure_representation hk hkn hP
    exact ⟨(K, U), heq⟩
  · rintro P ⟨⟨K, U⟩, rfl⟩
    exact marked_mem_closure_fullMarked K U

theorem isClosed_markedArrayLocus {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    IsClosed (markedArrayLocus n k) := by
  rw [← closure_fullMarkedLocus_eq_markedArrayLocus hk hkn]
  exact isClosed_closure

theorem marked_representation_with_dimension {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {P : Deleted n k → ℝ} (hP : P ∈ markedArrayLocus n k) :
    ∃ (K : Body n) (U : Fin n → Space n),
      n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  apply fullMarked_closure_representation hk hkn
  rwa [closure_fullMarkedLocus_eq_markedArrayLocus hk hkn]

end RankThreeProjection
end
end
end DevelopmentSource21

/- Source module: Projection.Normalization.Frames. SHA256: ef4bf82dc882735c2bcc065f3f15687f6f18ba5be037aeb05379e13a0fb046ce -/
section DevelopmentSource22





/-!
# Invertible frames and coordinate marked arrays

Invertible marks are dense, by the finite zero set of the characteristic
polynomial. An invertible marked frame can be pulled back to the standard
coordinate frame while rescaling the repeated body by the exact determinant
power. This proves the marked compactification for standard coordinate marks.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Metric Module MeasureTheory
open scoped Topology Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

def standardMarks (n : ℕ) : Fin n → Space n := fun i => Pi.single i 1

def invertibleMarks (n : ℕ) : Set (Fin n → Space n) :=
  {U | (columnsMatrix U).det ≠ 0}

def basisMarkedLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  Set.range (fun K : Body n => allMarkedArray (k := k) K (standardMarks n))

/-- Density of genuinely invertible marked-vector matrices. The only excluded
shift parameters are roots of one nonzero characteristic polynomial. -/
theorem dense_invertibleMarks (n : ℕ) : Dense (invertibleMarks n) := by
  intro U
  let M := columnsMatrix U
  let f : ℝ → Fin n → Space n := fun t i => U i + t • standardMarks n i
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfzero : f 0 = U := by
    funext i
    simp only [f, zero_smul, add_zero]
  have hmatrix (t : ℝ) : columnsMatrix (f t) = Matrix.scalar (Fin n) t + M := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [columnsMatrix, f, standardMarks, Matrix.scalar_apply, Matrix.diagonal_apply,
        Pi.single_apply, add_comm, M]
    · simp [columnsMatrix, f, standardMarks, Matrix.scalar_apply, Matrix.diagonal_apply,
        Pi.single_apply, hij, Ne.symm hij, add_comm, M]
  have hfinite : Set.Finite {t : ℝ | Polynomial.IsRoot (-M).charpoly t} :=
    Polynomial.finite_setOfPred_isRoot (-M).charpoly_monic.ne_zero
  have hdense : Dense {t : ℝ | (-M).charpoly.eval t ≠ 0} := by
    convert (dense_univ : Dense (Set.univ : Set ℝ)).sdiff_finite hfinite using 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, true_and, Polynomial.IsRoot]
  have hmaps : MapsTo f {t : ℝ | (-M).charpoly.eval t ≠ 0} (invertibleMarks n) := by
    intro t ht
    change (-M).charpoly.eval t ≠ 0 at ht
    change (columnsMatrix (f t)).det ≠ 0
    rw [hmatrix]
    simpa only [Matrix.eval_charpoly, sub_neg_eq_add] using ht
  have hclosure := map_mem_closure hf (hdense (0 : ℝ)) hmaps
  simpa only [hfzero] using hclosure

/-- Pull an actual invertible marked frame back to standard coordinate marks.
The factor on the repeated body is `|det A|^(1/(n-k))`. -/
theorem invertible_frame_pullback {n k : ℕ} (hkn : k < n)
    (K : Body n) (U : Fin n → Space n) (hU : U ∈ invertibleMarks n) :
    ∃ L : Body n, allMarkedArray (k := k) L (standardMarks n) = allMarkedArray K U := by
  let A := columnsLinear U
  have hA : LinearMap.det A.toLinearMap ≠ 0 := by
    rw [columnsLinear_det]
    exact hU
  let e : Space n ≃L[ℝ] Space n := A.toContinuousLinearEquivOfDetNeZero hA
  let d : ℝ := |LinearMap.det A.toLinearMap|
  have hd : 0 < d := abs_pos.mpr hA
  let r : ℝ := d ^ ((n - k : ℕ) : ℝ)⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos hd _
  have hnk : n - k ≠ 0 := (Nat.sub_pos_of_lt hkn).ne'
  have hpow : r ^ (n - k) = d := Real.rpow_inv_natCast_pow hd.le hnk
  have hmark (i : Fin n) : e.symm (U i) = standardMarks n i := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (columnsLinear_basis U i).symm
  have hdet : |LinearMap.det e.symm.toContinuousLinearMap.toLinearMap| = d⁻¹ := by
    rw [ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
      ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv]
    rfl
  have hmarks : (fun i => e.symm.toContinuousLinearMap (U i)) = standardMarks n := by
    funext i
    exact hmark i
  refine ⟨r • mapBody e.symm.toContinuousLinearMap K, ?_⟩
  funext I
  have hmap : allMarkedArray (mapBody e.symm.toContinuousLinearMap K) (standardMarks n) I =
      d⁻¹ * allMarkedArray K U I := by
    simpa only [hmarks, hdet] using allMarkedArray_map K U e.symm.toContinuousLinearMap I
  rw [allMarkedArray_smul_body _ _ r hr.le, hmap, hpow, ← mul_assoc,
    mul_inv_cancel₀ hd.ne', one_mul]

theorem marked_mem_closure_basisMarked {n k : ℕ} (hkn : k < n)
    (K : Body n) (U : Fin n → Space n) :
    allMarkedArray (k := k) K U ∈ closure (basisMarkedLocus n k) := by
  let f : (Fin n → Space n) → Deleted n k → ℝ := fun V => allMarkedArray K V
  have hf : Continuous f := by
    simpa only [f, Function.comp_def, id_eq] using
      (continuous_allMarkedArray (n := n) (k := k)).comp
        ((continuous_const : Continuous (fun _ : Fin n → Space n => K)).prodMk continuous_id)
  apply map_mem_closure (f := f) (x := U) hf (dense_invertibleMarks n U)
  intro V hV
  obtain ⟨L, hL⟩ := invertible_frame_pullback hkn K V hV
  exact ⟨L, hL⟩

theorem closure_basisMarkedLocus_eq_markedArrayLocus {n k : ℕ}
    (hk : 0 < k) (hkn : k < n) :
    closure (basisMarkedLocus n k) = markedArrayLocus n k := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (isClosed_markedArrayLocus hk hkn.le)
    rintro _ ⟨K, rfl⟩
    exact ⟨(K, standardMarks n), rfl⟩
  · rintro _ ⟨⟨K, U⟩, rfl⟩
    exact marked_mem_closure_basisMarked hkn K U

/-- Theorem 3.1's compactification expressed with genuine mixed volumes and
standard coordinate marks. Coordinate extrusion identifies `basisMarkedLocus`
with the paper's literal coordinate projection-volume locus. -/
theorem basis_marked_compactification {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (basisMarkedLocus n k) ↔
      ∃ (K : Body n) (U : Fin n → Space n),
        n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  rw [closure_basisMarkedLocus_eq_markedArrayLocus hk hkn]
  constructor
  · exact marked_representation_with_dimension hk hkn.le
  · rintro ⟨K, U, _hdim, hKU⟩
    exact ⟨(K, U), hKU⟩

end RankThreeProjection
end
end
end DevelopmentSource22

/- Source module: Projection.Hyperplane. SHA256: 00906ccdcbb8c05b62ed915c7ca2b9b106083adb7704a22b3fdef640fb720eb6 -/
section DevelopmentSource23







@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The shear fixes the hyperplane `{0} × E` pointwise. -/
def hyperplaneShear (v : E) : (ℝ × E) ≃L[ℝ] (ℝ × E) where
  toFun p := (p.1, p.2 - p.1 • v)
  invFun p := (p.1, p.2 + p.1 • v)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_smul] <;> abel
  map_smul' r p := by
    ext <;> simp [smul_sub, smul_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem hyperplaneShear_apply (v : E) (p : ℝ × E) :
    hyperplaneShear v p = (p.1, p.2 - p.1 • v) := rfl

def embedHyperplane (K : ConvexBody E) : ConvexBody (ℝ × E) :=
  mapBody (ContinuousLinearMap.inr ℝ ℝ E) K

@[simp] theorem shear_embedHyperplane (v : E) (K : ConvexBody E) :
    mapBody (hyperplaneShear v).toContinuousLinearMap (embedHyperplane K) =
      embedHyperplane K := by
  rw [embedHyperplane, mapBody_comp]
  congr 1
  apply ContinuousLinearMap.ext
  intro x
  change (0, x - (0 : ℝ) • v) = (0, x)
  simp

@[simp] theorem project_embedHyperplane (K : ConvexBody E) :
    mapBody (ContinuousLinearMap.snd ℝ ℝ E) (embedHyperplane K) = K := by
  rw [embedHyperplane, mapBody_comp]
  have he : (ContinuousLinearMap.snd ℝ ℝ E).comp
      (ContinuousLinearMap.inr ℝ ℝ E) = ContinuousLinearMap.id ℝ E := by ext; rfl
  rw [he]
  apply ConvexBody.ext
  exact Set.image_id _

theorem axisBody_eq_originSegment :
    (axisBody : ConvexBody (ℝ × E)) = originSegment (1, 0) := by
  apply ConvexBody.ext
  ext p
  change p ∈ Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set E) ↔
    p ∈ segment ℝ (0 : ℝ × E) (1, 0)
  rw [segment_eq_image]
  constructor
  · rintro ⟨hp, hp0⟩
    refine ⟨p.1, hp, ?_⟩
    ext <;> simpa using hp0.symm
  · rintro ⟨t, ht, rfl⟩
    simpa using ht

section Measure
variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

set_option backward.isDefEq.respectTransparency false in
/-- Fubini and translation invariance prove that the shear preserves the
actual product volume; no determinant value is assumed. -/
theorem hyperplaneShear_measurePreserving (v : E) :
    MeasurePreserving (hyperplaneShear v) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun t : ℝ => fun x : E => x - t • v)
    (by fun_prop) (Filter.Eventually.of_forall (fun t => by
      simpa only [sub_eq_add_neg] using
        (measurePreserving_add_right (volume : Measure E) (-(t • v))).map_eq))
  change MeasurePreserving (fun p : ℝ × E => (p.1, p.2 - p.1 • v))
    ((volume : Measure ℝ).prod (volume : Measure E))
    ((volume : Measure ℝ).prod (volume : Measure E))
  simpa only [id_eq] using h

theorem mixedVolume_translate_first {d : ℕ} (K : Fin d → ConvexBody E)
    (A : ConvexBody E) (v : E) :
    mixedVolume volume (Fin.cons (translateBody v A) K) =
      mixedVolume volume (Fin.cons A K) := by
  have h := mixedVolume_translate volume (Fin.cons A K) (Fin.cons v (fun _ => 0))
  convert h using 1
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Fin.cons_succ, translateBody_zero]

theorem mixedVolume_first_smul {d : ℕ} (K : Fin d → ConvexBody E)
    (A : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedVolume volume (Fin.cons (r • A) K) =
      r * mixedVolume volume (Fin.cons A K) := by
  simpa only [Fin.update_cons_zero] using
    mixedVolume_smul volume (Fin.cons A K) 0 A hr

/-- Centered and origin-based normal segments give the same extrusion. -/
theorem mixedVolume_centered_axis {d : ℕ} (K : Fin d → ConvexBody (ℝ × E)) :
    (d + 1 : ℝ) * mixedVolume volume (Fin.cons (centeredSegment (1, 0)) K) =
      mixedVolume volume (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ E) (K i)) := by
  rw [centered_eq_translate_origin, mixedVolume_translate_first,
    ← axisBody_eq_originSegment]
  exact mixedVolume_axis K

/-- The actual mixed volume with two marked segments and a body contained
in the coordinate hyperplane. The number `d` counts the repeated copies. -/
def hyperplanePair {d : ℕ} (K : ConvexBody E) (u v : ℝ × E) : ℝ :=
  mixedVolume volume (Fin.cons (centeredSegment u)
    (Fin.cons (centeredSegment v) (fun _ : Fin d => embedHyperplane K)))

theorem hyperplanePair_shear {d : ℕ} (K : ConvexBody E) (u v : ℝ × E) (a : E) :
    hyperplanePair (d := d) K (hyperplaneShear a u) (hyperplaneShear a v) =
      hyperplanePair (d := d) K u v := by
  have h := mixedVolume_map_measurePreserving volume volume (hyperplaneShear a)
    (hyperplaneShear_measurePreserving a)
    (Fin.cons (centeredSegment u)
      (Fin.cons (centeredSegment v) (fun _ : Fin d => embedHyperplane K)))
  unfold hyperplanePair
  convert h using 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero, ContinuousLinearEquiv.coe_coe] using
      (map_centeredSegment (hyperplaneShear a).toContinuousLinearMap u).symm
  · refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [Fin.cons_succ, Fin.cons_zero, ContinuousLinearEquiv.coe_coe] using
        (map_centeredSegment (hyperplaneShear a).toContinuousLinearMap v).symm
    · simpa only [Fin.cons_succ] using (shear_embedHyperplane a K).symm

theorem hyperplanePair_normal {d : ℕ} (K : ConvexBody E) (α β : ℝ) (b : E) :
    (d + 2 : ℝ) * hyperplanePair (d := d) K (α, 0) (β, b) =
      |α| * mixedVolume volume (Fin.cons (centeredSegment b) (fun _ : Fin d => K)) := by
  have he : (α, (0 : E)) = α • (1, (0 : E)) := by ext <;> simp
  rw [hyperplanePair, he, centeredSegment_abs_smul,
    mixedVolume_first_smul _ _ (abs_nonneg α)]
  rw [← mul_assoc, mul_comm (d + 2 : ℝ) |α|, mul_assoc,
    show (d + 2 : ℝ) = ((d + 1 : ℕ) + 1 : ℝ) by
      simp only [Nat.cast_add, Nat.cast_one]; ring,
    mixedVolume_centered_axis]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact map_centeredSegment _ _
  · exact project_embedHyperplane K

/-- The shear calculation when the first normal component is nonzero. -/
theorem hyperplanePair_formula_of_ne_zero {d : ℕ} (K : ConvexBody E)
    (α β : ℝ) (a b : E) (hα : α ≠ 0) :
    (d + 2 : ℝ) * hyperplanePair (d := d) K (α, a) (β, b) =
      mixedVolume volume
        (Fin.cons (centeredSegment (α • b - β • a)) (fun _ : Fin d => K)) := by
  have hu : hyperplaneShear (α⁻¹ • a) (α, a) = (α, 0) := by
    simp [hyperplaneShear, smul_smul, hα]
  have hv : hyperplaneShear (α⁻¹ • a) (β, b) = (β, b - (β / α) • a) := by
    simp [hyperplaneShear, smul_smul, div_eq_mul_inv]
  rw [← hyperplanePair_shear K (α, a) (β, b) (α⁻¹ • a), hu, hv,
    hyperplanePair_normal]
  have he : α • b - β • a = α • (b - (β / α) • a) := by
    rw [smul_sub, smul_smul]
    congr 1
    field_simp
  rw [he, centeredSegment_abs_smul, mixedVolume_first_smul _ _ (abs_nonneg α)]

/-- The formula extends continuously to zero normal components. This
includes bodies and marks of every dimension. -/
theorem hyperplanePair_formula {d : ℕ} (K : ConvexBody E)
    (α β : ℝ) (a b : E) :
    (d + 2 : ℝ) * hyperplanePair (d := d) K (α, a) (β, b) =
      mixedVolume volume
        (Fin.cons (centeredSegment (α • b - β • a)) (fun _ : Fin d => K)) := by
  let f : ℝ → ℝ := fun t => (d + 2 : ℝ) * hyperplanePair (d := d) K (t, a) (β, b)
  let g : ℝ → ℝ := fun t => mixedVolume volume
    (Fin.cons (centeredSegment (t • b - β • a)) (fun _ : Fin d => K))
  have hf : Continuous f := by
    apply Continuous.const_mul
    apply (continuous_mixedVolume volume (d + 1 + 1)).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_centeredSegment.comp (continuous_id.prodMk continuous_const)
    · exact continuous_const
  have hg : Continuous g := by
    apply (continuous_mixedVolume volume (d + 1)).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_centeredSegment.comp (by fun_prop)
    · exact continuous_const
  have he : f = g := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hf hg (by
    intro t ht
    exact hyperplanePair_formula_of_ne_zero K t β a b ht)
  exact congrFun he α

/-- Lemma 5.1 in a product frame, with the paper's exact normalization. -/
theorem hyperplanePair_eq_seminorm {d : ℕ} [Nontrivial E]
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 1) (u v : ℝ × E) :
    (d + 2 : ℝ) * (d + 1 : ℝ) * hyperplanePair (d := d) K u v =
      segmentMixedVolumeSeminorm volume (fun _ : Fin d => K) hdim
        (u.1 • v.2 - v.1 • u.2) := by
  rw [segmentMixedVolumeSeminorm_apply, ← hyperplanePair_formula K u.1 v.1 u.2 v.2]
  ring

end Measure
end RankThreeProjection
end
end
end DevelopmentSource23

/- Source module: Projection.CoordinateExtrusion. SHA256: 61558d2873d6ec1b542394f262c7f3e8f4f709ef358ad3bfa5cea7e74d35a394 -/
section DevelopmentSource24





@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

def splitFirst (n : ℕ) : Space (n + 1) ≃L[ℝ] (ℝ × Space n) where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv x := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases continuous_fst (fun j => ?_) i
    exact (continuous_apply j).comp continuous_snd

theorem splitFirst_measurePreserving (n : ℕ) :
    MeasurePreserving (splitFirst n) volume volume := by
  exact volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0

def tailCoordinates (n : ℕ) : Space (n + 1) →L[ℝ] Space n :=
  (ContinuousLinearMap.snd ℝ ℝ (Space n)).comp (splitFirst n).toContinuousLinearMap

@[simp] theorem tailCoordinates_apply (n : ℕ) (x : Space (n + 1)) (i : Fin n) :
    tailCoordinates n x i = x i.succ := rfl

@[simp] theorem splitFirst_basis_zero (n : ℕ) :
    splitFirst n (Pi.single 0 1) = (1, (0 : Space n)) := by
  ext i <;> simp [splitFirst]

@[simp] theorem tailCoordinates_basis_succ (n : ℕ) (j : Fin n) :
    tailCoordinates n (Pi.single j.succ 1) = Pi.single j 1 := by
  ext i
  simp [tailCoordinates_apply, Pi.single_apply, Fin.succ_inj]

/-- One coordinate deletion, with its exact mixed-volume normalization. -/
theorem mixedVolume_coordinate_head {n : ℕ} (K : Fin n → Body (n + 1)) :
    (n + 1 : ℝ) * mixedVolume volume
      (Fin.cons (centeredSegment (Pi.single 0 1)) K) =
      mixedVolume volume (fun i => mapBody (tailCoordinates n) (K i)) := by
  have h := mixedVolume_map_measurePreserving volume volume (splitFirst n)
    (splitFirst_measurePreserving n)
    (Fin.cons (centeredSegment (Pi.single 0 1)) K)
  have he : (fun i => mapBody (splitFirst n).toContinuousLinearMap
      ((Fin.cons (centeredSegment (Pi.single 0 1)) K :
        Fin (n + 1) → Body (n + 1)) i)) =
      Fin.cons (centeredSegment (1, (0 : Space n)))
        (fun i => mapBody (splitFirst n).toContinuousLinearMap (K i)) := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    simp only [Fin.cons_zero, map_centeredSegment]
    exact congrArg centeredSegment (splitFirst_basis_zero n)
  rw [← h, he, mixedVolume_centered_axis]
  congr 1
  funext i
  exact mapBody_comp _ _ _

/-- Delete the first `k` coordinates, keeping the last `d`. -/
def dropCoordinates (d k : ℕ) : Space (d + k) →L[ℝ] Space d :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj
    (⟨j.val + k, Nat.add_lt_add_right j.isLt k⟩ : Fin (d + k)))

@[simp] theorem dropCoordinates_apply (d k : ℕ) (x : Space (d + k)) (j : Fin d) :
    dropCoordinates d k x j = x ⟨j.val + k, Nat.add_lt_add_right j.isLt k⟩ := rfl

@[simp] theorem dropCoordinates_zero (d : ℕ) :
    dropCoordinates d 0 = ContinuousLinearMap.id ℝ (Space d) := by ext; rfl

theorem dropCoordinates_succ (d k : ℕ) :
    (dropCoordinates d k).comp (tailCoordinates (d + k)) = dropCoordinates d (k + 1) := by
  ext x j
  rfl

/-- Standard segments in the first `k` slots and copies of `K` elsewhere. -/
def coordinateTuple {d k : ℕ} (K : Body (d + k)) : Fin (d + k) → Body (d + k) :=
  fun i => if i.val < k then centeredSegment (Pi.single i 1) else K

theorem coordinateTuple_zero (d : ℕ) (K : Body d) :
    coordinateTuple (d := d) (k := 0) K = fun _ => K := by
  funext i
  simp [coordinateTuple]

theorem coordinateTuple_succ {d k : ℕ} (K : Body (d + (k + 1))) :
    coordinateTuple (d := d) (k := k + 1) K =
      Fin.cons (centeredSegment (Pi.single 0 1))
        (fun j : Fin (d + k) => coordinateTuple (d := d) (k := k + 1) K j.succ) := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  simp [coordinateTuple]

theorem coordinateTuple_tail {d k : ℕ} (K : Body (d + (k + 1))) :
    (fun j : Fin (d + k) => mapBody (tailCoordinates (d + k))
      (coordinateTuple (d := d) (k := k + 1) K j.succ)) =
      coordinateTuple (d := d) (k := k) (mapBody (tailCoordinates (d + k)) K) := by
  funext j
  by_cases hj : j.val < k
  · have hj' : j.succ.val < k + 1 := Nat.succ_lt_succ hj
    simp only [coordinateTuple, if_pos hj, if_pos hj',
      map_centeredSegment, tailCoordinates_basis_succ]
  · have hj' : ¬j.succ.val < k + 1 := fun h => hj (Nat.lt_of_succ_lt_succ h)
    simp only [coordinateTuple, if_neg hj, if_neg hj']

/-- Iterated actual interval extrusion. This includes zero-dimensional
projections and every lower-dimensional input body. -/
theorem coordinateTuple_factorial (d k : ℕ) (K : Body (d + k)) :
    ((d + k).factorial : ℝ) * mixedVolume volume (coordinateTuple (d := d) (k := k) K) =
      (d.factorial : ℝ) * volume.real
        ((mapBody (dropCoordinates d k) K : Body d) : Set (Space d)) := by
  induction k with
  | zero =>
      rw [coordinateTuple_zero, dropCoordinates_zero]
      have hm : mapBody (ContinuousLinearMap.id ℝ (Space d)) K = K := by
        apply ConvexBody.ext
        exact Set.image_id _
      rw [hm, mixedVolume_diagonal volume (by simp [Space])]
      simp only [Nat.add_zero]
  | succ k ih =>
      have hex : (d + k + 1 : ℝ) *
          mixedVolume volume (coordinateTuple (d := d) (k := k + 1) K) =
          mixedVolume volume (coordinateTuple (d := d) (k := k)
            (mapBody (tailCoordinates (d + k)) K)) := by
        rw [coordinateTuple_succ]
        simpa only [Nat.cast_add, Nat.cast_one, coordinateTuple_tail] using
          mixedVolume_coordinate_head
            (fun j : Fin (d + k) => coordinateTuple (d := d) (k := k + 1) K j.succ)
      calc
        _ = ((d + k).factorial : ℝ) * ((d + k + 1 : ℝ) *
            mixedVolume volume (coordinateTuple (d := d) (k := k + 1) K)) := by
              have hf : ((d + (k + 1)).factorial : ℝ) =
                  ((d + k).factorial : ℝ) * (d + k + 1 : ℝ) := by
                rw [Nat.add_succ, Nat.factorial_succ]
                push_cast
                ring
              rw [hf, mul_assoc]
        _ = ((d + k).factorial : ℝ) * mixedVolume volume
            (coordinateTuple (d := d) (k := k) (mapBody (tailCoordinates (d + k)) K)) := by rw [hex]
        _ = (d.factorial : ℝ) * volume.real
            ((mapBody (dropCoordinates d k) (mapBody (tailCoordinates (d + k)) K) : Body d) :
              Set (Space d)) := ih _
        _ = _ := by rw [mapBody_comp, dropCoordinates_succ]

theorem coordinateTuple_extrusion (d k : ℕ) (K : Body (d + k)) :
    ((d + k).factorial : ℝ) / (d.factorial : ℝ) *
        mixedVolume volume (coordinateTuple (d := d) (k := k) K) =
      volume.real ((mapBody (dropCoordinates d k) K : Body d) : Set (Space d)) := by
  have h := coordinateTuple_factorial d k K
  have hd : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [div_mul_eq_mul_div₀, div_eq_iff hd]
  exact h.trans (mul_comm _ _)

end RankThreeProjection
end
end
end DevelopmentSource24

/- Source module: Projection.CoordinateIdentity. SHA256: 6e186ca1b090f3b4421fae3140b352bf0af820885fc7121b72ba2bb8faa6b5c9 -/
section DevelopmentSource25






@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

section Relabel
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A coordinate permutation or relabeling, with the ordinary product measure. -/
def relabelCoordinates (e : ι ≃ κ) : (ι → ℝ) ≃L[ℝ] (κ → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => ℝ) e

@[simp] theorem relabelCoordinates_apply (e : ι ≃ κ) (x : ι → ℝ) (j : κ) :
    relabelCoordinates e x j = x (e.symm j) := by
  change Equiv.piCongrLeft (fun _ : κ => ℝ) e x j = x (e.symm j)
  simpa only [Equiv.apply_symm_apply] using
    (Equiv.piCongrLeft_apply_apply (P := fun _ : κ => ℝ) (e := e) x (e.symm j))

@[simp] theorem relabelCoordinates_symm_apply (e : ι ≃ κ) (x : κ → ℝ) (j : ι) :
    (relabelCoordinates e).symm x j = x (e j) := rfl

theorem relabelCoordinates_measurePreserving (e : ι ≃ κ) :
    MeasurePreserving (relabelCoordinates e) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : κ => ℝ) e

theorem relabelCoordinates_basis (e : ι ≃ κ) (i : ι) :
    relabelCoordinates e (Pi.single i 1) = Pi.single (e i) 1 := by
  ext j
  by_cases hj : j = e i
  · subst j
    simp
  · have he : e.symm j ≠ i := by
      intro h
      exact hj ((e.apply_symm_apply j).symm.trans (congrArg e h))
    simp [Pi.single_apply, hj, Ne.symm hj, he, Ne.symm he]

end Relabel

def retainedCoordinateEquiv {n k : ℕ} (I : Deleted n k) :
    Fin (n - k) ≃ Retained I.val :=
  Fintype.equivOfCardEq (by
    simp only [Retained, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_fin, I.property])

/-- Deleted coordinates are placed first, in their increasing order; retained
coordinates are placed last. The choice of order on the retained coordinates
does not change their Lebesgue volume. -/
def deletedCoordinateEquiv {n k : ℕ} (I : Deleted n k) : Fin (n - k + k) ≃ Fin n :=
  (((finCongr (Nat.add_comm (n - k) k)).trans finSumFinEquiv.symm).trans
    (Equiv.sumCongr (I.val.orderIsoOfFin I.property).toEquiv (retainedCoordinateEquiv I))).trans
      (Equiv.sumCompl (fun i : Fin n => i ∈ I.val))

def headIndex (d : ℕ) {k : ℕ} (i : Fin k) : Fin (d + k) :=
  (finCongr (Nat.add_comm d k)).symm (Fin.castAdd d i)

def tailIndex (k : ℕ) {d : ℕ} (i : Fin d) : Fin (d + k) :=
  ⟨i.val + k, Nat.add_lt_add_right i.isLt k⟩

@[simp] theorem headIndex_val (d : ℕ) {k : ℕ} (i : Fin k) :
    (headIndex d i).val = i.val := rfl

@[simp] theorem tailIndex_val (k : ℕ) {d : ℕ} (i : Fin d) :
    (tailIndex k i).val = i.val + k := rfl

@[simp] theorem deletedCoordinateEquiv_head {n k : ℕ} (I : Deleted n k) (i : Fin k) :
    deletedCoordinateEquiv I (headIndex (n - k) i) = I.val.orderEmbOfFin I.property i := by
  simp [deletedCoordinateEquiv, headIndex, Finset.coe_orderIsoOfFin_apply]

@[simp] theorem deletedCoordinateEquiv_tail {n k : ℕ} (I : Deleted n k) (i : Fin (n - k)) :
    deletedCoordinateEquiv I (tailIndex k i) = (retainedCoordinateEquiv I i).val := by
  have hi : tailIndex k i =
      (finCongr (Nat.add_comm (n - k) k)).symm (Fin.natAdd k i) := by
    apply Fin.ext
    exact Nat.add_comm _ _
  simp [hi, deletedCoordinateEquiv]

/-- Rotate the argument list from body-first to segment-first order. -/
def rotateMarkedIndices (d k : ℕ) : Equiv.Perm (Fin (d + k)) :=
  finAddFlip.trans (finCongr (Nat.add_comm k d))

@[simp] theorem rotateMarkedIndices_body (d k : ℕ) (i : Fin d) :
    rotateMarkedIndices d k (Fin.castAdd k i) = tailIndex k i := by
  simp only [rotateMarkedIndices, Equiv.trans_apply, finAddFlip_apply_castAdd]
  apply Fin.ext
  exact Nat.add_comm _ _

@[simp] theorem rotateMarkedIndices_segment (d k : ℕ) (i : Fin k) :
    rotateMarkedIndices d k (Fin.natAdd d i) = headIndex d i := by
  simp only [rotateMarkedIndices, Equiv.trans_apply, finAddFlip_apply_natAdd]
  rfl

theorem map_relabel_inverse_body {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (K : ConvexBody (κ → ℝ)) :
    mapBody (relabelCoordinates e).toContinuousLinearMap
      (mapBody (relabelCoordinates e).symm.toContinuousLinearMap K) = K := by
  rw [mapBody_comp]
  apply ConvexBody.ext
  change (fun x => relabelCoordinates e ((relabelCoordinates e).symm x)) '' (K : Set _) = _
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact Set.image_id _

theorem mapped_coordinateTuple_eq_markedTuple {n k : ℕ} (I : Deleted n k) (K : Body n) :
    (fun i => mapBody (relabelCoordinates (deletedCoordinateEquiv I)).toContinuousLinearMap
      (coordinateTuple (d := n - k) (k := k)
        (mapBody (relabelCoordinates (deletedCoordinateEquiv I)).symm.toContinuousLinearMap K)
        (rotateMarkedIndices (n - k) k i))) =
      markedTuple K (fun j => Pi.single j 1) I := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [rotateMarkedIndices_body, coordinateTuple, tailIndex_val,
      show ¬j.val + k < k by omega, if_false, map_relabel_inverse_body,
      markedTuple, Fin.append_left]
  · intro j
    simp only [rotateMarkedIndices_segment, coordinateTuple, headIndex_val,
      j.isLt, if_true, map_centeredSegment, ContinuousLinearEquiv.coe_coe,
      relabelCoordinates_basis,
      deletedCoordinateEquiv_head, markedTuple, Fin.append_right]

theorem markedTuple_eq_coordinateTuple_volume {n k : ℕ} (I : Deleted n k) (K : Body n) :
    mixedVolume volume (markedTuple K (fun j => Pi.single j 1) I) =
      mixedVolume volume (coordinateTuple (d := n - k) (k := k)
        (mapBody (relabelCoordinates (deletedCoordinateEquiv I)).symm.toContinuousLinearMap K)) := by
  rw [← mapped_coordinateTuple_eq_markedTuple]
  rw [mixedVolume_map_measurePreserving volume volume
    (relabelCoordinates (deletedCoordinateEquiv I))
    (relabelCoordinates_measurePreserving (deletedCoordinateEquiv I))]
  exact mixedVolume_reindex volume _ (rotateMarkedIndices (n - k) k)

theorem projectedBody_relabel_drop {n k : ℕ} (I : Deleted n k) (K : Body n) :
    mapBody (relabelCoordinates (retainedCoordinateEquiv I)).toContinuousLinearMap
      (mapBody (dropCoordinates (n - k) k)
        (mapBody (relabelCoordinates (deletedCoordinateEquiv I)).symm.toContinuousLinearMap K)) =
      projectedBody I.val K := by
  rw [mapBody_comp, mapBody_comp]
  congr 1
  ext x j
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    relabelCoordinates_apply, relabelCoordinates_symm_apply, dropCoordinates_apply,
    deleteCoordinates_apply]
  change x (deletedCoordinateEquiv I (tailIndex k ((retainedCoordinateEquiv I).symm j))) = x j.val
  rw [deletedCoordinateEquiv_tail, Equiv.apply_symm_apply]

/-- The actual coordinate projection volume is exactly the marked
mixed-volume coefficient with standard basis marks. -/
theorem coordinateVolume_eq_standardMarked {n k : ℕ} (I : Deleted n k) (K : Body n) :
    coordinateVolume I.val K = allMarkedArray K (fun i => Pi.single i 1) I := by
  have hkn : k ≤ n := by
    have h := I.val.card_le_univ
    simpa only [I.property, Fintype.card_fin] using h
  let K' : Body (n - k + k) :=
    mapBody (relabelCoordinates (deletedCoordinateEquiv I)).symm.toContinuousLinearMap K
  have hvol : coordinateVolume I.val K =
      volume.real ((mapBody (dropCoordinates (n - k) k) K' : Body (n - k)) :
        Set (Space (n - k))) := by
    rw [coordinateVolume, ← projectedBody_relabel_drop I K]
    change volume.real ((relabelCoordinates (retainedCoordinateEquiv I)) ''
      ((mapBody (dropCoordinates (n - k) k) K' : Body (n - k)) : Set (Space (n - k)))) = _
    exact measureReal_image_measurePreserving volume volume
      (relabelCoordinates (retainedCoordinateEquiv I))
      (relabelCoordinates_measurePreserving (retainedCoordinateEquiv I)) _
  rw [hvol, allMarkedArray, markedTuple_eq_coordinateTuple_volume]
  simpa only [Nat.sub_add_cancel hkn] using
    (coordinateTuple_extrusion (n - k) k K').symm

/-- Statement-level identification required in Theorem 3.1. Both sides are
defined independently from actual bodies, projections, and mixed volume. -/
theorem allProjectionArray_eq_standardMarked {n k : ℕ} (K : Body n) :
    allProjectionArray (k := k) K = allMarkedArray K (fun i => Pi.single i 1) := by
  funext I
  exact coordinateVolume_eq_standardMarked I K

end RankThreeProjection
end
end
end DevelopmentSource25

/- Source module: Projection.Normalization.Theorem31. SHA256: e9fc67d010b3b5ad8d7f248dae04d89be681a1ea9a17aa64fc43087f235d0985 -/
section DevelopmentSource26




/-!
# Theorem 3.1: coordinate projection compactification

`allProjectionLocus n k` is the range of literal coordinate deletion followed
by ordinary Lebesgue volume in the retained coordinates. `allMarkedArray`
is independently defined using the actual mixed-volume coefficient and the
centered segments `[-U_i/2,U_i/2]`. The coordinate extrusion theorem identifies
these two constructions for standard basis marks.

The two results below give both assertions of Theorem 3.1, for every
`1 ≤ k < n`, with no restriction on the marked vectors and no interior
assumption on the representing body.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace RankThreeProjection

theorem allProjectionLocus_eq_basisMarkedLocus (n k : ℕ) :
    allProjectionLocus n k = basisMarkedLocus n k := by
  unfold allProjectionLocus basisMarkedLocus
  congr 1
  funext K
  exact allProjectionArray_eq_standardMarked K

/-- **Theorem 3.1, closure formula.** Every parameter and every actual mixed
volume in the paper's statement is retained. -/
theorem theorem31 {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (P : Deleted n k → ℝ) :
    P ∈ closure (allProjectionLocus n k) ↔
      ∃ (K : Body n) (U : Fin n → Space n), allMarkedArray K U = P := by
  rw [allProjectionLocus_eq_basisMarkedLocus,
    closure_basisMarkedLocus_eq_markedArrayLocus hk hkn]
  constructor
  · rintro ⟨⟨K, U⟩, hKU⟩
    exact ⟨K, U, hKU⟩
  · rintro ⟨K, U, hKU⟩
    exact ⟨(K, U), hKU⟩

/-- **Theorem 3.1, dimension conclusion.** The same closure formula admits a
representation retaining at least `n-k+1` actual affine dimensions. -/
theorem theorem31_with_dimension {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (allProjectionLocus n k) ↔
      ∃ (K : Body n) (U : Fin n → Space n),
        n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  rw [allProjectionLocus_eq_basisMarkedLocus]
  exact basis_marked_compactification hk hkn P

/-- Every marked tuple, including degenerate marks and lower-dimensional
initial bodies, has a representation with the dimension stated in Theorem 3.1. -/
theorem theorem31_renormalize_dimension {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (K : Body n) (U : Fin n → Space n) :
    ∃ (L : Body n) (V : Fin n → Space n),
      n - k + 1 ≤ bodyDimension L ∧ allMarkedArray (k := k) L V = allMarkedArray K U :=
  marked_representation_with_dimension hk hkn.le ⟨(K, U), rfl⟩

end RankThreeProjection
end
end
end DevelopmentSource26

/- Source module: VolumeVerification.CircleFactorization. SHA256: 17c9f483faa98e2aaae9a6654545b52699a5b05ca92b768e83db26de6cde3d0a -/
section DevelopmentSource27













@[expose] public section
set_option autoImplicit false

/-!
# Positive hollow matrices of rank three
A nonprincipal four-by-four determinant identity gives an explicit Lorentz
factorization.  Positivity selects one sheet of the null cone, which can then
be normalized to the unit circle.  The angles are actual complex arguments.
-/
namespace VolumeVerification.CircleFactorization
open scoped Matrix BigOperators

private theorem bordered_det
    (a b c u v w u' v' w' p : ℝ) :
    Matrix.det !![0, a, b, u';
                 a, 0, c, v';
                 b, c, 0, w';
                 u, v, w, p] =
      2*a*b*c*p -
      (-c^2*u*u' - b^2*v*v' - a^2*w*w' +
        b*c*(u*v' + v*u') + a*c*(u*w' + w*u') + a*b*(v*w' + w*v')) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  ring

private theorem lorentz_identity
    (a b c r u v w u' v' w' : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hr : r ≠ 0) (hrsq : a*r^2 = 2*b*c) :
    ((u + 2*v/a)/2) * ((u' + 2*v'/a)/2) -
      ((2*v/a - u)/2) * ((2*v'/a - u')/2) -
      ((c*u + b*v - a*w)/(a*r)) * ((c*u' + b*v' - a*w')/(a*r)) =
      (-c^2*u*u' - b^2*v*v' - a^2*w*w' +
        b*c*(u*v' + v*u') + a*c*(u*w' + w*u') + a*b*(v*w' + w*v')) /
        (2*a*b*c) := by
  have hd : (a*r)*(a*r) = 2*a*b*c := by
    calc
      (a*r)*(a*r) = a*(a*r^2) := by ring
      _ = 2*a*b*c := by rw [hrsq]; ring
  have hy :
      ((c*u + b*v - a*w)/(a*r)) * ((c*u' + b*v' - a*w')/(a*r)) =
        ((c*u + b*v - a*w)*(c*u' + b*v' - a*w'))/(2*a*b*c) := by
    rw [div_mul_div_comm, hd]
  rw [hy]
  field_simp [ha, hb, hc]
  ring

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem four_minor_zero (P : Matrix ι ι ℝ) (hrank : P.rank ≤ 3)
    (rows cols : Fin 4 → ι) :
    (P.submatrix rows cols).det = 0 := by
  by_contra hdet
  have hr := Matrix.rank_of_det_ne_zero hdet
  have hle := Matrix.rank_submatrix_le P rows cols
  norm_num only [Fintype.card_fin] at hr
  omega

theorem schur_formula (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hrank : P.rank ≤ 3) (i₀ i₁ i₂ i j : ι) :
    2 * P i₀ i₁ * P i₀ i₂ * P i₁ i₂ * P i j =
      -(P i₁ i₂)^2 * P i₀ i * P i₀ j -
        (P i₀ i₂)^2 * P i₁ i * P i₁ j -
        (P i₀ i₁)^2 * P i₂ i * P i₂ j +
        P i₀ i₂ * P i₁ i₂ * (P i₀ i * P i₁ j + P i₁ i * P i₀ j) +
        P i₀ i₁ * P i₁ i₂ * (P i₀ i * P i₂ j + P i₂ i * P i₀ j) +
        P i₀ i₁ * P i₀ i₂ * (P i₁ i * P i₂ j + P i₂ i * P i₁ j) := by
  have hz := four_minor_zero P hrank ![i₀,i₁,i₂,i] ![i₀,i₁,i₂,j]
  have he :
      P.submatrix ![i₀,i₁,i₂,i] ![i₀,i₁,i₂,j] =
        !![0, P i₀ i₁, P i₀ i₂, P i₀ j;
           P i₀ i₁, 0, P i₁ i₂, P i₁ j;
           P i₀ i₂, P i₁ i₂, 0, P i₂ j;
           P i₀ i, P i₁ i, P i₂ i, P i j] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.submatrix, hdiag, hsym i₁ i₀, hsym i₂ i₀,
        hsym i₂ i₁, hsym i i₀, hsym i i₁, hsym i i₂]
  rw [he, bordered_det] at hz
  linarith

/-- An explicit future-null-cone factorization, before choosing circle angles. -/
theorem exists_normalized_lorentz_factorization (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank ≤ 3)
    (i₀ i₁ i₂ : ι) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    ∃ t x y : ι → ℝ,
      (∀ i, 0 < t i) ∧
      (∀ i, x i ^ 2 + y i ^ 2 = t i ^ 2) ∧
      (∀ i j, P i j = t i * t j - x i * x j - y i * y j) ∧
      t i₀ = 1 ∧ x i₀ = 1 ∧ y i₀ = 0 := by
  let a := P i₀ i₁
  let b := P i₀ i₂
  let c := P i₁ i₂
  have ha : 0 < a := hpos _ _ h01
  have hb : 0 < b := hpos _ _ h02
  have hc : 0 < c := hpos _ _ h12
  let r := Real.sqrt (2*b*c/a)
  have hinside : 0 < 2*b*c/a := by positivity
  have hr : 0 < r := Real.sqrt_pos.mpr hinside
  have hrsq : a*r^2 = 2*b*c := by
    have hsq : r^2 = 2*b*c/a := Real.sq_sqrt hinside.le
    rw [hsq]
    field_simp [ha.ne']
  let t : ι → ℝ := fun i => (P i₀ i + 2*P i₁ i/a)/2
  let x : ι → ℝ := fun i => (2*P i₁ i/a - P i₀ i)/2
  let y : ι → ℝ := fun i => (c*P i₀ i + b*P i₁ i - a*P i₂ i)/(a*r)
  have hnonneg : ∀ i j, 0 ≤ P i j := by
    intro i j
    by_cases hij : i = j
    · subst j; rw [hdiag]
    · exact (hpos i j hij).le
  have ht : ∀ i, 0 < t i := by
    intro i
    by_cases hi : i = i₀
    · subst i
      have hval : t i₀ = 1 := by
        dsimp [t]
        rw [hdiag, hsym i₁ i₀]
        change (0 + 2*a/a)/2 = 1
        field_simp [ha.ne']
        ring
      rw [hval]
      norm_num
    · have hui : 0 < P i₀ i := hpos _ _ (Ne.symm hi)
      have hvi : 0 ≤ P i₁ i := hnonneg _ _
      dsimp [t]
      positivity
  have hfactor : ∀ i j, P i j = t i*t j - x i*x j - y i*y j := by
    intro i j
    have hs := schur_formula P hsym hdiag hrank i₀ i₁ i₂ i j
    have hl := lorentz_identity a b c r
      (P i₀ i) (P i₁ i) (P i₂ i) (P i₀ j) (P i₁ j) (P i₂ j)
      ha.ne' hb.ne' hc.ne' hr.ne' hrsq
    change P i j = ((P i₀ i + 2*P i₁ i/a)/2) *
        ((P i₀ j + 2*P i₁ j/a)/2) -
      ((2*P i₁ i/a - P i₀ i)/2) * ((2*P i₁ j/a - P i₀ j)/2) -
      ((c*P i₀ i + b*P i₁ i - a*P i₂ i)/(a*r)) *
        ((c*P i₀ j + b*P i₁ j - a*P i₂ j)/(a*r))
    rw [hl]
    apply (eq_div_iff (by positivity : 2*a*b*c ≠ 0)).mpr
    dsimp [a,b,c]
    nlinarith [hs]
  refine ⟨t,x,y,ht,?_,hfactor,?_,?_,?_⟩
  · intro i
    have hi := hfactor i i
    rw [hdiag] at hi
    nlinarith
  · dsimp [t]
    rw [hdiag, hsym i₁ i₀]
    change (0 + 2*a/a)/2 = 1
    field_simp [ha.ne']
    ring
  · dsimp [x]
    rw [hdiag, hsym i₁ i₀]
    change (2*a/a - 0)/2 = 1
    field_simp [ha.ne']
    ring
  · dsimp [y]
    rw [hdiag, hsym i₁ i₀, hsym i₂ i₀]
    change (c*0 + b*a - a*b)/(a*r) = 0
    ring

/-- The Lorentz factorization without fixing the distinguished point. -/
theorem exists_lorentz_factorization (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank ≤ 3)
    (i₀ i₁ i₂ : ι) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    ∃ t x y : ι → ℝ,
      (∀ i, 0 < t i) ∧
      (∀ i, x i ^ 2 + y i ^ 2 = t i ^ 2) ∧
      (∀ i j, P i j = t i * t j - x i * x j - y i * y j) := by
  obtain ⟨t,x,y,ht,hn,hP,_,_,_⟩ :=
    exists_normalized_lorentz_factorization P hsym hdiag hpos hrank
      i₀ i₁ i₂ h01 h02 h12
  exact ⟨t,x,y,ht,hn,hP⟩

/-- A fully quantified circle factorization with distinct principal arguments. -/
theorem exists_circle_factorization (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank ≤ 3)
    (i₀ i₁ i₂ : ι) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    ∃ a θ : ι → ℝ, (∀ i, 0 < a i) ∧ Function.Injective θ ∧
      (∀ i, θ i ∈ Set.Ioc (-Real.pi) Real.pi) ∧
      ∀ i j, P i j = a i*a j*(1 - Real.cos (θ i - θ j)) := by
  obtain ⟨a,x,y,ha,hnull,hfactor⟩ :=
    exists_lorentz_factorization P hsym hdiag hpos hrank i₀ i₁ i₂ h01 h02 h12
  let z : ι → ℂ := fun i => ⟨x i/a i,y i/a i⟩
  have hunit : ∀ i, (x i/a i)^2 + (y i/a i)^2 = 1 := by
    intro i
    field_simp [(ha i).ne']
    exact hnull i
  have hnorm : ∀ i, ‖z i‖ = 1 := by
    intro i
    rw [Complex.norm_def]
    change Real.sqrt ((x i/a i)*(x i/a i) + (y i/a i)*(y i/a i)) = 1
    rw [← sq, ← sq, hunit i]
    norm_num
  have hz : ∀ i, z i ≠ 0 := by
    intro i h
    have hi := hnorm i
    rw [h, norm_zero] at hi
    norm_num at hi
  let θ : ι → ℝ := fun i => Complex.arg (z i)
  have hcos : ∀ i, Real.cos (θ i) = x i/a i := by
    intro i
    simpa [θ, hnorm i, z] using Complex.cos_arg (hz i)
  have hsin : ∀ i, Real.sin (θ i) = y i/a i := by
    intro i
    simpa [θ, hnorm i, z] using Complex.sin_arg (z i)
  have hP : ∀ i j, P i j = a i*a j*(1 - Real.cos (θ i - θ j)) := by
    intro i j
    rw [Real.cos_sub, hcos, hcos, hsin, hsin, hfactor]
    field_simp [(ha i).ne', (ha j).ne']
    ring
  refine ⟨a,θ,ha,?_,fun i => Complex.arg_mem_Ioc (z i),hP⟩
  intro i j hij
  by_contra hne
  have hp := hpos i j hne
  rw [hP i j, hij, sub_self, Real.cos_zero] at hp
  norm_num at hp

end
end VolumeVerification.CircleFactorization

end
end DevelopmentSource27

/- Source module: VolumeVerification.MatrixInertia. SHA256: 96fa2502740fa655bbdbd5f5ede825d2d1335e90dc815be68ecb7120a19dac57 -/
section DevelopmentSource28




@[expose] public section
set_option autoImplicit false

/-!
# Inertia and strict perturbations of positive hollow rank-three matrices

Inertia is stated using Mathlib's maximal dimensions of positive and negative
definite subspaces.  Sylvester's law of inertia in Mathlib identifies these
dimensions with the usual signs in a diagonalization.
-/
namespace VolumeVerification.MatrixInertia
open scoped BigOperators Matrix
open QuadraticMap

section General
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem one_le_sigPos_of_pos (Q : QuadraticForm ℝ E)
    {v : E} (hv : 0 < Q v) : 1 ≤ sigPos Q := by
  have hv0 : v ≠ 0 := by
    intro h
    simpa [h] using hv
  have hline : (Q.restrict (ℝ ∙ v)).PosDef := by
    intro x hx
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp x.property
    have hr0 : r ≠ 0 := by
      intro h
      apply hx
      apply Subtype.ext
      simpa [h] using hr.symm
    change 0 < Q x.val
    rw [← hr, QuadraticMap.map_smul]
    exact mul_pos (mul_self_pos.mpr hr0) hv
  have hb := le_sigPos_of_posDef Q hline
  rwa [finrank_span_singleton hv0] at hb

theorem sigPos_eq_one_of_nonpos_kernel (Q : QuadraticForm ℝ E)
    (l : E →ₗ[ℝ] ℝ) (hnonpos : ∀ x ∈ l.ker, Q x ≤ 0)
    (hpositive : ∃ x, 0 < Q x) : sigPos Q = 1 := by
  have hu := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := Q) (V := l.ker) hnonpos
  have hr := l.finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ l.range ≤ 1 := by
    simpa using l.range.finrank_le
  obtain ⟨x,hx⟩ := hpositive
  have hl := one_le_sigPos_of_pos Q hx
  omega

theorem strict_signature_of_negative_kernel (Q : QuadraticForm ℝ E)
    (l : E →ₗ[ℝ] ℝ) (hnegative : ∀ x ∈ l.ker, x ≠ 0 → Q x < 0)
    (hpositive : ∃ x, 0 < Q x) :
    sigPos Q = 1 ∧
      sigNeg Q = Module.finrank ℝ E - 1 ∧
      Module.finrank ℝ Q.radical = 0 := by
  have hp : sigPos Q = 1 := sigPos_eq_one_of_nonpos_kernel Q l
    (by
      intro x hx
      by_cases hzero : x = 0
      · simp [hzero]
      · exact (hnegative x hx hzero).le) hpositive
  have hneg : ((-Q).restrict l.ker).PosDef := by
    intro x hx
    have hx0 : x.val ≠ 0 := by simpa using hx
    change 0 < -Q x.val
    exact neg_pos.mpr (hnegative x.val x.property hx0)
  have hn := le_sigNeg_of_negDef Q hneg
  have hd := l.finrank_range_add_finrank_ker
  have hr : Module.finrank ℝ l.range ≤ 1 := by
    simpa using l.range.finrank_le
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  omega
end General

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dotLinear (a : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun x => ∑ i, a i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem quadratic_apply (P : Matrix ι ι ℝ) (u : ι → ℝ) :
    P.toQuadraticForm' u = ∑ i, ∑ j, u i * u j * P i j := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem bilinear_symmetric (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (u v : ι → ℝ) :
    Matrix.toLinearMap₂' ℝ P u v = Matrix.toLinearMap₂' ℝ P v u := by
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hsym i j]
  ring

theorem radical_eq_kernel (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) :
    P.toQuadraticForm'.radical = P.mulVecLin.ker := by
  have ha : QuadraticMap.associated P.toQuadraticForm' =
      Matrix.toLinearMap₂' ℝ P :=
    QuadraticMap.associated_left_inverse ℝ (bilinear_symmetric P hsym)
  rw [QuadraticMap.radical_eq_ker_associated, ha]
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    ext i
    have hi := LinearMap.congr_fun hx (Pi.single i 1)
    rw [bilinear_symmetric P hsym] at hi
    simpa [Matrix.toLinearMap₂'_apply'] using hi
  · intro hx
    apply LinearMap.ext
    intro y
    change Matrix.toLinearMap₂' ℝ P x y = 0
    rw [bilinear_symmetric P hsym, Matrix.toLinearMap₂'_apply']
    change y ⬝ᵥ (P.mulVecLin x) = 0
    rw [hx]
    simp

theorem rank_add_radical (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) :
    P.rank + Module.finrank ℝ P.toQuadraticForm'.radical = Fintype.card ι := by
  rw [radical_eq_kernel P hsym]
  simpa [Matrix.rank] using P.mulVecLin.finrank_range_add_finrank_ker

private theorem double_sum_product (a b u v : ι → ℝ) :
    (∑ i, ∑ j, u i * v j * (a i*b j)) = dotLinear a u * dotLinear b v := by
  simp only [dotLinear, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_lorentz (P : Matrix ι ι ℝ) (a b c : ι → ℝ)
    (hP : ∀ i j, P i j = a i*a j - b i*b j - c i*c j) (u : ι → ℝ) :
    P.toQuadraticForm' u =
      (dotLinear a u)^2 - (dotLinear b u)^2 - (dotLinear c u)^2 := by
  rw [quadratic_apply]
  simp_rw [hP, mul_sub, Finset.sum_sub_distrib]
  rw [double_sum_product, double_sum_product, double_sum_product]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem quadratic_pair (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0) (i j : ι) :
    P.toQuadraticForm' (Pi.single i 1 + Pi.single j 1) = 2 * P i j := by
  have hsingle (k l : ι) :
      Matrix.toLinearMap₂' ℝ P (Pi.single k (1 : ℝ)) (Pi.single l (1 : ℝ)) = P k l := by
    simp only [Matrix.toLinearMap₂'_apply', single_dotProduct,
      Matrix.mulVec_single_one, Matrix.col_apply, one_mul]
  have hsum : (P i i + P j i) + (P i j + P j j) = 2 * P i j := by
    rw [hdiag i, hdiag j, hsym j i]
    ring
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    map_add, LinearMap.add_apply]
  exact (congrArg₂ (fun x y : ℝ => x + y)
    (congrArg₂ (fun x y : ℝ => x + y) (hsingle i i) (hsingle j i))
    (congrArg₂ (fun x y : ℝ => x + y) (hsingle i j) (hsingle j j))).trans hsum

/-- The inertia assertion in Lemma 2.1, without replacing matrix rank by a hypothesis
on an unverified factorization. -/
theorem positive_hollow_rank_three_signature (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank = 3)
    (i₀ i₁ i₂ : ι) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    sigPos P.toQuadraticForm' = 1 ∧ sigNeg P.toQuadraticForm' = 2 ∧
      Module.finrank ℝ P.toQuadraticForm'.radical = Fintype.card ι - 3 := by
  obtain ⟨a,b,c,ha,hnull,hP⟩ :=
    CircleFactorization.exists_lorentz_factorization P hsym hdiag hpos
      hrank.le i₀ i₁ i₂ h01 h02 h12
  have hp : sigPos P.toQuadraticForm' = 1 :=
    sigPos_eq_one_of_nonpos_kernel _ (dotLinear a)
      (by
        intro u hu
        rw [LinearMap.mem_ker] at hu
        rw [quadratic_lorentz P a b c hP, hu]
        nlinarith [sq_nonneg (dotLinear b u), sq_nonneg (dotLinear c u)])
      ⟨Pi.single i₀ 1 + Pi.single i₁ 1, by
        rw [quadratic_pair P hsym hdiag]
        exact mul_pos (by norm_num) (hpos _ _ h01)⟩
  have hs := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := P.toQuadraticForm')
  have hr := rank_add_radical P hsym
  simp only [Module.finrank_fintype_fun_eq_card] at hs
  rw [hrank] at hr
  omega

/-- A hollow perturbation preserving all positive off-diagonal entries. -/
def strictPerturb (P : Matrix ι ι ℝ) (a : ι → ℝ) (ε : ℝ) : Matrix ι ι ℝ :=
  fun i j => P i j + ε * (a i*a j - if i = j then (a i)^2 else 0)

theorem strictPerturb_symmetric (P : Matrix ι ι ℝ) (a : ι → ℝ) (ε : ℝ)
    (hsym : ∀ i j, P i j = P j i) :
    ∀ i j, strictPerturb P a ε i j = strictPerturb P a ε j i := by
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp [strictPerturb, h, Ne.symm h, hsym i j, mul_comm]

theorem strictPerturb_hollow (P : Matrix ι ι ℝ) (a : ι → ℝ) (ε : ℝ)
    (hdiag : ∀ i, P i i = 0) :
    ∀ i, strictPerturb P a ε i i = 0 := by
  intro i
  simp [strictPerturb, hdiag, pow_two]

theorem strictPerturb_positive (P : Matrix ι ι ℝ) (a : ι → ℝ) (ε : ℝ)
    (ha : ∀ i, 0 < a i) (hε : 0 ≤ ε)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) :
    ∀ i j, i ≠ j → 0 < strictPerturb P a ε i j := by
  intro i j hij
  simp only [strictPerturb, if_neg hij, sub_zero]
  exact add_pos_of_pos_of_nonneg (hpos i j hij)
    (mul_nonneg hε (mul_pos (ha i) (ha j)).le)

theorem strictPerturb_quadratic (P : Matrix ι ι ℝ) (a b c : ι → ℝ)
    (hP : ∀ i j, P i j = a i*a j - b i*b j - c i*c j)
    (ε : ℝ) (u : ι → ℝ) :
    (strictPerturb P a ε).toQuadraticForm' u =
      (1+ε)*(dotLinear a u)^2 - (dotLinear b u)^2 - (dotLinear c u)^2 -
        ε * ∑ i, (a i)^2*(u i)^2 := by
  have hdiag :
      (∑ i, ∑ j, u i * u j * (if i = j then (a i)^2 else 0)) =
        ∑ i, (a i)^2*(u i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  have hsplit : (strictPerturb P a ε).toQuadraticForm' u =
      P.toQuadraticForm' u +
        ε * ((dotLinear a u)^2 - ∑ i, (a i)^2*(u i)^2) := by
    simp only [quadratic_apply, strictPerturb]
    simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have he1 :
        (∑ i, ∑ j, u i * u j * (ε * (a i*a j))) =
          ε * (∑ i, ∑ j, u i * u j * (a i*a j)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have he2 :
        (∑ i, ∑ j, u i * u j * (ε * (if i = j then (a i)^2 else 0))) =
          ε * (∑ i, ∑ j, u i * u j * (if i = j then (a i)^2 else 0)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he1, he2, double_sum_product, hdiag]
    ring
  rw [hsplit, quadratic_lorentz P a b c hP]
  ring

theorem strictPerturb_negative_kernel (P : Matrix ι ι ℝ) (a b c : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hP : ∀ i j, P i j = a i*a j - b i*b j - c i*c j)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ u ∈ (dotLinear a).ker, u ≠ 0 →
      (strictPerturb P a ε).toQuadraticForm' u < 0 := by
  intro u hu hu0
  rw [LinearMap.mem_ker] at hu
  have hsum : 0 < ∑ k, (a k)^2 * (u k)^2 := by
    apply Finset.sum_pos'
    · intro k _
      positivity
    · have hex : ∃ k, u k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hu0 (funext h)
      obtain ⟨k,hk⟩ := hex
      exact ⟨k, Finset.mem_univ k,
        mul_pos (sq_pos_of_pos (ha k)) (sq_pos_of_ne_zero hk)⟩
  rw [strictPerturb_quadratic P a b c hP, hu]
  have hs1 := sq_nonneg (dotLinear b u)
  have hs2 := sq_nonneg (dotLinear c u)
  nlinarith [mul_pos hε hsum]

theorem strictPerturb_signature (P : Matrix ι ι ℝ) (a b c : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hP : ∀ i j, P i j = a i*a j - b i*b j - c i*c j)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (i j : ι) (hij : i ≠ j) (ε : ℝ) (hε : 0 < ε) :
    sigPos (strictPerturb P a ε).toQuadraticForm' = 1 ∧
      sigNeg (strictPerturb P a ε).toQuadraticForm' = Fintype.card ι - 1 ∧
      Module.finrank ℝ (strictPerturb P a ε).toQuadraticForm'.radical = 0 := by
  suffices h :
      sigPos (strictPerturb P a ε).toQuadraticForm' = 1 ∧
        sigNeg (strictPerturb P a ε).toQuadraticForm' =
          Module.finrank ℝ (ι → ℝ) - 1 ∧
        Module.finrank ℝ (strictPerturb P a ε).toQuadraticForm'.radical = 0 by
    simpa using h
  apply strict_signature_of_negative_kernel _ (dotLinear a)
  · intro u hu hu0
    rw [LinearMap.mem_ker] at hu
    have hsum : 0 < ∑ k, (a k)^2 * (u k)^2 := by
      apply Finset.sum_pos'
      · intro k _
        positivity
      · have hex : ∃ k, u k ≠ 0 := by
          by_contra h
          push_neg at h
          exact hu0 (funext h)
        obtain ⟨k,hk⟩ := hex
        exact ⟨k, Finset.mem_univ k, mul_pos (sq_pos_of_pos (ha k)) (sq_pos_of_ne_zero hk)⟩
    rw [strictPerturb_quadratic P a b c hP, hu]
    have hs1 := sq_nonneg (dotLinear b u)
    have hs2 := sq_nonneg (dotLinear c u)
    nlinarith [mul_pos hε hsum]
  · refine ⟨Pi.single i 1 + Pi.single j 1, ?_⟩
    rw [quadratic_pair _ (strictPerturb_symmetric P a ε hsym)
      (strictPerturb_hollow P a ε hdiag)]
    exact mul_pos (by norm_num) (strictPerturb_positive P a ε ha hε.le hpos i j hij)

theorem strictPerturb_tendsto (P : Matrix ι ι ℝ) (a : ι → ℝ) :
    Filter.Tendsto (strictPerturb P a) (nhds 0) (nhds P) := by
  have hc : Continuous (strictPerturb P a) := by
    unfold strictPerturb
    fun_prop
  have hzero : strictPerturb P a 0 = P := by
    ext i j
    simp only [strictPerturb, zero_mul, add_zero]
  simpa only [hzero] using hc.tendsto 0

end Matrix
end VolumeVerification.MatrixInertia

end
end DevelopmentSource28

/- Source module: Projection.StrictTopology. SHA256: 78741ee4db5aa50dbc06cb810dba24a0dff19cf621b1d46fb9a8394753147400 -/
section DevelopmentSource29








/-!
# Relative-open strict counterexample families

This file concerns finite-dimensional matrix topology only. Its exclusion
hypothesis is explicit: the geometric obstruction must supply it. The proof
uses compactness of a unit sphere in one fixed negative hyperplane.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Module Filter
open scoped BigOperators Matrix Topology

namespace RankThreeProjection
open VolumeVerification.MatrixInertia

/-- The ambient space specified in the open-set assertion of Theorem 1.1. -/
abbrev HollowSymmetricArray (n : ℕ) :=
  {P : Array n // (∀ i, P i i = 0) ∧ (∀ i j, P i j = P j i)}

/-- Actual quadratic-form inertia, including absence of a radical. -/
def StrictLorentzian {n : ℕ} (P : Array n) : Prop :=
  sigPos P.toQuadraticForm' = 1 ∧
  sigNeg P.toQuadraticForm' = n - 1 ∧
  finrank ℝ P.toQuadraticForm'.radical = 0

theorem continuous_matrix_quadratic {n : ℕ} :
    Continuous (fun z : Array n × Space n => z.1.toQuadraticForm' z.2) := by
  simp only [quadratic_apply]
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/-- Strict negativity on a fixed hyperplane is an open matrix condition. -/
theorem isOpen_negative_on_kernel {n : ℕ} (l : Space n →ₗ[ℝ] ℝ) :
    IsOpen {P : Array n | ∀ x ∈ l.ker, x ≠ 0 → P.toQuadraticForm' x < 0} := by
  let S := Metric.sphere (0 : l.ker) 1
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : l.ker) 1)
  let bad : Set (Array n × S) :=
    {z | 0 ≤ z.1.toQuadraticForm' z.2.val.val}
  have hb : IsClosed bad := by
    have hS : Continuous (fun x : S => (x.val : l.ker)) := continuous_subtype_val
    have hker : Continuous (fun x : l.ker => (x.val : Space n)) :=
      continuous_subtype_val
    have hpoint : Continuous (fun z : Array n × S => (z.2.val.val : Space n)) :=
      hker.comp (hS.comp continuous_snd)
    have hquad : Continuous
        (fun z : Array n × S => z.1.toQuadraticForm' (z.2.val.val : Space n)) := by
      simp only [quadratic_apply]
      refine continuous_finsetSum _ (fun i _ => ?_)
      refine continuous_finsetSum _ (fun j _ => ?_)
      exact (((continuous_apply i).comp hpoint).mul
        ((continuous_apply j).comp hpoint)).mul
          ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))
    exact isClosed_le continuous_const hquad
  have hopen : IsOpen (Prod.fst '' bad)ᶜ :=
    (isClosedMap_fst_of_compactSpace bad hb).isOpen_compl
  convert hopen using 1
  ext P
  constructor
  · intro hP hbad
    obtain ⟨⟨Q, x⟩, hx, he⟩ := hbad
    change Q = P at he
    subst Q
    have hnorm : ‖x.val‖ = 1 := by
      simpa only [S, Metric.mem_sphere, dist_zero_right] using x.property
    have hne : x.val.val ≠ 0 := by
      intro hzero
      have hx0 : x.val = 0 := Subtype.ext hzero
      rw [hx0, norm_zero] at hnorm
      norm_num at hnorm
    exact (not_le_of_gt (hP x.val.val x.val.property hne)) hx
  · intro hP x hx hne
    let y : l.ker := ⟨x, hx⟩
    have hy : y ≠ 0 := by
      intro he
      exact hne (congrArg Subtype.val he)
    let z : l.ker := ‖y‖⁻¹ • y
    have hz : z ∈ S := by
      simp only [S, z, Metric.mem_sphere, dist_zero_right]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
    have hq : P.toQuadraticForm' z.val < 0 := by
      by_contra h
      apply hP
      exact ⟨(P, ⟨z, hz⟩), le_of_not_gt h, rfl⟩
    have hscale : 0 < ‖y‖⁻¹ * ‖y‖⁻¹ :=
      mul_pos (inv_pos.mpr (norm_pos_iff.mpr hy))
        (inv_pos.mpr (norm_pos_iff.mpr hy))
    change P.toQuadraticForm' (‖y‖⁻¹ • x) < 0 at hq
    rw [QuadraticMap.map_smul] at hq
    exact (smul_neg_iff_of_pos_left hscale).mp hq

theorem isOpen_positive_off_diagonal (n : ℕ) :
    IsOpen {P : Array n | ∀ i j, i ≠ j → 0 < P i j} := by
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _hij
  exact isOpen_lt continuous_const
    ((continuous_apply j).comp (continuous_apply i))

/-- The negative hyperplane and exclusion persist on a relative-open
neighborhood consisting of positive hollow matrices of inertia (1,n-1,0). -/
theorem exists_open_strict_family_of_negative_kernel {n : ℕ} (hn : 2 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P)
    (houtside : P ∉ closedProjectionLocus n)
    (l : Space n →ₗ[ℝ] ℝ)
    (hnegative : ∀ x ∈ l.ker, x ≠ 0 → P.toQuadraticForm' x < 0) :
    ∃ V : Set (HollowSymmetricArray n),
      IsOpen V ∧ V.Nonempty ∧
      ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧
        StrictLorentzian Q.val ∧ Q.val ∉ closedProjectionLocus n := by
  let V : Set (HollowSymmetricArray n) :=
    {Q | (∀ x ∈ l.ker, x ≠ 0 → Q.val.toQuadraticForm' x < 0) ∧
      (∀ i j, i ≠ j → 0 < Q.val i j) ∧ Q.val ∉ closedProjectionLocus n}
  refine ⟨V, ?_, ?_, ?_⟩
  · exact ((isOpen_negative_on_kernel l).inter
      ((isOpen_positive_off_diagonal n).inter
        (isClosed_closedProjectionLocus n).isOpen_compl)).preimage
      continuous_subtype_val
  · exact ⟨⟨P, hP.1, hP.2.1⟩, hnegative, hP.2.2, houtside⟩
  · intro Q hQ
    refine ⟨⟨Q.property.1, Q.property.2, hQ.2.1⟩, ?_, hQ.2.2⟩
    have hpositive : ∃ x, 0 < Q.val.toQuadraticForm' x := by
      let i : Fin n := ⟨0, by omega⟩
      let j : Fin n := ⟨1, by omega⟩
      have hij : i ≠ j := by
        intro h
        have he := congrArg Fin.val h
        simp [i, j] at he
      refine ⟨Pi.single i 1 + Pi.single j 1, ?_⟩
      rw [quadratic_pair Q.val Q.property.2 Q.property.1 i j]
      exact mul_pos (by norm_num) (hQ.2.1 i j hij)
    simpa only [StrictLorentzian, Space, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using
      strict_signature_of_negative_kernel Q.val.toQuadraticForm' l hQ.1 hpositive

/-- Exclusion persists for all sufficiently small positive parameters. -/
theorem strict_perturbations_outside {n : ℕ} (P : Array n) (a : Fin n → ℝ)
    (houtside : P ∉ closedProjectionLocus n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      strictPerturb P a ε ∉ closedProjectionLocus n := by
  have he : ∀ᶠ ε : ℝ in 𝓝 0,
      strictPerturb P a ε ∉ closedProjectionLocus n :=
    (strictPerturb_tendsto P a).eventually
      ((isClosed_closedProjectionLocus n).isOpen_compl.mem_nhds houtside)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  apply hball
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
    abs_of_pos hε] using hεδ

/-- All perturbation and relative-openness conclusions follow from the exact
rank-three exclusion. That geometric exclusion is an explicit hypothesis. -/
theorem rank_three_strict_family {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3)
    (houtside : P ∉ closedProjectionLocus n) :
    ∃ a : Fin n → ℝ,
      (∀ i, 0 < a i) ∧
      Tendsto (strictPerturb P a) (𝓝 0) (𝓝 P) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        PositiveHollowSymmetric (strictPerturb P a ε) ∧
        StrictLorentzian (strictPerturb P a ε) ∧
        strictPerturb P a ε ∉ closedProjectionLocus n) ∧
      (∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
        ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
          Q.val ∉ closedProjectionLocus n) := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₂ : Fin n := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by intro h; have := congrArg Fin.val h; simp [i₀, i₁] at this
  have h02 : i₀ ≠ i₂ := by intro h; have := congrArg Fin.val h; simp [i₀, i₂] at this
  have h12 : i₁ ≠ i₂ := by intro h; have := congrArg Fin.val h; simp [i₁, i₂] at this
  obtain ⟨a,b,c,ha,_hnull,hfactor⟩ :=
    VolumeVerification.CircleFactorization.exists_lorentz_factorization
      P hP.2.1 hP.1 hP.2.2 hrank.le i₀ i₁ i₂ h01 h02 h12
  obtain ⟨δ, hδ, hout⟩ := strict_perturbations_outside P a houtside
  have hpert (ε : ℝ) (hε : 0 < ε) :
      PositiveHollowSymmetric (strictPerturb P a ε) :=
    ⟨strictPerturb_hollow P a ε hP.1,
      strictPerturb_symmetric P a ε hP.2.1,
      strictPerturb_positive P a ε ha hε.le hP.2.2⟩
  refine ⟨a, ha, strictPerturb_tendsto P a, ⟨δ, hδ, ?_⟩, ?_⟩
  · intro ε hε hεδ
    refine ⟨hpert ε hε, ?_, hout ε hε hεδ⟩
    simpa only [StrictLorentzian, Fintype.card_fin] using
      strictPerturb_signature P a b c ha hfactor hP.2.1 hP.1 hP.2.2 i₀ i₁ h01 ε hε
  · exact exists_open_strict_family_of_negative_kernel (by omega)
      (strictPerturb P a (δ / 2)) (hpert _ (by positivity))
      (hout _ (by positivity) (by linarith)) (dotLinear a)
      (strictPerturb_negative_kernel P a b c ha hfactor (δ / 2) (by positivity))

end RankThreeProjection

end
end
end DevelopmentSource29

/- Source module: Projection.CoordinateMeaning. SHA256: 7734f27907673421be52cac4736239d1b9c5bcb269a460db57fbea7d338ed0e6 -/
section DevelopmentSource30







/-!
# Euclidean meaning of the coordinate conventions

The coordinate model `Fin n → ℝ` carries the maximum norm and product
Lebesgue measure. Its coordinate bijection with Euclidean space preserves
Lebesgue measure exactly. Coordinate deletion commutes with that bijection,
so all projection volumes and their realization loci agree. The same map
preserves the actual mixed volume and affine dimension. Consequently the
compactification theorem also has the fully Euclidean formulation below.

No comparison of the different unit spheres is made in these statements.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise

namespace RankThreeProjection
open VolumePolynomials

abbrev EuclideanBody (n : ℕ) := ConvexBody (EuclideanSpace ℝ (Fin n))

/-- The identity on coordinates, with the Euclidean norm on the codomain. -/
def coordinateEuclideanEquiv (ι : Type*) [Fintype ι] :
    (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm

@[simp] theorem coordinateEuclideanEquiv_apply {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (i : ι) : coordinateEuclideanEquiv ι x i = x i := rfl

@[simp] theorem coordinateEuclideanEquiv_symm_apply {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) (i : ι) : (coordinateEuclideanEquiv ι).symm x i = x i := rfl

theorem coordinateEuclideanEquiv_measurePreserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (coordinateEuclideanEquiv ι) volume volume :=
  PiLp.volume_preserving_toLp ι

theorem coordinateEuclideanEquiv_symm_measurePreserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (coordinateEuclideanEquiv ι).symm volume volume :=
  PiLp.volume_preserving_ofLp ι

/-- The same coordinate convention also preserves topological closure of
finite arrays of real data. -/
theorem coordinateEuclideanEquiv_image_closure (ι : Type*) [Fintype ι]
    (S : Set (ι → ℝ)) :
    coordinateEuclideanEquiv ι '' closure S =
      closure (coordinateEuclideanEquiv ι '' S) :=
  (coordinateEuclideanEquiv ι).toHomeomorph.image_closure S

/-- The scalar in generic Haar transport is exactly one for these standard
coordinate models. -/
theorem coordinateEuclideanEquiv_frameFactor (ι : Type*) [Fintype ι] :
    mixedVolumeFrameFactor volume volume (coordinateEuclideanEquiv ι) = 1 := by
  unfold mixedVolumeFrameFactor
  simpa only [(coordinateEuclideanEquiv_measurePreserving ι).map_eq] using
    (Measure.addHaarScalarFactor_self (volume : Measure (EuclideanSpace ℝ ι)))

def toEuclideanBody {n : ℕ} (K : Body n) : EuclideanBody n :=
  mapBody (coordinateEuclideanEquiv (Fin n)).toContinuousLinearMap K

def fromEuclideanBody {n : ℕ} (K : EuclideanBody n) : Body n :=
  mapBody (coordinateEuclideanEquiv (Fin n)).symm.toContinuousLinearMap K

@[simp] theorem toEuclideanBody_fromEuclideanBody {n : ℕ} (K : EuclideanBody n) :
    toEuclideanBody (fromEuclideanBody K) = K := by
  apply ConvexBody.ext
  change (coordinateEuclideanEquiv (Fin n)) ''
    ((coordinateEuclideanEquiv (Fin n)).symm '' (K : Set (EuclideanSpace ℝ (Fin n)))) = _
  rw [Set.image_image]
  simp only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply, image_id']

@[simp] theorem fromEuclideanBody_toEuclideanBody {n : ℕ} (K : Body n) :
    fromEuclideanBody (toEuclideanBody K) = K := by
  apply ConvexBody.ext
  change (coordinateEuclideanEquiv (Fin n)).symm ''
    ((coordinateEuclideanEquiv (Fin n)) '' (K : Set (Space n))) = _
  rw [Set.image_image]
  simp only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, image_id']

/-- Euclidean coordinate projection, with the retained coordinates as its
Euclidean target. Its coordinate formula is proved immediately below. -/
def euclideanDeleteCoordinates {n : ℕ} (I : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Retained I) :=
  (coordinateEuclideanEquiv (Retained I)).toContinuousLinearMap.comp
    ((deleteCoordinates I).comp
      (coordinateEuclideanEquiv (Fin n)).symm.toContinuousLinearMap)

@[simp] theorem euclideanDeleteCoordinates_apply {n : ℕ} (I : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (j : Retained I) :
    euclideanDeleteCoordinates I x j = x j.val := rfl

theorem euclideanDeleteCoordinates_target_dimension {n : ℕ} (I : Finset (Fin n)) :
    finrank ℝ (EuclideanSpace ℝ (Retained I)) = n - I.card := by
  simp only [finrank_euclideanSpace, Retained, Fintype.card_subtype_compl,
    Fintype.card_fin, Fintype.card_coe]

theorem euclideanDeleteCoordinates_commutes {n : ℕ} (I : Finset (Fin n)) :
    (euclideanDeleteCoordinates I).comp
        (coordinateEuclideanEquiv (Fin n)).toContinuousLinearMap =
      (coordinateEuclideanEquiv (Retained I)).toContinuousLinearMap.comp
        (deleteCoordinates I) := by
  ext x j
  rfl

def euclideanCoordinateVolume {n : ℕ} (I : Finset (Fin n))
    (K : EuclideanBody n) : ℝ :=
  volume.real (mapBody (euclideanDeleteCoordinates I) K :
    Set (EuclideanSpace ℝ (Retained I)))

/-- Literal projection volumes are identical in the two coordinate models,
including projections of lower-dimensional bodies. -/
theorem euclideanCoordinateVolume_toEuclideanBody {n : ℕ}
    (I : Finset (Fin n)) (K : Body n) :
    euclideanCoordinateVolume I (toEuclideanBody K) = coordinateVolume I K := by
  have hbody : mapBody (euclideanDeleteCoordinates I) (toEuclideanBody K) =
      mapBody (coordinateEuclideanEquiv (Retained I)).toContinuousLinearMap
        (projectedBody I K) := by
    rw [toEuclideanBody, mapBody_comp, euclideanDeleteCoordinates_commutes,
      ← mapBody_comp]
    rfl
  rw [euclideanCoordinateVolume, hbody, coe_mapBody]
  exact measureReal_image_measurePreserving volume volume
    (coordinateEuclideanEquiv (Retained I))
    (coordinateEuclideanEquiv_measurePreserving (Retained I)) _

theorem coordinateVolume_fromEuclideanBody {n : ℕ}
    (I : Finset (Fin n)) (K : EuclideanBody n) :
    coordinateVolume I (fromEuclideanBody K) = euclideanCoordinateVolume I K := by
  simpa only [toEuclideanBody_fromEuclideanBody] using
    (euclideanCoordinateVolume_toEuclideanBody I (fromEuclideanBody K)).symm

def euclideanAllProjectionArray {n k : ℕ} (K : EuclideanBody n) : Deleted n k → ℝ :=
  fun I => euclideanCoordinateVolume I.val K

def euclideanAllProjectionLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  Set.range (euclideanAllProjectionArray (n := n) (k := k))

theorem euclideanAllProjectionArray_toEuclideanBody {n k : ℕ} (K : Body n) :
    euclideanAllProjectionArray (k := k) (toEuclideanBody K) = allProjectionArray K := by
  funext I
  exact euclideanCoordinateVolume_toEuclideanBody I.val K

theorem allProjectionArray_fromEuclideanBody {n k : ℕ} (K : EuclideanBody n) :
    allProjectionArray (k := k) (fromEuclideanBody K) = euclideanAllProjectionArray K := by
  funext I
  exact coordinateVolume_fromEuclideanBody I.val K

/-- Exact equality of the loci for every number of deleted coordinates. -/
theorem euclideanAllProjectionLocus_eq (n k : ℕ) :
    euclideanAllProjectionLocus n k = allProjectionLocus n k := by
  apply Set.Subset.antisymm
  · rintro P ⟨K, rfl⟩
    exact ⟨fromEuclideanBody K, allProjectionArray_fromEuclideanBody K⟩
  · rintro P ⟨K, rfl⟩
    exact ⟨toEuclideanBody K, euclideanAllProjectionArray_toEuclideanBody K⟩

def euclideanProjectionArray {n : ℕ} (K : EuclideanBody n) : Array n :=
  fun i j => if i = j then 0 else euclideanCoordinateVolume {i, j} K

def euclideanProjectionLocus (n : ℕ) : Set (Array n) :=
  Set.range (euclideanProjectionArray (n := n))

def euclideanClosedProjectionLocus (n : ℕ) : Set (Array n) :=
  closure (euclideanProjectionLocus n)

theorem euclideanProjectionArray_toEuclideanBody {n : ℕ} (K : Body n) :
    euclideanProjectionArray (toEuclideanBody K) = projectionArray K := by
  ext i j
  simp only [euclideanProjectionArray, projectionArray,
    euclideanCoordinateVolume_toEuclideanBody]

theorem projectionArray_fromEuclideanBody {n : ℕ} (K : EuclideanBody n) :
    projectionArray (fromEuclideanBody K) = euclideanProjectionArray K := by
  ext i j
  simp only [projectionArray, euclideanProjectionArray, coordinateVolume_fromEuclideanBody]

theorem euclideanProjectionLocus_eq (n : ℕ) :
    euclideanProjectionLocus n = projectionLocus n := by
  apply Set.Subset.antisymm
  · rintro P ⟨K, rfl⟩
    exact ⟨fromEuclideanBody K, projectionArray_fromEuclideanBody K⟩
  · rintro P ⟨K, rfl⟩
    exact ⟨toEuclideanBody K, euclideanProjectionArray_toEuclideanBody K⟩

theorem euclideanClosedProjectionLocus_eq (n : ℕ) :
    euclideanClosedProjectionLocus n = closedProjectionLocus n := by
  rw [euclideanClosedProjectionLocus, euclideanProjectionLocus_eq, closedProjectionLocus]

/-- The actual projection array regarded in the hollow symmetric subspace. -/
def hollowProjectionArray {n : ℕ} (K : Body n) : HollowSymmetricArray n :=
  ⟨projectionArray K, projectionArray_diagonal K, projectionArray_symmetric K⟩

def hollowProjectionLocus (n : ℕ) : Set (HollowSymmetricArray n) :=
  Set.range (hollowProjectionArray (n := n))

theorem val_image_hollowProjectionLocus (n : ℕ) :
    Subtype.val '' hollowProjectionLocus n = projectionLocus n := by
  ext P
  constructor
  · rintro ⟨Q, ⟨K, hK⟩, hQP⟩
    exact ⟨K, (congrArg Subtype.val hK).trans hQP⟩
  · rintro ⟨K, rfl⟩
    exact ⟨hollowProjectionArray K, ⟨K, rfl⟩, rfl⟩

/-- Taking closure intrinsically in hollow symmetric matrices agrees exactly
with the ambient matrix closure used by the principal theorem. -/
theorem hollowProjectionClosure_eq_preimage (n : ℕ) :
    closure (hollowProjectionLocus n) =
      Subtype.val ⁻¹' closedProjectionLocus n := by
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    val_image_hollowProjectionLocus, closedProjectionLocus]

theorem mem_hollowProjectionClosure_iff {n : ℕ} (P : HollowSymmetricArray n) :
    P ∈ closure (hollowProjectionLocus n) ↔ P.val ∈ closedProjectionLocus n := by
  rw [hollowProjectionClosure_eq_preimage]
  rfl

theorem mem_hollowProjectionClosure_iff_euclidean {n : ℕ}
    (P : HollowSymmetricArray n) :
    P ∈ closure (hollowProjectionLocus n) ↔
      P.val ∈ euclideanClosedProjectionLocus n := by
  rw [euclideanClosedProjectionLocus_eq]
  exact mem_hollowProjectionClosure_iff P

def euclideanMarkedTuple {n k : ℕ} (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) (I : Deleted n k) :
    Fin (n - k + k) → EuclideanBody n :=
  Fin.append (fun _ : Fin (n - k) => K)
    (fun j : Fin k => centeredSegment (U (I.val.orderEmbOfFin I.property j)))

def euclideanAllMarkedArray {n k : ℕ} (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) : Deleted n k → ℝ :=
  fun I => (n.factorial : ℝ) / ((n - k).factorial : ℝ) *
    mixedVolume volume (euclideanMarkedTuple K U I)

def euclideanBodyDimension {n : ℕ} (K : EuclideanBody n) : ℕ :=
  finrank ℝ (affineSpan ℝ (K : Set (EuclideanSpace ℝ (Fin n)))).direction

theorem euclideanAllMarkedArray_toEuclideanBody {n k : ℕ}
    (K : Body n) (U : Fin n → Space n) :
    euclideanAllMarkedArray (k := k) (toEuclideanBody K)
        (fun i => coordinateEuclideanEquiv (Fin n) (U i)) = allMarkedArray K U := by
  funext I
  have htuple : euclideanMarkedTuple (toEuclideanBody K)
        (fun i => coordinateEuclideanEquiv (Fin n) (U i)) I =
      fun j => mapBody (coordinateEuclideanEquiv (Fin n)).toContinuousLinearMap
        (markedTuple K U I j) := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [euclideanMarkedTuple, markedTuple, Fin.append_left, toEuclideanBody]
    · intro i
      simp only [euclideanMarkedTuple, markedTuple, Fin.append_right, map_centeredSegment]
      rfl
  unfold euclideanAllMarkedArray allMarkedArray
  rw [htuple, mixedVolume_map_measurePreserving volume volume
    (coordinateEuclideanEquiv (Fin n)) (coordinateEuclideanEquiv_measurePreserving (Fin n))]

theorem allMarkedArray_fromEuclideanBody {n k : ℕ}
    (K : EuclideanBody n) (U : Fin n → EuclideanSpace ℝ (Fin n)) :
    allMarkedArray (k := k) (fromEuclideanBody K)
        (fun i => (coordinateEuclideanEquiv (Fin n)).symm (U i)) = euclideanAllMarkedArray K U := by
  have h := euclideanAllMarkedArray_toEuclideanBody (k := k) (fromEuclideanBody K)
    (fun i => (coordinateEuclideanEquiv (Fin n)).symm (U i))
  simpa only [toEuclideanBody_fromEuclideanBody, ContinuousLinearEquiv.apply_symm_apply] using h.symm

theorem euclideanBodyDimension_toEuclideanBody {n : ℕ} (K : Body n) :
    euclideanBodyDimension (toEuclideanBody K) = bodyDimension K := by
  let T := coordinateEuclideanEquiv (Fin n)
  change finrank ℝ
    (affineSpan ℝ (T.toLinearEquiv.toAffineEquiv.toAffineMap '' (K : Set (Space n)))).direction = _
  rw [← AffineSubspace.map_span T.toLinearEquiv.toAffineEquiv.toAffineMap,
    AffineSubspace.map_direction]
  exact T.toLinearEquiv.finrank_map_eq _

theorem bodyDimension_fromEuclideanBody {n : ℕ} (K : EuclideanBody n) :
    bodyDimension (fromEuclideanBody K) = euclideanBodyDimension K := by
  simpa only [toEuclideanBody_fromEuclideanBody] using
    (euclideanBodyDimension_toEuclideanBody (fromEuclideanBody K)).symm

/-- The unrestricted closure formula of Theorem 3.1 in Euclidean coordinates.
The comparison vectors may be zero or linearly dependent, and the initial
body may have any affine dimension. -/
theorem theorem31_euclidean_closure {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (euclideanAllProjectionLocus n k) ↔
      ∃ (K : EuclideanBody n) (U : Fin n → EuclideanSpace ℝ (Fin n)),
        euclideanAllMarkedArray K U = P := by
  rw [euclideanAllProjectionLocus_eq, theorem31 hk hkn]
  constructor
  · rintro ⟨K, U, heq⟩
    refine ⟨toEuclideanBody K, fun i => coordinateEuclideanEquiv (Fin n) (U i), ?_⟩
    rw [euclideanAllMarkedArray_toEuclideanBody]
    exact heq
  · rintro ⟨K, U, heq⟩
    refine ⟨fromEuclideanBody K, fun i => (coordinateEuclideanEquiv (Fin n)).symm (U i), ?_⟩
    rw [allMarkedArray_fromEuclideanBody]
    exact heq

/-- The complete compactification statement in canonical Euclidean spaces,
with ordinary Euclidean volume, actual Euclidean mixed volume, and actual
Euclidean affine dimension. -/
theorem theorem31_euclidean {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (euclideanAllProjectionLocus n k) ↔
      ∃ (K : EuclideanBody n) (U : Fin n → EuclideanSpace ℝ (Fin n)),
        n - k + 1 ≤ euclideanBodyDimension K ∧ euclideanAllMarkedArray K U = P := by
  rw [euclideanAllProjectionLocus_eq, theorem31_with_dimension hk hkn]
  constructor
  · rintro ⟨K, U, hdim, heq⟩
    refine ⟨toEuclideanBody K, fun i => coordinateEuclideanEquiv (Fin n) (U i), ?_, ?_⟩
    · simpa only [euclideanBodyDimension_toEuclideanBody] using hdim
    · rw [euclideanAllMarkedArray_toEuclideanBody]
      exact heq
  · rintro ⟨K, U, hdim, heq⟩
    refine ⟨fromEuclideanBody K, fun i => (coordinateEuclideanEquiv (Fin n)).symm (U i), ?_, ?_⟩
    · simpa only [bodyDimension_fromEuclideanBody] using hdim
    · rw [allMarkedArray_fromEuclideanBody]
      exact heq

/-- Every unrestricted Euclidean marked representation can be replaced by
one retaining the full dimension bound in the paper. -/
theorem theorem31_euclidean_renormalize_dimension {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) :
    ∃ (L : EuclideanBody n) (V : Fin n → EuclideanSpace ℝ (Fin n)),
      n - k + 1 ≤ euclideanBodyDimension L ∧
        euclideanAllMarkedArray (k := k) L V = euclideanAllMarkedArray K U :=
  (theorem31_euclidean hk hkn (euclideanAllMarkedArray K U)).mp
    ((theorem31_euclidean_closure hk hkn (euclideanAllMarkedArray K U)).mpr ⟨K, U, rfl⟩)

end RankThreeProjection
end
end
end DevelopmentSource30

/- Source module: Projection.SignatureMeaning. SHA256: 20b3d12266d0a396c0834b85fa53ad17e6922017130c6fa97d7b4394a97f6eff -/
section DevelopmentSource31





/-!
# Signature as the signs in a diagonalization

The positive and negative indices used by the main theorem are exactly the
usual counts of positive and negative diagonal coefficients. The radical
dimension is exactly the count of zero coefficients. This equivalence follows
from Mathlib's existence and uniqueness statements for Sylvester's law of
inertia, with no additional spectral or geometric hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace RankThreeProjection

open QuadraticMap

/-- The three indices in the principal statement are precisely the usual
diagonal-sign signature. A diagonalization is a genuine linear isometry of
quadratic forms, and its existence is supplied by Mathlib. -/
theorem signature_iff_diagonal_sign_counts
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (Q : QuadraticForm ℝ E) (p m z : ℕ) :
    (sigPos Q = p ∧ sigNeg Q = m ∧ Module.finrank ℝ Q.radical = z) ↔
      ∃ w : Fin (Module.finrank ℝ E) → ℝ,
        Equivalent Q (weightedSumSquares ℝ w) ∧
        {i | 0 < w i}.ncard = p ∧ {i | w i < 0}.ncard = m ∧
        {i | w i = 0}.ncard = z := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares
    exact ⟨w, hw,
      (QuadraticForm.sigPos_of_equiv_weightedSumSquares hw).symm.trans h.1,
      (QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw).symm.trans h.2.1,
      (QuadraticForm.finrank_radical_of_equiv_weightedSumSquares hw).symm.trans h.2.2⟩
  · rintro ⟨w, hw, hp, hm, hz⟩
    exact ⟨(QuadraticForm.sigPos_of_equiv_weightedSumSquares hw).trans hp,
      (QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw).trans hm,
      (QuadraticForm.finrank_radical_of_equiv_weightedSumSquares hw).trans hz⟩

end RankThreeProjection
end
end
end DevelopmentSource31

#check @RankThreeProjection.theorem31
#print axioms RankThreeProjection.theorem31
#check @RankThreeProjection.theorem31_with_dimension
#print axioms RankThreeProjection.theorem31_with_dimension
#check @RankThreeProjection.theorem31_renormalize_dimension
#print axioms RankThreeProjection.theorem31_renormalize_dimension
#check @RankThreeProjection.theorem31_euclidean
#print axioms RankThreeProjection.theorem31_euclidean
#check @RankThreeProjection.theorem31_euclidean_closure
#print axioms RankThreeProjection.theorem31_euclidean_closure
#check @RankThreeProjection.theorem31_euclidean_renormalize_dimension
#print axioms RankThreeProjection.theorem31_euclidean_renormalize_dimension
#check @VolumePapers.RankThree.no_nonnegative_weighted_triangles
#print axioms VolumePapers.RankThree.no_nonnegative_weighted_triangles
#check @RankThreeProjection.signature_iff_diagonal_sign_counts
#print axioms RankThreeProjection.signature_iff_diagonal_sign_counts
#check @VolumePapers.RankThree.corollary_two_three
#print axioms VolumePapers.RankThree.corollary_two_three
#check @VolumePapers.RankThree.PositiveMetricMatrix.rank_at_least_four
#print axioms VolumePapers.RankThree.PositiveMetricMatrix.rank_at_least_four

/-!
Development/final-audit command to append after the mathematical declarations
of the canonical module. It uses only the pinned Lean environment APIs. It
does not add mathematical declarations or assume propositions. Run it in the
same module so local private proof bodies remain available. Imported, already
checked declarations are recorded as explicit boundary nodes with their module
and transitive axiom set.
-/

public meta section
open Lean Elab Command

elab "#assert_standard_axioms " id:ident : command => do
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms root
  for axiomName in axioms do
    unless axiomName == ``propext || axiomName == ``Classical.choice ||
        axiomName == ``Quot.sound do
      throwError "Dependency audit rejected {root}: nonstandard axiom {axiomName}"
  logInfo m!"Standard-axiom audit passed: {root}; axioms {axioms}"

elab "#export_checked_dependencies " id:ident " to " file:str : command => do
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env := (← getEnv).setExporting false
  let importedRoot := (env.getModuleIdxFor? root).isSome
  let axioms ← collectAxioms root
  for axiomName in axioms do
    unless axiomName == ``propext || axiomName == ``Classical.choice ||
        axiomName == ``Quot.sound do
      throwError "Dependency audit rejected {root}: nonstandard axiom {axiomName}"
  let mut queue : Array Name := #[root]
  let mut position := 0
  let mut seen : NameSet := {}
  let mut nodes : Array Json := #[]
  while position < queue.size do
    let name := queue[position]!
    position := position + 1
    if seen.contains name then
      continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Dependency {name} is absent from the kernel-checked environment"
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      let importedAxioms ← collectAxioms name
      nodes := nodes.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("kind", toJson "imported_boundary"),
        ("module", toJson moduleName.toString),
        ("axioms", toJson (importedAxioms.map Name.toString))]
    else
      let typeDependencies := info.type.getUsedConstants
      let mut valueDependencies := (info.value? true).map Expr.getUsedConstants |>.getD #[]
      if let .inductInfo data := info then
        valueDependencies := valueDependencies ++ data.ctors.toArray
      for dependency in typeDependencies ++ valueDependencies do
        unless seen.contains dependency do
          queue := queue.push dependency
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      nodes := nodes.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("kind", toJson kind),
        ("module", toJson env.mainModule.toString),
        ("type_dependencies", toJson (typeDependencies.map Name.toString)),
        ("value_dependencies", toJson (valueDependencies.map Name.toString))]
  let report := Json.mkObj [
    ("root", toJson root.toString),
    ("root_is_imported", toJson importedRoot),
    ("scope", toJson "Full current-module dependency closure; imported checked boundary nodes explicit"),
    ("axioms", toJson (axioms.map Name.toString)),
    ("nodes", Json.arr nodes)]
  let destination : System.FilePath := file.getString
  if let some parent := destination.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile destination report.pretty
  logInfo m!"Exported checked dependency graph for {root}: {nodes.size} nodes"

/-
Each genuine project module exports all of its local declarations. Later
modules can depend on helpers outside the closure of an earlier headline
theorem, so exporting only headline roots would leave gaps when joining graphs.
The separate endpoint audit checks the allowed axiom set. This report records
the exact kernel environment and does not by itself certify a successful build.
-/
elab "#export_checked_module_dependencies " file:str : command => do
  let env := (← getEnv).setExporting false
  let localNames := env.checked.get.constants.foldStage2
    (fun names name _ =>
      if (env.getModuleIdxFor? name).isNone then names.push name else names)
    (#[] : Array Name)
  let localNames := localNames.qsort Name.lt
  let mut queue := localNames
  let mut position := 0
  let mut seen : NameSet := {}
  let mut nodes : Array Json := #[]
  while position < queue.size do
    let name := queue[position]!
    position := position + 1
    if seen.contains name then
      continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Dependency {name} is absent from the kernel-checked environment"
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      let importedAxioms ← collectAxioms name
      nodes := nodes.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("kind", toJson "imported_boundary"),
        ("module", toJson moduleName.toString),
        ("axioms", toJson (importedAxioms.map Name.toString))]
    else
      let typeDependencies := info.type.getUsedConstants
      let mut valueDependencies := (info.value? true).map Expr.getUsedConstants |>.getD #[]
      if let .inductInfo data := info then
        valueDependencies := valueDependencies ++ data.ctors.toArray
      for dependency in typeDependencies ++ valueDependencies do
        unless seen.contains dependency do
          queue := queue.push dependency
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      nodes := nodes.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("kind", toJson kind),
        ("module", toJson env.mainModule.toString),
        ("type_dependencies", toJson (typeDependencies.map Name.toString)),
        ("value_dependencies", toJson (valueDependencies.map Name.toString))]
  let report := Json.mkObj [
    ("module", toJson env.mainModule.toString),
    ("scope", toJson "All current-module declarations; imported checked boundary nodes explicit"),
    ("local_declarations", toJson (localNames.map Name.toString)),
    ("local_count", toJson localNames.size),
    ("nodes", Json.arr nodes)]
  let destination : System.FilePath := file.getString
  if let some parent := destination.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile destination report.pretty
  logInfo m!"Exported full module dependency graph for {env.mainModule}: {localNames.size} local declarations, {nodes.size} nodes"

#assert_standard_axioms RankThreeProjection.theorem31
#assert_standard_axioms RankThreeProjection.theorem31_with_dimension
#assert_standard_axioms RankThreeProjection.theorem31_renormalize_dimension
#assert_standard_axioms RankThreeProjection.theorem31_euclidean
#assert_standard_axioms RankThreeProjection.theorem31_euclidean_closure
#assert_standard_axioms RankThreeProjection.theorem31_euclidean_renormalize_dimension
#assert_standard_axioms VolumePapers.RankThree.no_nonnegative_weighted_triangles
#assert_standard_axioms RankThreeProjection.signature_iff_diagonal_sign_counts
#assert_standard_axioms VolumePapers.RankThree.corollary_two_three
#assert_standard_axioms VolumePapers.RankThree.PositiveMetricMatrix.rank_at_least_four
#export_checked_module_dependencies ".lake/reports/verification/Compactification.dependencies.json"
