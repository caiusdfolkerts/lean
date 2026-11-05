module
public import PaperVerification.EisensteinConvolution
public import Mathlib.Tactic.Module
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triangularProduct (α : ℝ) (z : TriPoint) : ℝ :=
  triangularGaussian α z * triangularGaussian α (z + triC) *
    triangularGaussian α (z - triC)

def triangularConstrained (α : ℝ) (z w u : TriPoint) : ℝ :=
  ∑' h : TriZeroSum,
    Real.exp (-α * triQ (eisEmbed (h.val 0) - z)) *
      Real.exp (-α * triQ (eisEmbed (h.val 1) - w)) *
      Real.exp (-α * triQ (eisEmbed (h.val 2) - u))

lemma triangularConstrained_third {α : ℝ} (hα : 0 < α) (z w u : TriPoint)
    (C : ℝ) (hu : ∀ r, triangularResidueGaussian α u r = C) :
    triangularConstrained α z w u = triangularGaussian α z * triangularGaussian α w * C :=
  eis_convolution_uniform_third _ _ _ (summable_triangularGaussian hα z)
    (summable_triangularGaussian hα w) (summable_triangularGaussian hα u) C hu

lemma triangularConstrained_second {α : ℝ} (hα : 0 < α) (z w u : TriPoint)
    (C : ℝ) (hw : ∀ r, triangularResidueGaussian α w r = C) :
    triangularConstrained α z w u = triangularGaussian α z * triangularGaussian α u * C :=
  eis_convolution_uniform_second _ _ _ (summable_triangularGaussian hα z)
    (summable_triangularGaussian hα w) (summable_triangularGaussian hα u) C hw

set_option maxHeartbeats 0 in
lemma triangularProduct_glue {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularProduct α z = ∑ r : ZMod 3,
      triangularConstrained α (-triTheta z - (r.val : ℝ) • triC)
        (triC - (r.val : ℝ) • triC) (-triC - (r.val : ℝ) • triC) := by
  let f : (Fin 3 → EisInt) → ℝ := fun v ↦
    ∏ i, Real.exp (-α * triQ (eisEmbed (v i) - (![z,z+triC,z-triC] : Fin 3 → TriPoint) i))
  let g : TriGlueIndex → ℝ := fun p ↦
    ∏ i, Real.exp (-α * triQ (triGluePoint p i -
      (![-triTheta z,triC,-triC] : Fin 3 → TriPoint) i))
  have hf : Summable f := by
    dsimp only [f]
    exact summable_fin_product 3
      (fun i m ↦ Real.exp (-α * triQ
        (eisEmbed m - (![z,z+triC,z-triC] : Fin 3 → TriPoint) i)))
      (fun i ↦ summable_triangularGaussian hα _)
  have he (v : Fin 3 → EisInt) : f v = g (triDFTIntegerEquiv v) := by
    dsimp [f,g]
    rw [← Real.exp_sum, ← Real.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      triDFT_lattice_distance, triDFTIntegerEquiv_apply]
  have hg : Summable g := triDFTIntegerEquiv.summable_iff.mp (hf.congr he)
  have hP : triangularProduct α z = ∑' v, f v := by
    dsimp only [f]
    rw [tsum_fin_product 3
      (fun i (m : EisInt) ↦ Real.exp (-α * triQ
        (eisEmbed m - (![z,z+triC,z-triC] : Fin 3 → TriPoint) i)))
      (fun i ↦ summable_triangularGaussian hα _)]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, triangularProduct, triangularGaussian]
  rw [hP]
  calc
    (∑' v, f v) = ∑' p, g p := by
      simp_rw [he]
      exact triDFTIntegerEquiv.tsum_eq _
    _ = ∑ r : ZMod 3, ∑' h : TriZeroSum, g (r,h) := by
      rw [hg.tsum_prod, tsum_fintype]
    _ = ∑ r : ZMod 3,
        triangularConstrained α (-triTheta z - (r.val : ℝ) • triC)
          (triC - (r.val : ℝ) • triC) (-triC - (r.val : ℝ) • triC) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply tsum_congr
      intro h
      dsimp [g, triangularConstrained]
      simp only [Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one,
        triGluePoint]
      have hshift (a b d : TriPoint) : a + d - b = a - (b - d) := by abel
      simp only [hshift, mul_assoc]

lemma triangularGaussian_neg_three_c (α : ℝ) :
    triangularGaussian α (-(3 : ℝ) • triC) = triangularGaussian α 0 := by
  have he : -(3 : ℝ) • triC = (0 : TriPoint) + eisEmbed (-1,1) := by
    ext <;> norm_num [triC,eisEmbed]
  rw [he, triangularGaussian_periodic]

lemma triangularGaussian_two_c (α : ℝ) (z : TriPoint) :
    triangularGaussian α (z + (2 : ℝ) • triC) = triangularGaussian α (z - triC) := by
  have he : z + (2 : ℝ) • triC = (z - triC) + eisEmbed (1,-1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [he, triangularGaussian_periodic]

/-- Proposition 8.1, equation (30), proved directly from the physical lattice
by an exact three-coset isometry and absolutely convergent residue sums. -/
theorem triangular_cubic_identity {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularProduct α z = triangularGaussian α triC / 3 *
      (triangularGaussian α 0 *
          (triangularGaussian α (triTheta z + triC) +
            triangularGaussian α (triTheta z - triC)) +
        triangularGaussian α triC * triangularGaussian α (triTheta z)) := by
  rw [triangularProduct_glue hα]
  have hs : (Finset.univ : Finset (ZMod 3)) = {0,1,2} := by decide
  rw [hs]
  rw [Finset.sum_insert (show (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) by decide),
    Finset.sum_insert (show (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) by decide),
    Finset.sum_singleton]
  simp only [ZMod.val_zero, zmodThree_val_one, zmodThree_val_two, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_smul, one_smul, sub_zero, sub_self]
  have h0 := triangularConstrained_third hα (-triTheta z) triC (-triC)
    (triangularGaussian α triC / 3) (triangularResidueGaussian_at_neg_c hα)
  have h1 := triangularConstrained_third hα (-triTheta z - triC) 0 (-(2 : ℝ) • triC)
    (triangularGaussian α triC / 3) (triangularResidueGaussian_at_neg_two_c hα)
  have h2 := triangularConstrained_second hα (-triTheta z - (2 : ℝ) • triC)
    (-triC) (-(3 : ℝ) • triC) (triangularGaussian α triC / 3)
    (triangularResidueGaussian_at_neg_c hα)
  have e1 : -triC - triC = -(2 : ℝ) • triC := by module
  have e2 : triC - (2 : ℝ) • triC = -triC := by module
  have e3 : -triC - (2 : ℝ) • triC = -(3 : ℝ) • triC := by module
  rw [e1,e2,e3,h0,h1,h2,triangularGaussian_even,triangularGaussian_neg_three_c]
  rw [show -triTheta z - triC = -(triTheta z + triC) by abel,
    show -triTheta z - (2 : ℝ) • triC = -(triTheta z + (2 : ℝ) • triC) by module,
    triangularGaussian_even,triangularGaussian_even,triangularGaussian_two_c]
  ring

end PaperVerification.ColdSpots
