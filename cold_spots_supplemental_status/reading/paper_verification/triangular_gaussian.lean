module
public import PaperVerification.EisensteinArithmetic
public import PaperVerification.ThetaRelations
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triangularGaussian (α : ℝ) (z : TriPoint) : ℝ :=
  ∑' m : EisInt, Real.exp (-α * triQ (eisEmbed m - z))

def triangularSplitEquiv : EisInt ⊕ EisInt ≃ EisInt where
  toFun
    | .inl p => (p.1 + p.2, 2 * p.2)
    | .inr p => (p.1 + p.2 + 1, 2 * p.2 + 1)
  invFun p := if Even p.2 then .inl (p.1 - p.2 / 2, p.2 / 2)
    else .inr (p.1 - p.2 / 2 - 1, p.2 / 2)
  left_inv := by
    intro p
    cases p with
    | inl p =>
      have he : Even (2 * p.2) := even_two_mul _
      change (if Even (2 * p.2) then
        Sum.inl (p.1 + p.2 - (2 * p.2) / 2, (2 * p.2) / 2)
        else Sum.inr (p.1 + p.2 - (2 * p.2) / 2 - 1, (2 * p.2) / 2)) = Sum.inl p
      rw [if_pos he]
      apply congrArg Sum.inl
      apply Prod.ext <;> dsimp <;> omega
    | inr p =>
      have he : ¬Even (2 * p.2 + 1) := by rw [Int.even_iff]; omega
      change (if Even (2 * p.2 + 1) then
        Sum.inl (p.1 + p.2 + 1 - (2 * p.2 + 1) / 2, (2 * p.2 + 1) / 2)
        else Sum.inr (p.1 + p.2 + 1 - (2 * p.2 + 1) / 2 - 1,
          (2 * p.2 + 1) / 2)) = Sum.inr p
      rw [if_neg he]
      apply congrArg Sum.inr
      apply Prod.ext <;> dsimp <;> omega
  right_inv := by
    intro p
    dsimp only
    split_ifs with he
    · rw [Int.even_iff] at he
      apply Prod.ext <;> dsimp <;> omega
    · rw [Int.even_iff] at he
      apply Prod.ext <;> dsimp <;> omega

lemma triangular_even_term (α : ℝ) (z : TriPoint) (p : EisInt) :
    Real.exp (-α * triQ (eisEmbed (triangularSplitEquiv (.inl p)) - z)) =
      Real.exp (-α * ((p.1 : ℝ) - (z.1 - z.2 / 2)) ^ 2) *
      Real.exp (-(3 * α) * ((p.2 : ℝ) - z.2 / 2) ^ 2) := by
  rw [← Real.exp_add]
  dsimp [triangularSplitEquiv, eisEmbed, triQ]
  push_cast
  congr 1
  ring

lemma triangular_odd_term (α : ℝ) (z : TriPoint) (p : EisInt) :
    Real.exp (-α * triQ (eisEmbed (triangularSplitEquiv (.inr p)) - z)) =
      Real.exp (-α * ((p.1 : ℝ) - (z.1 - z.2 / 2 - 1 / 2)) ^ 2) *
      Real.exp (-(3 * α) * ((p.2 : ℝ) - (z.2 / 2 - 1 / 2)) ^ 2) := by
  rw [← Real.exp_add]
  dsimp [triangularSplitEquiv, eisEmbed, triQ]
  push_cast
  congr 1
  ring

theorem hasSum_triangularGaussian {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    HasSum (fun m : EisInt ↦ Real.exp (-α * triQ (eisEmbed m - z)))
      (gaussian α (z.1 - z.2 / 2) * gaussian (3 * α) (z.2 / 2) +
       gaussian α (z.1 - z.2 / 2 - 1 / 2) * gaussian (3 * α) (z.2 / 2 - 1 / 2)) := by
  have h3 : 0 < 3 * α := by positivity
  have he : HasSum
      (fun p : EisInt ↦ Real.exp (-α * triQ (eisEmbed (triangularSplitEquiv (.inl p)) - z)))
      (gaussian α (z.1 - z.2 / 2) * gaussian (3 * α) (z.2 / 2)) := by
    simpa only [triangular_even_term] using hasSum_gaussian_pair hα h3
      (z.1 - z.2 / 2) (z.2 / 2)
  have ho : HasSum
      (fun p : EisInt ↦ Real.exp (-α * triQ (eisEmbed (triangularSplitEquiv (.inr p)) - z)))
      (gaussian α (z.1 - z.2 / 2 - 1 / 2) * gaussian (3 * α) (z.2 / 2 - 1 / 2)) := by
    simpa only [triangular_odd_term] using hasSum_gaussian_pair hα h3
      (z.1 - z.2 / 2 - 1 / 2) (z.2 / 2 - 1 / 2)
  exact (triangularSplitEquiv.hasSum_iff
    (f := fun m : EisInt ↦ Real.exp (-α * triQ (eisEmbed m - z)))).mp (he.sum ho)

theorem summable_triangularGaussian {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    Summable (fun m : EisInt ↦ Real.exp (-α * triQ (eisEmbed m - z))) :=
  (hasSum_triangularGaussian hα z).summable

theorem triangularGaussian_eq_products {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α z =
      gaussian α (z.1 - z.2 / 2) * gaussian (3 * α) (z.2 / 2) +
      gaussian α (z.1 - z.2 / 2 - 1 / 2) * gaussian (3 * α) (z.2 / 2 - 1 / 2) :=
  (hasSum_triangularGaussian hα z).tsum_eq

theorem triangularGaussian_pos {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    0 < triangularGaussian α z := by
  rw [triangularGaussian_eq_products hα]
  exact add_pos (mul_pos (gaussian_pos hα _) (gaussian_pos (by positivity) _))
    (mul_pos (gaussian_pos hα _) (gaussian_pos (by positivity) _))

theorem continuous_triangularGaussian {α : ℝ} (hα : 0 < α) :
    Continuous (triangularGaussian α) := by
  have heq : triangularGaussian α = fun z : TriPoint ↦
      gaussian α (z.1 - z.2 / 2) * gaussian (3 * α) (z.2 / 2) +
      gaussian α (z.1 - z.2 / 2 - 1 / 2) * gaussian (3 * α) (z.2 / 2 - 1 / 2) :=
    funext (triangularGaussian_eq_products hα)
  rw [heq]
  have ha := continuous_gaussian hα
  have hb := continuous_gaussian (show 0 < 3 * α by positivity)
  exact ((ha.comp (continuous_fst.sub (continuous_snd.div_const 2))).mul
      (hb.comp (continuous_snd.div_const 2))).add
    ((ha.comp ((continuous_fst.sub (continuous_snd.div_const 2)).sub continuous_const)).mul
      (hb.comp ((continuous_snd.div_const 2).sub continuous_const)))

theorem triangularGaussian_periodic (α : ℝ) (z : TriPoint) (w : EisInt) :
    triangularGaussian α (z + eisEmbed w) = triangularGaussian α z := by
  unfold triangularGaussian
  rw [← (Equiv.addRight w).tsum_eq]
  apply tsum_congr
  intro m
  simp only [Equiv.coe_addRight, map_add]
  apply congrArg (fun v : TriPoint => Real.exp (-α * triQ v))
  abel

lemma triQ_neg (z : TriPoint) : triQ (-z) = triQ z := by
  dsimp [triQ]
  ring

theorem triangularGaussian_even (α : ℝ) (z : TriPoint) :
    triangularGaussian α (-z) = triangularGaussian α z := by
  unfold triangularGaussian
  rw [← (Equiv.neg EisInt).tsum_eq]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply, map_neg]
  rw [show -eisEmbed m - -z = -(eisEmbed m - z) by abel, triQ_neg]

def triangularResidueGaussian (α : ℝ) (z : TriPoint) (r : ZMod 3) : ℝ :=
  ∑' m : {m : EisInt // eisResidue m = r}, Real.exp (-α * triQ (eisEmbed m.val - z))

def eisRotateC : EisInt ≃ EisInt where
  toFun z := eisOmega z - (0, 1)
  invFun z := eisOmega (eisOmega (z + (0, 1)))
  left_inv := by
    intro z
    change eisOmega (eisOmega ((eisOmega z - (0, 1)) + (0, 1))) = z
    rw [sub_add_cancel, eisOmega_cube]
  right_inv := by
    intro z
    change eisOmega (eisOmega (eisOmega (z + (0, 1)))) - (0, 1) = z
    rw [eisOmega_cube, add_sub_cancel_right]

lemma eisResidue_rotateC (z : EisInt) : eisResidue (eisRotateC z) = eisResidue z - 1 := by
  change eisResidue (eisOmega z - (0, 1)) = _
  rw [map_sub, eisResidue_omega]
  rfl

lemma eisRotateC_distance (z : EisInt) :
    triQ (eisEmbed (eisRotateC z) - triC) = triQ (eisEmbed z - triC) := by
  have h : eisEmbed (eisRotateC z) - triC = triOmega (eisEmbed z - triC) := by
    ext <;> simp [eisRotateC, eisEmbed, eisOmega, triC, triOmega] <;> ring
  rw [h, triQ_omega]

def eisRotateResidue (r : ZMod 3) :
    {m : EisInt // eisResidue m = r} ≃ {m : EisInt // eisResidue m = r - 1} where
  toFun m := ⟨eisRotateC m.val, by rw [eisResidue_rotateC, m.property]⟩
  invFun m := ⟨eisRotateC.symm m.val, by
    have h := eisResidue_rotateC (eisRotateC.symm m.val)
    rw [eisRotateC.apply_symm_apply, m.property] at h
    exact sub_left_inj.mp h.symm⟩
  left_inv := by intro m; apply Subtype.ext; exact eisRotateC.symm_apply_apply m.val
  right_inv := by intro m; apply Subtype.ext; exact eisRotateC.apply_symm_apply m.val

theorem triangularResidueGaussian_rotate (α : ℝ) (r : ZMod 3) :
    triangularResidueGaussian α triC (r - 1) = triangularResidueGaussian α triC r := by
  unfold triangularResidueGaussian
  rw [← (eisRotateResidue r).tsum_eq]
  apply tsum_congr
  intro m
  exact congrArg (fun t : ℝ ↦ Real.exp (-α * t)) (eisRotateC_distance m.val)

theorem triangularResidueGaussian_sum {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    (∑ r : ZMod 3, triangularResidueGaussian α z r) = triangularGaussian α z := by
  have h := (summable_triangularGaussian hα z).hasSum
  have hs := ((Equiv.sigmaFiberEquiv eisResidue).hasSum_iff
    (f := fun m : EisInt ↦ Real.exp (-α * triQ (eisEmbed m - z)))).mpr h
  have hout := hs.sigma (fun r ↦ ((summable_triangularGaussian hα z).subtype
    (fun m ↦ eisResidue m = r)).hasSum)
  simpa only [triangularResidueGaussian, triangularGaussian,
    Function.comp_def, tsum_fintype] using hout.tsum_eq

/-- Each theta-residue class contributes exactly one third at a triangular hole. -/
theorem triangularResidueGaussian_at_c {α : ℝ} (hα : 0 < α) (r : ZMod 3) :
    triangularResidueGaussian α triC r = triangularGaussian α triC / 3 := by
  have h0 := triangularResidueGaussian_rotate α 0
  have h1 := triangularResidueGaussian_rotate α 1
  rw [show (0 : ZMod 3) - 1 = 2 by decide] at h0
  rw [sub_self] at h1
  have hall : ∀ s : ZMod 3, triangularResidueGaussian α triC s =
      triangularResidueGaussian α triC 0 := by
    intro s
    fin_cases s
    · rfl
    · exact h1.symm
    · exact h0
  have hs := triangularResidueGaussian_sum hα triC
  simp only [hall, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_ofNat] at hs
  rw [hall]
  linarith

end PaperVerification.ColdSpots
