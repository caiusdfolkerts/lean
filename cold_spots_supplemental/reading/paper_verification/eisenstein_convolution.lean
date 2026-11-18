module
public import PaperVerification.EisensteinDFT
public import PaperVerification.TriangularGaussian
public import PaperVerification.GaussianProduct
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def eisZeroSumEquiv :
    (Σ a : EisInt, Σ b : EisInt, {c : EisInt // eisResidue c = -eisResidue a - eisResidue b}) ≃
      TriZeroSum where
  toFun p := ⟨![p.1, p.2.1, p.2.2.val], by
    simp only [Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add]
    rw [p.2.2.property]
    abel⟩
  invFun h := ⟨h.val 0, h.val 1, ⟨h.val 2, by
    have hh := h.property
    simp only [Fin.sum_univ_three,
      map_add] at hh
    linear_combination hh⟩⟩
  left_inv := by rintro ⟨a,b,c⟩; rfl
  right_inv := by
    intro h
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

def eisZeroSumSwap : TriZeroSum ≃ TriZeroSum where
  toFun h := ⟨![h.val 0, h.val 2, h.val 1], by
    have hh := h.property
    simp only [Fin.sum_univ_three, map_add] at hh
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add]
    linear_combination hh⟩
  invFun h := ⟨![h.val 0, h.val 2, h.val 1], by
    have hh := h.property
    simp only [Fin.sum_univ_three, map_add] at hh
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add]
    linear_combination hh⟩
  left_inv := by intro h; apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv := by intro h; apply Subtype.ext; funext i; fin_cases i <;> rfl

theorem eis_convolution_uniform_third (f g h : EisInt → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h) (C : ℝ)
    (hc : ∀ r : ZMod 3, (∑' c : {c : EisInt // eisResidue c = r}, h c.val) = C) :
    (∑' v : TriZeroSum, f (v.val 0) * g (v.val 1) * h (v.val 2)) =
      (∑' a, f a) * (∑' b, g b) * C := by
  have hall : Summable (fun v : Fin 3 → EisInt ↦ f (v 0) * g (v 1) * h (v 2)) := by
    have ht := summable_fin_product 3 (![f,g,h]) (by
      intro i; fin_cases i <;> assumption)
    simpa [Fin.prod_univ_succ, mul_assoc] using ht
  have hz := hall.subtype (fun v ↦ eisResidue (∑ i, v i) = 0)
  have hs := eisZeroSumEquiv.summable_iff.mpr hz
  change Summable (fun p : (Σ a : EisInt, Σ b : EisInt,
    {c : EisInt // eisResidue c = -eisResidue a - eisResidue b}) ↦
    f p.1 * g p.2.1 * h p.2.2.val) at hs
  rw [← eisZeroSumEquiv.tsum_eq]
  change (∑' p : (Σ a : EisInt, Σ b : EisInt,
    {c : EisInt // eisResidue c = -eisResidue a - eisResidue b}),
    f p.1 * g p.2.1 * h p.2.2.val) = _
  rw [hs.tsum_sigma]
  calc
    (∑' a, ∑' b : (Σ b : EisInt, {c : EisInt //
        eisResidue c = -eisResidue a - eisResidue b}),
        f a * g b.1 * h b.2.val) =
        ∑' a, ∑' b, f a * g b * C := by
      apply tsum_congr
      intro a
      rw [(hs.sigma_factor a).tsum_sigma]
      apply tsum_congr
      intro b
      change (∑' c : {c : EisInt // eisResidue c = -eisResidue a - eisResidue b},
        (f a * g b) * h c.val) = f a * g b * C
      rw [tsum_mul_left, hc]
    _ = (∑' a, f a) * (∑' b, g b) * C := by
      calc
        (∑' a, ∑' b, f a * g b * C) =
            ∑' a, (f a * (∑' b, g b)) * C := by
          apply tsum_congr
          intro a
          rw [tsum_mul_right, tsum_mul_left]
        _ = _ := by rw [tsum_mul_right, tsum_mul_right]

theorem eis_convolution_uniform_second (f g h : EisInt → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h) (C : ℝ)
    (hc : ∀ r : ZMod 3, (∑' c : {c : EisInt // eisResidue c = r}, g c.val) = C) :
    (∑' v : TriZeroSum, f (v.val 0) * g (v.val 1) * h (v.val 2)) =
      (∑' a, f a) * (∑' b, h b) * C := by
  rw [← eisZeroSumSwap.tsum_eq]
  have he : (fun v : TriZeroSum ↦
      f ((eisZeroSumSwap v).val 0) * g ((eisZeroSumSwap v).val 1) *
        h ((eisZeroSumSwap v).val 2)) =
      fun v : TriZeroSum ↦ f (v.val 0) * h (v.val 1) * g (v.val 2) := by
    funext v
    dsimp [eisZeroSumSwap]
    ring
  rw [he]
  exact eis_convolution_uniform_third f h g hf hh hg C hc

def eisResidueNeg (r : ZMod 3) :
    {m : EisInt // eisResidue m = r} ≃ {m : EisInt // eisResidue m = -r} where
  toFun m := ⟨-m.val, by rw [map_neg, m.property]⟩
  invFun m := ⟨-m.val, by rw [map_neg, m.property, neg_neg]⟩
  left_inv := by intro m; apply Subtype.ext; exact neg_neg _
  right_inv := by intro m; apply Subtype.ext; exact neg_neg _

theorem triangularResidueGaussian_neg (α : ℝ) (z : TriPoint) (r : ZMod 3) :
    triangularResidueGaussian α (-z) (-r) = triangularResidueGaussian α z r := by
  unfold triangularResidueGaussian
  rw [← (eisResidueNeg r).tsum_eq]
  apply tsum_congr
  intro m
  change Real.exp (-α * triQ (eisEmbed (-m.val) - -z)) = _
  rw [map_neg, show -eisEmbed m.val - -z = -(eisEmbed m.val - z) by abel, triQ_neg]

def eisResidueAdd (w : EisInt) (r : ZMod 3) :
    {m : EisInt // eisResidue m = r} ≃
      {m : EisInt // eisResidue m = r + eisResidue w} where
  toFun m := ⟨m.val + w, by rw [map_add, m.property]⟩
  invFun m := ⟨m.val - w, by rw [map_sub, m.property, add_sub_cancel_right]⟩
  left_inv := by intro m; apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv := by intro m; apply Subtype.ext; exact sub_add_cancel _ _

theorem triangularResidueGaussian_add (α : ℝ) (z : TriPoint) (w : EisInt) (r : ZMod 3) :
    triangularResidueGaussian α (z + eisEmbed w) (r + eisResidue w) =
      triangularResidueGaussian α z r := by
  unfold triangularResidueGaussian
  rw [← (eisResidueAdd w r).tsum_eq]
  apply tsum_congr
  intro m
  change Real.exp (-α * triQ (eisEmbed (m.val + w) - (z + eisEmbed w))) = _
  rw [map_add, add_sub_add_right_eq_sub]

lemma triangularResidueGaussian_at_neg_c {α : ℝ} (hα : 0 < α) (r : ZMod 3) :
    triangularResidueGaussian α (-triC) r = triangularGaussian α triC / 3 := by
  rw [← neg_neg r, triangularResidueGaussian_neg]
  exact triangularResidueGaussian_at_c hα (-r)

lemma triangularResidueGaussian_at_neg_two_c {α : ℝ} (hα : 0 < α) (r : ZMod 3) :
    triangularResidueGaussian α (-(2 : ℝ) • triC) r = triangularGaussian α triC / 3 := by
  have hz : -(2 : ℝ) • triC = triC + eisEmbed (-1,1) := by
    ext <;> norm_num [triC, eisEmbed]
  have hr : eisResidue (-1,1) = 0 := by norm_num [eisResidue]
  rw [hz, ← add_zero r, ← hr, triangularResidueGaussian_add]
  exact triangularResidueGaussian_at_c hα r

end PaperVerification.ColdSpots
