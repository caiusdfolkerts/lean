module

public import VolumePolynomials.InteractionEdges
public import VolumePolynomials.InteractionSpectralBound

@[expose] public section
set_option autoImplicit false

/-! # Exact Fourier matrix of the product-edge body -/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

def flipCorner (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

@[simp] theorem flipCorner_flip (i : Fin 2) : flipCorner (flipCorner i) = i := by
  first
  | fin_cases i <;> norm_num [flipCorner]

theorem flipCorner_eq_iff (i j : Fin 2) : flipCorner i = j ↔ i = flipCorner j := by
  first
  | constructor
    · intro h
      simpa using congrArg flipCorner h
    · intro h
      simpa using congrArg flipCorner h

theorem signIndex_neg {x : ℝ} (hx : x ≠ 0) : signIndex (-x) = flipCorner (signIndex x) := by
  first
  | rcases lt_or_gt_of_ne hx with hx | hx
    · simp [signIndex, flipCorner, not_le_of_gt hx, (neg_pos.mpr hx).le]
    · simp [signIndex, flipCorner, hx.le, not_le_of_gt (neg_neg_of_pos hx)]

theorem signIndex_pos_mul {a x : ℝ} (ha : 0 < a) : signIndex (a * x) = signIndex x := by
  first
  | unfold signIndex
    simp only [mul_nonneg_iff_of_pos_left ha]

theorem slopeAtom_axis {e : Plane} (he : e.1 = 0 ∨ e.2 = 0) : slopeAtom e = 0 := by
  first
  | have hw : atomWeight e = 0 := by
      first
      | apply Subtype.ext
        change Real.sqrt (|e.1| * |e.2|) = 0
        rcases he with he | he <;> simp [he]
    rw [slopeAtom, hw, zero_smul]

theorem cornerAtom_axis {e : Plane} (he : e.1 = 0 ∨ e.2 = 0) (i j : Fin 2) :
    cornerAtom e i j = 0 := by
  first
  | simp only [cornerAtom, slopeAtom_axis he]
    split_ifs <;> rfl

theorem cornerMatrix_completed {ι : Type*} [Fintype ι] (e : ι → Plane) :
    cornerMatrix (completedEdges e) = cornerMatrix e := by
  first
  | ext i j : 2
    simp only [cornerMatrix, completedEdges, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    have haxis (k : Fin 4) : cornerAtom (axisCompletion e k) i j = 0 := by
      first
      | apply cornerAtom_axis
        fin_cases k <;> simp [axisCompletion]
    simp only [haxis, Finset.sum_const_zero, add_zero]

theorem charFun_slopeAtom (e : Plane) (ξ : ℝ) :
    charFun (slopeAtom e) ξ = (atomWeight e : ℂ) *
      Complex.exp (((ξ * atomSlope e : ℝ) : ℂ) * Complex.I) := by
  first
  | simp only [charFun_apply_real, slopeAtom, integral_smul_nnreal_measure,
      integral_dirac, NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul]

theorem charFun_cornerAtom (e : Plane) (i j : Fin 2) (ξ : ℝ) :
    charFun (cornerAtom e i j) ξ =
      if signIndex e.1 = i ∧ signIndex e.2 = j then charFun (slopeAtom e) ξ else 0 := by
  first
  | unfold cornerAtom
    split_ifs <;> simp

theorem charFun_cornerMatrix {ι : Type*} [Fintype ι] (e : ι → Plane)
    (i j : Fin 2) (ξ : ℝ) :
    charFun (cornerMatrix e i j) ξ = ∑ k, charFun (cornerAtom (e k) i j) ξ := by
  first
  | simp only [charFun_eq_integral_innerProbChar, cornerMatrix]
    exact integral_finsetSum_measure (fun k _ =>
      (BoundedContinuousFunction.innerProbChar ξ).integrable (cornerAtom (e k) i j))

theorem interactionEdge_axis_left {b c : Plane} (hb : b.1 = 0 ∨ b.2 = 0) :
    (interactionEdge b c).1 = 0 ∨ (interactionEdge b c).2 = 0 := by
  first
  | rcases hb with hb | hb
    · left
      simp [interactionEdge, hb]
    · left
      unfold interactionEdge
      split_ifs <;> simp [hb]

theorem interactionEdge_axis_right {b c : Plane} (hc : c.1 = 0 ∨ c.2 = 0) :
    (interactionEdge b c).1 = 0 ∨ (interactionEdge b c).2 = 0 := by
  first
  | rcases hc with hc | hc
    · left
      simp [interactionEdge, hc]
    · right
      unfold interactionEdge
      split_ifs <;> simp [hc]

theorem interactionEdge_weight {b c : Plane} (h : 0 < b.1 * c.1) :
    (atomWeight (interactionEdge b c) : ℝ) =
      (atomWeight b : ℝ) * (atomWeight c : ℝ) := by
  first
  | change Real.sqrt (|(interactionEdge b c).1| * |(interactionEdge b c).2|) =
      Real.sqrt (|b.1| * |b.2|) * Real.sqrt (|c.1| * |c.2|)
    rw [show interactionEdge b c = (-|c.1| * b.2, |b.1| * c.2) from
      by simp only [interactionEdge, if_pos h]]
    simp only [abs_mul, abs_neg, abs_abs]
    rw [← Real.sqrt_mul (mul_nonneg (abs_nonneg b.1) (abs_nonneg b.2))]
    congr 1
    ring

theorem interactionEdge_slope {b c : Plane} (h : 0 < b.1 * c.1)
    (hb : b.2 ≠ 0) (hc : c.2 ≠ 0) :
    atomSlope (interactionEdge b c) = atomSlope c - atomSlope b := by
  first
  | have hb1 : b.1 ≠ 0 := fun hb1 => by simp [hb1] at h
    have hc1 : c.1 ≠ 0 := fun hc1 => by simp [hc1] at h
    simp only [atomSlope, interactionEdge, if_pos h, abs_mul, abs_neg, abs_abs]
    rw [Real.log_div (mul_ne_zero (abs_ne_zero.mpr hb1) (abs_ne_zero.mpr hc))
        (mul_ne_zero (abs_ne_zero.mpr hc1) (abs_ne_zero.mpr hb)),
      Real.log_mul (abs_ne_zero.mpr hb1) (abs_ne_zero.mpr hc),
      Real.log_mul (abs_ne_zero.mpr hc1) (abs_ne_zero.mpr hb),
      Real.log_div (abs_ne_zero.mpr hc) (abs_ne_zero.mpr hc1),
      Real.log_div (abs_ne_zero.mpr hb) (abs_ne_zero.mpr hb1)]
    ring

theorem charFun_interactionAtom {b c : Plane} (h : 0 < b.1 * c.1) (ξ : ℝ) :
    charFun (slopeAtom (interactionEdge b c)) ξ =
      conj (charFun (slopeAtom b) ξ) * charFun (slopeAtom c) ξ := by
  first
  | by_cases hb : b.2 = 0
    · rw [slopeAtom_axis (interactionEdge_axis_left (Or.inr hb)),
        slopeAtom_axis (Or.inr hb)]
      simp
    by_cases hc : c.2 = 0
    · rw [slopeAtom_axis (interactionEdge_axis_right (Or.inr hc)),
        slopeAtom_axis (Or.inr hc)]
      simp
    rw [← charFun_neg, charFun_slopeAtom, charFun_slopeAtom, charFun_slopeAtom]
    have hw := interactionEdge_weight h
    have hwc : (atomWeight (interactionEdge b c) : ℂ) =
        (atomWeight b : ℂ) * (atomWeight c : ℂ) := by exact_mod_cast hw
    rw [hwc, interactionEdge_slope h hb hc]
    have he : (((ξ * (atomSlope c - atomSlope b) : ℝ) : ℂ) * Complex.I) =
        (((-ξ * atomSlope b : ℝ) : ℂ) * Complex.I) +
        (((ξ * atomSlope c : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_add]
    ring

theorem cornerAtom_fourier_product_sum (b c : Plane) (j k : Fin 2) (ξ : ℝ) :
    (∑ i, conj (charFun (cornerAtom b i j) ξ) * charFun (cornerAtom c i k) ξ) =
      if signIndex b.1 = signIndex c.1 ∧ signIndex b.2 = j ∧ signIndex c.2 = k
        then conj (charFun (slopeAtom b) ξ) * charFun (slopeAtom c) ξ else 0 := by
  first
  | have hterm (i : Fin 2) :
        conj (charFun (cornerAtom b i j) ξ) * charFun (cornerAtom c i k) ξ =
          if signIndex b.1 = i then
            (if signIndex b.1 = signIndex c.1 ∧ signIndex b.2 = j ∧ signIndex c.2 = k
              then conj (charFun (slopeAtom b) ξ) * charFun (slopeAtom c) ξ else 0) else 0 := by
      first
      | rw [charFun_cornerAtom, charFun_cornerAtom]
        by_cases hi : signIndex b.1 = i
        · subst i
          by_cases hc : signIndex b.1 = signIndex c.1 <;>
            by_cases hj : signIndex b.2 = j <;> by_cases hk : signIndex c.2 = k <;>
            simp [hc, hj, hk, eq_comm]
        · simp [hi]
    simp_rw [hterm]
    simp

theorem charFun_interactionCornerAtom (b c : Plane) (i j : Fin 2) (ξ : ℝ) :
    charFun (cornerAtom (interactionEdge b c) i j) ξ =
      ∑ k, conj (charFun (cornerAtom b k (flipCorner i)) ξ) *
        charFun (cornerAtom c k j) ξ := by
  first
  | by_cases hb : b.1 = 0 ∨ b.2 = 0
    · rw [cornerAtom_axis (interactionEdge_axis_left hb)]
      simp only [cornerAtom_axis hb, charFun_zero_measure, map_zero, zero_mul,
        Finset.sum_const_zero]
    by_cases hc : c.1 = 0 ∨ c.2 = 0
    · rw [cornerAtom_axis (interactionEdge_axis_right hc)]
      simp only [cornerAtom_axis hc, charFun_zero_measure, mul_zero, Finset.sum_const_zero]
    have hb1 : b.1 ≠ 0 := fun h => hb (Or.inl h)
    have hb2 : b.2 ≠ 0 := fun h => hb (Or.inr h)
    have hc1 : c.1 ≠ 0 := fun h => hc (Or.inl h)
    have hc2 : c.2 ≠ 0 := fun h => hc (Or.inr h)
    rw [cornerAtom_fourier_product_sum]
    simp only [signIndex_eq_iff hb1 hc1]
    by_cases h : 0 < b.1 * c.1
    · have hs1 : signIndex (interactionEdge b c).1 = flipCorner (signIndex b.2) := by
        first
        | rw [interactionEdge, if_pos h]
          change signIndex (-|c.1| * b.2) = _
          rw [show -|c.1| * b.2 = |c.1| * (-b.2) by ring,
            signIndex_pos_mul (abs_pos.mpr hc1), signIndex_neg hb2]
      have hs2 : signIndex (interactionEdge b c).2 = signIndex c.2 := by
        first
        | rw [interactionEdge, if_pos h]
          exact signIndex_pos_mul (abs_pos.mpr hb1)
      rw [charFun_cornerAtom, hs1, hs2, charFun_interactionAtom h]
      simp only [flipCorner_eq_iff, h, true_and]
    · simp only [h, false_and, ite_false]
      simp [interactionEdge, h, cornerAtom_axis (e := (0 : Plane)) (Or.inl rfl)]

def cornerSwapMatrix : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if j = flipCorner i then 1 else 0

theorem cornerSwapMatrix_mul (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (cornerSwapMatrix * M) i j = M (flipCorner i) j := by
  first
  | simp [cornerSwapMatrix, Matrix.mul_apply]

theorem productEdges_fourier {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → Plane) (c : κ → Plane) (ξ : ℝ) :
    slopeFourierMatrix (cornerMatrix (productEdges b c)) ξ =
      cornerSwapMatrix * (slopeFourierMatrix (cornerMatrix b) ξ)ᴴ *
        slopeFourierMatrix (cornerMatrix c) ξ := by
  first
  | ext i j
    rw [Matrix.mul_assoc, cornerSwapMatrix_mul]
    simp only [slopeFourierMatrix, charFun_cornerMatrix, productEdges,
      Fintype.sum_prod_type, charFun_interactionCornerAtom,
      Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum]
    calc
      _ = ∑ a, ∑ k, ∑ d,
          conj (charFun (cornerAtom (b a) k (flipCorner i)) ξ) *
            charFun (cornerAtom (c d) k j) ξ :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ k, ∑ a, ∑ d,
          conj (charFun (cornerAtom (b a) k (flipCorner i)) ξ) *
            charFun (cornerAtom (c d) k j) ξ := Finset.sum_comm
      _ = _ := by
        first
        | symm
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          simp only [starRingEnd_apply]

/-- Exact formula (4.10), including the four explicitly added axis edges. -/
theorem completed_productEdges_fourier {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → Plane) (c : κ → Plane) (ξ : ℝ) :
    slopeFourierMatrix (cornerMatrix (completedEdges (productEdges b c))) ξ =
      cornerSwapMatrix * (slopeFourierMatrix (cornerMatrix b) ξ)ᴴ *
        slopeFourierMatrix (cornerMatrix c) ξ := by
  first
  | rw [cornerMatrix_completed, productEdges_fourier]

theorem matrixSecondTrace_cornerSwap (M : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSecondTrace (cornerSwapMatrix * M) = matrixSecondTrace M := by
  first
  | simp only [matrixSecondTrace_eq_sum, cornerSwapMatrix_mul, Fin.sum_univ_two]
    norm_num [flipCorner]
    ring

theorem productEdge_secondMoment {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → Plane) (c : κ → Plane) :
    slopeSecondMoment (cornerMatrix (completedEdges (productEdges b c))) =
      slopeInteractionMoment (cornerMatrix b) (cornerMatrix c) := by
  first
  | unfold slopeSecondMoment slopeInteractionMoment
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ξ
    change matrixSecondTrace (slopeFourierMatrix (cornerMatrix (completedEdges (productEdges b c))) ξ) =
      matrixSecondTrace ((slopeFourierMatrix (cornerMatrix b) ξ)ᴴ *
        slopeFourierMatrix (cornerMatrix c) ξ)
    rw [completed_productEdges_fourier, Matrix.mul_assoc, matrixSecondTrace_cornerSwap]

end VolumePolynomials.PlanarEdges
