module

public import VolumePolynomials.CrossPlaneMixedVolume

@[expose] public section

set_option autoImplicit false

/-! # Rigidity of the four coordinate support terms -/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

def axisNormals : Fin 4 → Plane →L[ℝ] ℝ :=
  ![normal (0, 1), normal (0, -1), normal (1, 0), normal (-1, 0)]

def AxisFunctional (F : ConvexBody Plane → ℝ) : Prop :=
  ∃ c : Fin 4 → ℝ, ∀ A, F A = ∑ i, c i * SupportGeometry.support (A : Set Plane) (axisNormals i)

theorem AxisFunctional.zero : AxisFunctional (fun _ => 0) := by
  first
  | exact ⟨fun _ => 0, by intro A; simp⟩

theorem AxisFunctional.add {F G : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (hG : AxisFunctional G) : AxisFunctional (fun A => F A + G A) := by
  first
  | obtain ⟨c, hc⟩ := hF
    obtain ⟨d, hd⟩ := hG
    refine ⟨fun i => c i + d i, ?_⟩
    intro A
    dsimp only
    rw [hc, hd]
    simp only [add_mul, Finset.sum_add_distrib]

theorem AxisFunctional.smul {F : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (r : ℝ) : AxisFunctional (fun A => r * F A) := by
  first
  | obtain ⟨c, hc⟩ := hF
    refine ⟨fun i => r * c i, ?_⟩
    intro A
    dsimp only
    rw [hc, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)

theorem AxisFunctional.neg {F : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) : AxisFunctional (fun A => -F A) := by
  first
  | simpa only [neg_one_mul] using hF.smul (-1)

theorem AxisFunctional.sub {F G : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (hG : AxisFunctional G) : AxisFunctional (fun A => F A - G A) := by
  first
  | simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem AxisFunctional.sum {ι : Type*} [Fintype ι]
    {F : ι → ConvexBody Plane → ℝ} (hF : ∀ i, AxisFunctional (F i)) :
    AxisFunctional (fun A => ∑ i, F i A) := by
  first
  | choose c hc using hF
    refine ⟨fun j => ∑ i, c i j, ?_⟩
    intro A
    simp_rw [hc]
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]

theorem AxisFunctional.congr {F G : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (h : ∀ A, F A = G A) : AxisFunctional G := by
  first
  | obtain ⟨c, hc⟩ := hF
    exact ⟨c, fun A => (h A).symm.trans (hc A)⟩

theorem axisFunctional_support (i : Fin 4) :
    AxisFunctional (fun A => SupportGeometry.support (A : Set Plane) (axisNormals i)) := by
  first
  | refine ⟨Pi.single i 1, ?_⟩
    intro A
    simp [Pi.single_apply]

theorem axisFunctional_support_normal_X (r : ℝ) :
    AxisFunctional (fun A => SupportGeometry.support (A : Set Plane) (normal (0, r))) := by
  first
  | have h := ((axisFunctional_support 0).smul (max r 0)).add
      ((axisFunctional_support 1).smul (max (-r) 0))
    apply h.congr
    intro A
    have he : r • ((0, 1) : Plane) = (0, r) := by ext <;> simp
    have hn : -((0, 1) : Plane) = (0, -1) := by ext <;> simp
    simpa only [axisNormals, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, he, hn] using
      (support_normal_signed_smul A r (0, 1)).symm

theorem axisFunctional_support_normal_Y (r : ℝ) :
    AxisFunctional (fun A => SupportGeometry.support (A : Set Plane) (normal (r, 0))) := by
  first
  | have h := ((axisFunctional_support 2).smul (max r 0)).add
      ((axisFunctional_support 3).smul (max (-r) 0))
    apply h.congr
    intro A
    have he : r • ((1, 0) : Plane) = (r, 0) := by ext <;> simp
    have hn : -((1, 0) : Plane) = (-1, 0) := by ext <;> simp
    simpa only [axisNormals, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, he, hn] using
      (support_normal_signed_smul A r (1, 0)).symm

theorem axisFunctional_support_normal {e : Plane} (he : e.1 = 0 ∨ e.2 = 0) :
    AxisFunctional (fun A => SupportGeometry.support (A : Set Plane) (normal e)) := by
  first
  | rcases he with he | he
    · have h : e = (0, e.2) := Prod.ext he rfl
      rw [h]
      exact axisFunctional_support_normal_X _
    · have h : e = (e.1, 0) := Prod.ext rfl he
      rw [h]
      exact axisFunctional_support_normal_Y _

theorem axisFunctional_width : AxisFunctional width := by
  first
  | apply ((axisFunctional_support 0).add (axisFunctional_support 1)).congr
    intro A
    exact support_axisX_sum A

theorem axisFunctional_height : AxisFunctional height := by
  first
  | apply ((axisFunctional_support 2).add (axisFunctional_support 3)).congr
    intro A
    exact support_axisY_sum A

/-- Translation invariance and the two unit-segment values determine an
axis-supported difference completely. Four tests suffice, even for signed
coefficients and degenerate test bodies. -/
theorem AxisFunctional.eq_zero {F : ConvexBody Plane → ℝ} (hF : AxisFunctional F)
    (hpx : F (pointBody (1, 0)) = 0) (hpy : F (pointBody (0, 1)) = 0)
    (hx : F unitX = 0) (hy : F unitY = 0) : ∀ A, F A = 0 := by
  first
  | obtain ⟨c, hc⟩ := hF
    rw [hc] at hpx hpy hx hy
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, axisNormals,
      Matrix.cons_val_zero, Matrix.cons_val_succ, support_pointBody, normal_apply,
      mul_zero, mul_one, zero_sub, sub_zero, zero_mul, neg_zero,
      support_unitX, support_unitY, abs_zero, abs_one, abs_neg] at hpx hpy hx hy
    norm_num at hpx hpy hx hy
    have h0 : c 0 = 0 := by linarith
    have h1 : c 1 = 0 := by linarith
    have h2 : c 2 = 0 := by linarith
    have h3 : c 3 = 0 := by linarith
    have hcz : ∀ i, c i = 0 := by
      intro i
      fin_cases i <;> assumption
    intro A
    rw [hc]
    simp only [hcz, zero_mul, Finset.sum_const_zero]

end VolumePolynomials.PlanarInteraction
