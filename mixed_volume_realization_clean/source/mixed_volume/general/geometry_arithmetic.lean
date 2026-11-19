module

public import mixed_volume.general.quadratic_moments
public import mixed_volume.general.realization_forward
public import mixed_volume.general.labels
public import Mathlib.LinearAlgebra.Lagrange
public import mixed_volume.general.projected_forcing
public import mixed_volume.general.target_polynomial

/-! Standby source partition. Generation is not a proof certificate.
Exact copied proof ranges are recorded in the adjacent manifest. -/

/- BEGIN SOURCE: MixedVolume/General/ReferenceMoments.lean -/
section


/-! Exact rational absolute linear moments at the reference thresholds a/s.
The repeating base-(s+1) digit gives a one-state recursion, while every other
first-letter class has a fixed sign. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.ReferenceMoments

open VolumePolynomials AutomatonWords AutomatonZonoids AutomatonMoments AutomatonRecurrence
open MomentGeometry QuadraticMoments Matrix
open scoped BigOperators

variable {s m : ℕ}

def digit (a : Fin s) : ℝ := (a.val : ℝ) + 1

def thresholdTerm (A : Data s m) (a : Fin s) (j : Fin m) (w : Word s) : ℝ :=
  massTerm A j w * |digit a - (s : ℝ) * tag w|

def thresholdMoment (A : Data s m) (a : Fin s) (j : Fin m) : ℝ :=
  ∑' w, thresholdTerm A a j w

theorem threshold_summable (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    Summable (thresholdTerm A a j) := by
  apply ((mass_summable A hs j).mul_left (digit a + s)).of_norm_bounded
  intro w
  have hd : 0 ≤ digit a := by dsimp [digit]; positivity
  have hst : 0 ≤ (s : ℝ) * tag w := mul_nonneg (Nat.cast_nonneg s) (tag_nonneg w)
  have hst' : (s : ℝ) * tag w ≤ s := mul_le_of_le_one_right (Nat.cast_nonneg s) (tag_lt_one w).le
  have ha : |digit a - (s : ℝ) * tag w| ≤ digit a + s := by
    have h := abs_sub (digit a) ((s : ℝ) * tag w)
    rw [abs_of_nonneg hd,abs_of_nonneg hst] at h
    linarith
  rw [Real.norm_eq_abs,thresholdTerm,abs_mul,abs_abs,
    abs_of_nonneg (massTerm_nonneg A hs j w)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left ha (massTerm_nonneg A hs j w)

def headConstant (a b : Fin s) : ℝ := base s * digit a - (s : ℝ) * digit b

theorem headConstant_self (a : Fin s) : headConstant a a = digit a := by
  dsimp [headConstant,base]
  ring

theorem threshold_cons_same (a : Fin s) (w : Word s) :
    |digit a - (s : ℝ) * tag (a :: w)| =
      |digit a - (s : ℝ) * tag w| / base s := by
  rw [tag_cons]
  have h : digit a - (s : ℝ) * (((a.val : ℝ) + 1 + tag w) / base s) =
      (digit a - (s : ℝ) * tag w) / base s := by
    dsimp [digit,base]
    field_simp [(base_pos s).ne']
    ring
  rw [h,abs_div,abs_of_pos (base_pos s)]

theorem threshold_cons_lt (a b : Fin s) (hba : b < a) (w : Word s) :
    |digit a - (s : ℝ) * tag (b :: w)| =
      (headConstant a b - (s : ℝ) * tag w) / base s := by
  have hs0 : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hba' : digit b + 1 ≤ digit a := by
    dsimp [digit]
    have h : (b.val : ℝ) + 1 ≤ (a.val : ℝ) := by exact_mod_cast hba
    linarith
  have hd : 0 < digit a := by dsimp [digit]; positivity
  have hC : 0 ≤ headConstant a b - (s : ℝ) * tag w := by
    have hm := mul_le_mul_of_nonneg_left hba' hs0
    have ht := mul_le_of_le_one_right hs0 (tag_lt_one w).le
    dsimp [headConstant,base]
    nlinarith
  have h : digit a - (s : ℝ) * tag (b :: w) =
      (headConstant a b - (s : ℝ) * tag w) / base s := by
    rw [tag_cons]
    dsimp [headConstant,digit]
    field_simp [(base_pos s).ne']
    ring
  rw [h,abs_of_nonneg (div_nonneg hC (base_pos s).le)]

theorem threshold_cons_gt (a b : Fin s) (hab : a < b) (w : Word s) :
    |digit a - (s : ℝ) * tag (b :: w)| =
      ((s : ℝ) * tag w - headConstant a b) / base s := by
  have hs0 : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hab' : digit a + 1 ≤ digit b := by
    dsimp [digit]
    have h : (a.val : ℝ) + 1 ≤ (b.val : ℝ) := by exact_mod_cast hab
    linarith
  have hd : digit a ≤ (s : ℝ) := by dsimp [digit]; exact_mod_cast a.isLt
  have hC : headConstant a b - (s : ℝ) * tag w ≤ 0 := by
    have hm := mul_le_mul_of_nonneg_left hab' hs0
    have ht := mul_nonneg hs0 (tag_nonneg w)
    dsimp [headConstant,base]
    nlinarith
  have h : digit a - (s : ℝ) * tag (b :: w) =
      (headConstant a b - (s : ℝ) * tag w) / base s := by
    rw [tag_cons]
    dsimp [headConstant,digit]
    field_simp [(base_pos s).ne']
    ring
  rw [h,abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hC (base_pos s).le)]
  ring

def headMoment (A : Data s m) (a b : Fin s) (k : Fin m) : ℝ :=
  if b < a then headConstant a b * mass A k - (s : ℝ) * first A k
  else if a < b then (s : ℝ) * first A k - headConstant a b * mass A k
  else thresholdMoment A a k

theorem head_term_sum (A : Data s m) (hs : 0 < s) (a b : Fin s) (k : Fin m) :
    (∑' w, massTerm A k w * |digit a - (s : ℝ) * tag (b :: w)|) =
      headMoment A a b k / base s := by
  rcases lt_trichotomy b a with hba | hba | hab
  · simp_rw [threshold_cons_lt a b hba]
    rw [headMoment,if_pos hba]
    have he (w : Word s) : massTerm A k w * ((headConstant a b - (s : ℝ) * tag w) / base s) =
        (headConstant a b * massTerm A k w - (s : ℝ) * firstTerm A k w) / base s := by
      dsimp [firstTerm]
      ring
    simp_rw [he]
    rw [tsum_div_const,Summable.tsum_sub ((mass_summable A hs k).mul_left _)
      ((first_summable A hs k).mul_left _),tsum_mul_left,tsum_mul_left]
    rfl
  · subst b
    simp_rw [threshold_cons_same]
    simp only [headMoment,lt_self_iff_false,if_false]
    change (∑' w, massTerm A k w * (|digit a - (s : ℝ) * tag w| / base s)) =
      (∑' w, thresholdTerm A a k w) / base s
    rw [← tsum_div_const]
    apply tsum_congr
    intro w
    dsimp [thresholdTerm]
    ring
  · simp_rw [threshold_cons_gt a b hab]
    rw [headMoment,if_neg (not_lt_of_gt hab),if_pos hab]
    have he (w : Word s) : massTerm A k w * (((s : ℝ) * tag w - headConstant a b) / base s) =
        ((s : ℝ) * firstTerm A k w - headConstant a b * massTerm A k w) / base s := by
      dsimp [firstTerm]
      ring
    simp_rw [he]
    rw [tsum_div_const,Summable.tsum_sub ((first_summable A hs k).mul_left _)
      ((mass_summable A hs k).mul_left _),tsum_mul_left,tsum_mul_left]
    rfl

theorem head_term_summable (A : Data s m) (hs : 0 < s) (a b : Fin s) (k : Fin m) :
    Summable (fun w => massTerm A k w * |digit a - (s : ℝ) * tag (b :: w)|) := by
  apply ((mass_summable A hs k).mul_left (digit a + s)).of_norm_bounded
  intro w
  have hd : 0 ≤ digit a := by dsimp [digit]; positivity
  have hst : 0 ≤ (s : ℝ) * tag (b :: w) := mul_nonneg (Nat.cast_nonneg s) (tag_nonneg _)
  have hst' : (s : ℝ) * tag (b :: w) ≤ s := mul_le_of_le_one_right (Nat.cast_nonneg s) (tag_lt_one _).le
  have ha : |digit a - (s : ℝ) * tag (b :: w)| ≤ digit a + s := by
    have h := abs_sub (digit a) ((s : ℝ) * tag (b :: w))
    rw [abs_of_nonneg hd,abs_of_nonneg hst] at h
    linarith
  rw [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (massTerm_nonneg A hs k w)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left ha (massTerm_nonneg A hs k w)

theorem threshold_recurrence (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    thresholdMoment A a j = digit a * (1 + A.f j) +
      rho s / base s * ∑ b, ∑ k, A.P b j k * headMoment A a b k := by
  rw [thresholdMoment,tsum_words _ (threshold_summable A hs a j)]
  have hnil : thresholdTerm A a j [] = digit a * (1 + A.f j) := by
    simp only [thresholdTerm,massTerm_nil,tag_nil,mul_zero,sub_zero,
      abs_of_nonneg (by dsimp [digit]; positivity : 0 ≤ digit a)]
    ring
  rw [hnil,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  have hterm (w : Word s) : thresholdTerm A a j (b :: w) =
      rho s * ∑ k, A.P b j k * (massTerm A k w * |digit a - (s : ℝ) * tag (b :: w)|) := by
    rw [thresholdTerm,massTerm_cons,Finset.mul_sum,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hterm]
  rw [tsum_mul_left,sum_states_tsum _ _ (head_term_summable A hs a b)]
  simp_rw [head_term_sum A hs a b]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring


def offHeadMoment (A : Data s m) (a b : Fin s) (k : Fin m) : ℝ :=
  if b < a then headConstant a b * mass A k - (s : ℝ) * first A k
  else if a < b then (s : ℝ) * first A k - headConstant a b * mass A k
  else 0

theorem headMoment_split (A : Data s m) (a b : Fin s) (k : Fin m) :
    headMoment A a b k = (if b = a then thresholdMoment A a k else 0) + offHeadMoment A a b k := by
  rcases lt_trichotomy b a with h | h | h
  · simp [headMoment,offHeadMoment,h,ne_of_lt h]
  · subst b; simp [headMoment,offHeadMoment]
  · simp [headMoment,offHeadMoment,h,not_lt_of_gt h,ne_of_gt h]

def thresholdSource (A : Data s m) (a : Fin s) (j : Fin m) : ℝ :=
  digit a * (1 + A.f j) + rho s / base s * ∑ b, ∑ k, A.P b j k * offHeadMoment A a b k

theorem threshold_matrix_recurrence (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    thresholdMoment A a j = thresholdSource A a j +
      ∑ k, (rho s / base s * A.P a j k) * thresholdMoment A a k := by
  rw [threshold_recurrence A hs a j]
  simp_rw [headMoment_split,mul_add,Finset.sum_add_distrib]
  have hsingle : (∑ b, ∑ k, A.P b j k * (if b = a then thresholdMoment A a k else 0)) =
      ∑ k, A.P a j k * thresholdMoment A a k := by
    simp_rw [mul_ite,mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp
  rw [hsingle]
  dsimp [thresholdSource]
  rw [mul_add,Finset.mul_sum]
  have he : (∑ k, rho s / base s * (A.P a j k * thresholdMoment A a k)) =
      ∑ k, (rho s / base s * A.P a j k) * thresholdMoment A a k := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  ring

def digitQ (a : Fin s) : ℚ := (a.val : ℚ) + 1
def headConstantQ (a b : Fin s) : ℚ := baseQ s * digitQ a - (s : ℚ) * digitQ b

@[simp] theorem cast_digitQ (a : Fin s) : (digitQ a : ℝ) = digit a := by simp [digitQ,digit]
@[simp] theorem cast_headConstantQ (a b : Fin s) : (headConstantQ a b : ℝ) = headConstant a b := by
  simp [headConstantQ,headConstant]

def offHeadMomentQ (A : RationalData s m) (a b : Fin s) (k : Fin m) : ℚ :=
  if b < a then headConstantQ a b * massQ A k - (s : ℚ) * firstQ A k
  else if a < b then (s : ℚ) * firstQ A k - headConstantQ a b * massQ A k
  else 0

def thresholdSourceQ (A : RationalData s m) (a : Fin s) (j : Fin m) : ℚ :=
  digitQ a * (1 + A.f j) + rhoQ s / baseQ s * ∑ b, ∑ k, A.P b j k * offHeadMomentQ A a b k

def thresholdMatrix (A : RationalData s m) (a : Fin s) : Matrix (Fin m) (Fin m) ℚ :=
  fun j k => rhoQ s / baseQ s * A.P a j k

def thresholdMomentQ (A : RationalData s m) (a : Fin s) : Fin m → ℚ :=
  RationalSystems.rationalSolution (thresholdMatrix A a) (thresholdSourceQ A a)

theorem cast_offHeadMomentQ (A : RationalData s m) (hs : 0 < s) (a b : Fin s) (k : Fin m) :
    (offHeadMomentQ A a b k : ℝ) = offHeadMoment A.toReal a b k := by
  have hm : mass A.toReal k = (massQ A k : ℝ) := congrFun (mass_eq_rational A hs) k
  have hx : first A.toReal k = (firstQ A k : ℝ) := congrFun (first_eq_rational A hs) k
  simp only [offHeadMomentQ,offHeadMoment,hm,hx]
  split_ifs <;> simp only [Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_zero,cast_headConstantQ]

theorem cast_thresholdSourceQ (A : RationalData s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    (thresholdSourceQ A a j : ℝ) = thresholdSource A.toReal a j := by
  simp only [thresholdSourceQ,thresholdSource,Rat.cast_add,Rat.cast_mul,Rat.cast_sum,Rat.cast_div,
    Rat.cast_one,cast_digitQ,cast_rhoQ,cast_baseQ,cast_offHeadMomentQ A hs]
  rfl

theorem thresholdMatrix_row (A : RationalData s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    (∑ k, |(thresholdMatrix A a j k : ℝ)|) ≤ 1 / 4 := by
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hrho : rho s ≤ 1 / 4 := by
    dsimp [rho]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * s) (by norm_num : (0 : ℝ) < 4)).2
    linarith
  have hbase : 1 ≤ base s := by dsimp [base]; linarith
  have hquot : rho s / base s ≤ rho s := (div_le_self (rho_pos hs).le hbase)
  have hnonneg (k : Fin m) : 0 ≤ (thresholdMatrix A a j k : ℝ) := by
    simp only [thresholdMatrix,Rat.cast_mul,Rat.cast_div,cast_rhoQ,cast_baseQ]
    exact mul_nonneg (div_nonneg (rho_pos hs).le (base_pos s).le)
      (by exact_mod_cast A.P_nonneg a j k)
  simp_rw [abs_of_nonneg (hnonneg _)]
  simp only [thresholdMatrix,Rat.cast_mul,Rat.cast_div,cast_rhoQ,cast_baseQ,← Finset.mul_sum]
  have hr : ∑ k, (A.P a j k : ℝ) = 1 := by exact_mod_cast A.P_sum a j
  rw [hr,mul_one]
  exact hquot.trans hrho

/-- The absolute moments introduced by the identity/letter reference pairs
are all explicit rational finite-system solutions. -/
theorem threshold_eq_rational (A : RationalData s m) (hs : 0 < s) (a : Fin s) :
    thresholdMoment A.toReal a = RationalSystems.castVector (thresholdMomentQ A a) := by
  apply RationalSystems.real_solution_is_rational (thresholdMatrix A a) (thresholdSourceQ A a)
    (1 / 4) (by norm_num) (by norm_num) (thresholdMatrix_row A hs a)
  funext j
  rw [threshold_matrix_recurrence A.toReal hs a j]
  change _ = (thresholdSourceQ A a j : ℝ) +
    ∑ k, (thresholdMatrix A a j k : ℝ) * thresholdMoment A.toReal a k
  rw [cast_thresholdSourceQ A hs]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [thresholdMatrix,Rat.cast_mul,Rat.cast_div,cast_rhoQ,cast_baseQ]
  rfl

def referenceNormal (a : Fin s) : AutomatonWords.Plane →L[ℝ] ℝ :=
  digit a • ContinuousLinearMap.snd ℝ ℝ ℝ - (s : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ

@[simp] theorem referenceNormal_apply (a : Fin s) (x : AutomatonWords.Plane) :
    referenceNormal a x = digit a * x.2 - (s : ℝ) * x.1 := rfl

theorem referenceNormal_weighted (A : Data s m) (a : Fin s) (j : Fin m) (w : Word s) :
    referenceNormal a (A.weight w j • generator w) =
      massTerm A j w * (digit a - (s : ℝ) * tag w) := by
  rw [weighted_generator]
  rw [referenceNormal_apply]
  dsimp [firstTerm]
  ring

theorem threshold_width (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    ReferenceExpansion.linearWidth (referenceNormal a) (stateBody A hs j) = thresholdMoment A a j := by
  rw [stateBody,linearWidth_series hs]
  simp_rw [referenceNormal_weighted,abs_mul,abs_of_nonneg (massTerm_nonneg A hs j _)]
  rfl

end MixedVolume.ReferenceMoments

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/ReferenceMoments.lean -/

/- BEGIN SOURCE: MixedVolume/General/VolumeLocus.lean -/
section


/-! The exact full ordinary coefficient array in the paper's realization
locus, with the stated number of bodies. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralLocus

open VolumePolynomials AutomatonWords GeneralLabels GeneralTarget GeneralDeficit GeneralRealization
open MvPolynomial
open scoped BigOperators

variable {s m : ℕ}

def numberOfBodies (s m : ℕ) : ℕ := (s+1)*m+s+5

def labelEquiv (s m : ℕ) : Label s m ≃ Fin (numberOfBodies s m) :=
  (Fintype.equivFin (Label s m)).trans (finCongr (card_labels s m))

def polynomial (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ) (theta : ℝ) :
    MvPolynomial (Fin (numberOfBodies s m)) ℝ :=
  MvPolynomial.rename (labelEquiv s m) (targetPolynomial A hs (targetDelta A p theta))

theorem polynomial_homogeneous (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ) (theta : ℝ) :
    (polynomial A hs p theta).IsHomogeneous 3 :=
  (targetPolynomial_homogeneous A hs (targetDelta A p theta)).rename_isHomogeneous

def coefficientArray (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ) (theta : ℝ) :
    Coefficients (numberOfBodies s m) 3 := coefficientsOfPolynomial (polynomial A hs p theta)

theorem evaluate_coefficientArray (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ) (theta : ℝ)
    (w : Fin (numberOfBodies s m) → ℝ) :
    evaluate (coefficientArray A hs p theta) w =
      MvPolynomial.eval (w ∘ labelEquiv s m) (targetPolynomial A hs (targetDelta A p theta)) := by
  rw [coefficientArray,evaluate_eq_polynomial_eval,
    coefficientPolynomial_coefficientsOfPolynomial _ (polynomial_homogeneous A hs p theta),
    polynomial,MvPolynomial.eval_rename]

theorem sumBody_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (K : κ → Body 3) (w : κ → ℝ) :
    sumBody (K ∘ e) (w ∘ e) = sumBody K w := e.sum_comp (fun i => w i • K i)

theorem coefficientArray_mem_iff_target (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ) (theta : ℝ) :
    coefficientArray A hs p theta ∈ VolumeLocus (numberOfBodies s m) 3 ↔
      ∃ K : Label s m → Body 3, RealizesTarget A hs (targetDelta A p theta) K := by
  rw [mem_volumeLocus]
  constructor
  · rintro ⟨K,hK⟩
    refine ⟨K ∘ labelEquiv s m,?_⟩
    intro w hw
    have h := hK (w ∘ (labelEquiv s m).symm) (fun i => hw _)
    rw [evaluate_coefficientArray] at h
    have hf : (w ∘ (labelEquiv s m).symm) ∘ labelEquiv s m = w := by ext i; simp
    rw [hf] at h
    rw [h]
    change bodyVolume (sumBody K (w ∘ (labelEquiv s m).symm)) = _
    congr 1
    have hr := sumBody_reindex (labelEquiv s m) K (w ∘ (labelEquiv s m).symm)
    rw [hf] at hr
    exact hr.symm
  · rintro ⟨K,hK⟩
    refine ⟨K ∘ (labelEquiv s m).symm,?_⟩
    intro w hw
    rw [evaluate_coefficientArray,hK (w ∘ labelEquiv s m) (fun i => hw _)]
    change bodyVolume (sumBody K (w ∘ labelEquiv s m)) = bodyVolume (sumBody (K ∘ (labelEquiv s m).symm) w)
    congr 1
    have hr := sumBody_reindex (labelEquiv s m).symm K (w ∘ labelEquiv s m)
    simpa [Function.comp_def] using hr.symm

/-- The full ordinary cubic array has exactly the required geometric
realizability condition, with no restrictions on words or on real parameters. -/
theorem coefficientArray_mem_iff (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ)
    (hp : ProbabilityRow p) (theta : ℝ) (htheta₀ : 0 < theta) (htheta₁ : theta < 1) :
    coefficientArray A hs p theta ∈ VolumeLocus (numberOfBodies s m) 3 ↔
      A.UniversalCutpoint p theta := by
  rw [coefficientArray_mem_iff_target,realization_iff_cutpoint A hs p hp theta htheta₀ htheta₁]

@[simp] theorem seven_state_four_letter_count : numberOfBodies 4 7 = 44 := by decide
@[simp] theorem twenty_eight_state_binary_count : numberOfBodies 2 28 = 91 := by decide

end MixedVolume.GeneralLocus

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/VolumeLocus.lean -/

/- BEGIN SOURCE: MixedVolume/General/Interpolation.lean -/
section


/-! Exact rational extraction of the complete cubic coefficient array.
This is the already recovered interpolation construction, reused in the
isolated general mixed-volume dependency chain. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset Polynomial VolumePolynomials
open scoped BigOperators
namespace MixedVolume.RationalExtraction

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

end MixedVolume.RationalExtraction
end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/Interpolation.lean -/

/- BEGIN SOURCE: MixedVolume/General/ReferenceRecursion.lean -/
section


/-! A finite arithmetic algorithm for adjoining all reference segments.
Its three registers are the genuine volume, projected areas, and pair widths.
Every update follows from the actual extrusion formula. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.ReferenceRecursion

open VolumePolynomials VolumePolynomials.Holonomy GeneralLabels GeneralCalibration GeneralForcing
open ReferenceExpansion Set MeasureTheory
open scoped BigOperators Pointwise

abbrev Plane := AutomatonWords.Plane
variable {s : ℕ}

def projection : Reference s → Space 3 →L[ℝ] Plane
  | .inl i => coordinateProjection i
  | .inr (.inl a) => projectionLetter a
  | .inr (.inr _) => projectionIdentity

def pairFunctional (i j : Reference s) : Space 3 →L[ℝ] ℝ :=
  (determinantFunctional (projection j (GeneralLabels.referenceDirection i))).comp (projection j)

def directionQ : Reference s → (Fin 3 → ℚ)
  | .inl i => Pi.single i 1
  | .inr (.inl a) => ![-((a.val : ℚ)+1),-((s : ℚ)+1),1]
  | .inr (.inr _) => ![0,-1,1]

def projectionQ : Reference s → (Fin 3 → ℚ) → ℚ × ℚ
  | .inl i, x => (x (i.succAbove 0),x (i.succAbove 1))
  | .inr (.inl a), x => (x 0 + ((a.val : ℚ)+1)*x 2,x 1 + ((s : ℚ)+1)*x 2)
  | .inr (.inr _), x => (x 0,x 1+x 2)

def tripleQ (i j k : Reference s) : ℚ :=
  let u := projectionQ j (directionQ i)
  let v := projectionQ j (directionQ k)
  |u.1*v.2-u.2*v.1|

theorem cast_directionQ (i : Reference s) (k : Fin 3) :
    (directionQ i k : ℝ) = GeneralLabels.referenceDirection i k := by
  rcases i with i | a | u
  · by_cases h : k = i <;>
      simp [directionQ,GeneralLabels.referenceDirection,axis,Pi.single_apply,h]
  · fin_cases k <;> simp [directionQ,GeneralLabels.referenceDirection,letterDirection,AutomatonWords.base]
  · fin_cases k <;> simp [directionQ,GeneralLabels.referenceDirection,identityDirection]

theorem cast_projectionQ (i : Reference s) (x : Fin 3 → ℚ) :
    ((projectionQ i x).1 : ℝ) = (projection i (fun k => (x k : ℝ))).1 ∧
    ((projectionQ i x).2 : ℝ) = (projection i (fun k => (x k : ℝ))).2 := by
  rcases i with i | a | u
  · simp [projectionQ,projection,coordinateProjection_apply]
  · simp [projectionQ,projection,projectionLetter_apply,AutomatonWords.base]
  · simp [projectionQ,projection,projectionIdentity_apply]

theorem cast_tripleQ (i j k : Reference s) :
    (tripleQ i j k : ℝ) = |pairFunctional i j (GeneralLabels.referenceDirection k)| := by
  simp only [tripleQ,Rat.cast_abs,Rat.cast_sub,Rat.cast_mul,
    (cast_projectionQ j (directionQ i)).1,(cast_projectionQ j (directionQ i)).2,
    (cast_projectionQ j (directionQ k)).1,(cast_projectionQ j (directionQ k)).2,cast_directionQ]
  rfl

theorem reference_extrusion (K : Body 3) (i : Reference s) :
    bodyVolume (K + centeredBody (GeneralLabels.referenceDirection i)) - bodyVolume K =
      projectionArea (projection i) K := by
  rcases i with i | a | u
  · exact bodyExtrusion_axis K i
  · exact extrusion_letter a K
  · exact extrusion_identity K

theorem volume_add_reference (K : Body 3) (i : Reference s) {r : ℝ} (hr : 0 ≤ r) :
    bodyVolume (K + r • centeredBody (GeneralLabels.referenceDirection i)) =
      bodyVolume K + r * projectionArea (projection i) K := by
  have h := bodyVolume_add_smul_segment K (-(1/2 : ℝ) • GeneralLabels.referenceDirection i)
    ((1/2 : ℝ) • GeneralLabels.referenceDirection i) hr
  change bodyVolume (K + r • centeredBody (GeneralLabels.referenceDirection i)) =
    bodyVolume K + r * (bodyVolume (K + centeredBody (GeneralLabels.referenceDirection i)) - bodyVolume K) at h
  rw [reference_extrusion] at h
  exact h

@[ext] structure Stats (R : Type*) (s : ℕ) where
  volume : R
  area : Reference s → R
  width : Reference s → Reference s → R

def actualStats (K : Body 3) : Stats ℝ s where
  volume := bodyVolume K
  area i := projectionArea (projection i) K
  width i j := linearWidth (pairFunctional i j) K

def step {R : Type*} [Semiring R] (D : Reference s → Reference s → Reference s → R)
    (u : R) (j : Reference s) (z : Stats R s) : Stats R s where
  volume := z.volume + u*z.area j
  area i := z.area i + u*z.width j i
  width i k := z.width i k + u*D i k j

def castStats (z : Stats ℚ s) : Stats ℝ s where
  volume := z.volume
  area i := z.area i
  width i j := z.width i j

theorem actualStats_step (K : Body 3) (j : Reference s) {u : ℝ} (hu : 0 ≤ u) :
    actualStats (K + u • centeredBody (GeneralLabels.referenceDirection j)) =
      step (fun i k l => (tripleQ i k l : ℝ)) u j (actualStats K) := by
  apply Stats.ext
  · exact volume_add_reference K j hu
  · funext i
    exact projectionArea_add_segment (projection i) K (GeneralLabels.referenceDirection j) hu
  · funext i k
    change linearWidth (pairFunctional i k) (K + u • centeredBody (GeneralLabels.referenceDirection j)) = _
    rw [linearWidth_add_smul_centeredBody _ _ _ hu]
    simp only [step,actualStats,cast_tripleQ]

theorem castStats_step (z : Stats ℚ s) (u : ℚ) (j : Reference s) :
    castStats (step tripleQ u j z) =
      step (fun i k l => (tripleQ i k l : ℝ)) (u : ℝ) j (castStats z) := by
  apply Stats.ext
  · simp [castStats,step]
  · funext i; simp [castStats,step]
  · funext i k; simp [castStats,step]

def run {R : Type*} [Semiring R] (D : Reference s → Reference s → Reference s → R)
    (u : Reference s → R) (z : Stats R s) : List (Reference s) → Stats R s
  | [] => z
  | j :: rest => run D u (step D (u j) j z) rest

def addReferences (K : Body 3) (u : Reference s → ℝ) : List (Reference s) → Body 3
  | [] => K
  | j :: rest => addReferences (K + u j • centeredBody (GeneralLabels.referenceDirection j)) u rest

theorem actualStats_run (K : Body 3) (u : Reference s → ℝ) (hu : ∀ j, 0 ≤ u j)
    (refs : List (Reference s)) :
    actualStats (addReferences K u refs) =
      run (fun i k l => (tripleQ i k l : ℝ)) u (actualStats K) refs := by
  induction refs generalizing K with
  | nil => rfl
  | cons j refs ih => rw [addReferences,ih,actualStats_step _ _ (hu j),run]

theorem castStats_run (z : Stats ℚ s) (u : Reference s → ℚ) (refs : List (Reference s)) :
    castStats (run tripleQ u z refs) =
      run (fun i k l => (tripleQ i k l : ℝ)) (fun j => (u j : ℝ)) (castStats z) refs := by
  induction refs generalizing z with
  | nil => rfl
  | cons j refs ih => rw [run,run,ih,castStats_step]

theorem addReferences_eq_sum (K : Body 3) (u : Reference s → ℝ) (refs : List (Reference s)) :
    addReferences K u refs = K + (refs.map (fun j => u j • centeredBody (GeneralLabels.referenceDirection j))).sum := by
  induction refs generalizing K with
  | nil => simp [addReferences]
  | cons j refs ih => simp only [addReferences,ih,List.map_cons,List.sum_cons,add_assoc]

/-- Exact finite rational evaluation once the planar starting moments are
supplied, for arbitrary alphabet size and all nonnegative rational weights. -/
theorem rational_volume_after_references (K : Body 3) (z : Stats ℚ s)
    (hz : actualStats K = castStats z) (u : Reference s → ℚ) (hu : ∀ j, 0 ≤ u j)
    (refs : List (Reference s)) :
    bodyVolume (addReferences K (fun j => (u j : ℝ)) refs) =
      ((run tripleQ u z refs).volume : ℝ) := by
  have h := actualStats_run K (fun j => (u j : ℝ)) (fun j => by exact_mod_cast hu j) refs
  rw [hz,← castStats_run] at h
  exact congrArg Stats.volume h

end MixedVolume.ReferenceRecursion

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/ReferenceRecursion.lean -/

/- BEGIN SOURCE: MixedVolume/General/PlanarRational.lean -/
section


/-! Finite rational area and width formulae for all nonnegative combinations
of the state bodies and their transition images. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.PlanarRational

open VolumePolynomials AutomatonWords AutomatonZonoids AutomatonMoments MomentGeometry QuadraticMoments
open VolumePolynomials.PlanarMixedForm Set MeasureTheory Matrix
open scoped BigOperators Pointwise

variable {s m : ℕ}

theorem image_height (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    PlanarCorner.height (mapBody (transition a) (stateBody A hs j)) = rho s * mass A j := by
  rw [stateBody,IndexedSeries.map_segmentSeriesBody]
  change ReferenceExpansion.linearWidth (ContinuousLinearMap.snd ℝ ℝ ℝ) _ = _
  rw [linearWidth_series hs]
  have hterm (w : Word s) :
      |(ContinuousLinearMap.snd ℝ ℝ ℝ) (transition a (A.weight w j • generator w))| =
        rho s * massTerm A j w := by
    rw [weighted_generator]
    change |rho s * massTerm A j w| = _
    exact abs_of_nonneg (mul_nonneg (rho_pos hs).le (massTerm_nonneg A hs j w))
  simp_rw [hterm]
  rw [tsum_mul_left]
  rfl

def imageWidthQ (A : RationalData s m) (a : Fin s) (j : Fin m) : ℚ :=
  rhoQ s / baseQ s * (firstQ A j + ((a.val : ℚ)+1)*massQ A j)

def imageMixedQ (A : RationalData s m) (a b : Fin s) (j k : Fin m) : ℚ :=
  (if a = b then imageFactorQ s * pairMomentQ A (j,k) else 0) + crossMomentQ A a b j k

def stateImageQ (A : RationalData s m) (j : Fin m) (a : Fin s) (k : Fin m) : ℚ :=
  (1+A.f j)*imageWidthQ A a k + ∑ b, ∑ l, A.P b j l * imageMixedQ A b a l k

theorem image_width_rational (A : RationalData s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    PlanarCorner.width (mapBody (transition a) (stateBody A.toReal hs j)) = (imageWidthQ A a j : ℝ) := by
  have hm : mass A.toReal j = (massQ A j : ℝ) := congrFun (mass_eq_rational A hs) j
  have hx : first A.toReal j = (firstQ A j : ℝ) := congrFun (first_eq_rational A hs) j
  rw [image_width]
  simp only [imageWidthQ,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,
    cast_rhoQ,cast_baseQ,hm,hx]

theorem image_mixed_rational (A : RationalData s m) (hs : 0 < s) (a b : Fin s) (j k : Fin m) :
    twiceMixed (mapBody (transition a) (stateBody A.toReal hs j))
      (mapBody (transition b) (stateBody A.toReal hs k)) = (imageMixedQ A a b j k : ℝ) := by
  have hp : pairMoment A.toReal hs (j,k) = (pairMomentQ A (j,k) : ℝ) :=
    congrFun (pairMoment_eq_rational A hs) (j,k)
  rw [image_mixed]
  simp only [imageMixedQ,Rat.cast_add,cast_crossMomentQ A hs]
  congr 1
  split_ifs <;> simp only [Rat.cast_mul,Rat.cast_zero,cast_imageFactorQ,hp]

theorem state_image_rational (A : RationalData s m) (hs : 0 < s) (j : Fin m) (a : Fin s) (k : Fin m) :
    twiceMixed (stateBody A.toReal hs j) (mapBody (transition a) (stateBody A.toReal hs k)) =
      (stateImageQ A j a k : ℝ) := by
  rw [state_left_expansion,image_width_rational]
  simp only [stateImageQ,Rat.cast_add,Rat.cast_mul,Rat.cast_one,Rat.cast_sum,image_mixed_rational A hs]
  rfl

abbrev Primitive (s m : ℕ) := Fin m ⊕ (Fin s × Fin m)

def primitiveBody (A : Data s m) (hs : 0 < s) : Primitive s m → ConvexBody Plane
  | .inl j => stateBody A hs j
  | .inr (a,j) => mapBody (transition a) (stateBody A hs j)

def heightQ (A : RationalData s m) : Primitive s m → ℚ
  | .inl j => massQ A j
  | .inr (_,j) => rhoQ s * massQ A j

def widthQ (A : RationalData s m) : Primitive s m → ℚ
  | .inl j => firstQ A j
  | .inr (a,j) => imageWidthQ A a j

def mixedQ (A : RationalData s m) : Primitive s m → Primitive s m → ℚ
  | .inl j, .inl k => pairMomentQ A (j,k)
  | .inl j, .inr (a,k) => stateImageQ A j a k
  | .inr (a,j), .inl k => stateImageQ A k a j
  | .inr (a,j), .inr (b,k) => imageMixedQ A a b j k

theorem primitive_height (A : RationalData s m) (hs : 0 < s) (i : Primitive s m) :
    PlanarCorner.height (primitiveBody A.toReal hs i) = (heightQ A i : ℝ) := by
  have hm (j : Fin m) : mass A.toReal j = (massQ A j : ℝ) :=
    congrFun (mass_eq_rational A hs) j
  rcases i with j | ⟨a,j⟩
  · exact (state_height A.toReal hs j).trans (hm j)
  · rw [primitiveBody,image_height]
    simp only [heightQ,Rat.cast_mul,cast_rhoQ,hm]

theorem primitive_width (A : RationalData s m) (hs : 0 < s) (i : Primitive s m) :
    PlanarCorner.width (primitiveBody A.toReal hs i) = (widthQ A i : ℝ) := by
  rcases i with j | ⟨a,j⟩
  · exact (state_width A.toReal hs j).trans (congrFun (first_eq_rational A hs) j)
  · exact image_width_rational A hs a j

theorem primitive_mixed (A : RationalData s m) (hs : 0 < s) (i j : Primitive s m) :
    twiceMixed (primitiveBody A.toReal hs i) (primitiveBody A.toReal hs j) = (mixedQ A i j : ℝ) := by
  rcases i with i | ⟨a,i⟩ <;> rcases j with j | ⟨b,j⟩
  · exact congrFun (pairMoment_eq_rational A hs) (i,j)
  · exact state_image_rational A hs i b j
  · rw [twiceMixed_symm]; exact state_image_rational A hs j a i
  · exact image_mixed_rational A hs a b i j

def combination (A : Data s m) (hs : 0 < s) (b : Primitive s m → ℝ) : ConvexBody Plane :=
  ∑ i, b i • primitiveBody A hs i

def combinationHeightQ (A : RationalData s m) (b : Primitive s m → ℚ) : ℚ := ∑ i, b i*heightQ A i
def combinationWidthQ (A : RationalData s m) (b : Primitive s m → ℚ) : ℚ := ∑ i, b i*widthQ A i
def combinationMixedQ (A : RationalData s m) (b c : Primitive s m → ℚ) : ℚ :=
  ∑ i, ∑ j, b i*c j*mixedQ A i j

def combinationAreaQ (A : RationalData s m) (b : Primitive s m → ℚ) : ℚ :=
  combinationMixedQ A b b / 2

theorem combination_mixed (A : RationalData s m) (hs : 0 < s) (b c : Primitive s m → ℚ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    twiceMixed (combination A.toReal hs (fun i => (b i : ℝ)))
      (combination A.toReal hs (fun i => (c i : ℝ))) = (combinationMixedQ A b c : ℝ) := by
  rw [combination,combination,twiceMixed_sum_left]
  simp_rw [twiceMixed_sum_right]
  simp_rw [twiceMixed_smul_left _ _ (show (0 : ℝ) ≤ (b _ : ℝ) from by exact_mod_cast hb _),
    twiceMixed_smul_right _ _ (show (0 : ℝ) ≤ (c _ : ℝ) from by exact_mod_cast hc _),primitive_mixed A hs]
  simp only [combinationMixedQ,Rat.cast_sum,Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem combination_area (A : RationalData s m) (hs : 0 < s) (b : Primitive s m → ℚ)
    (hb : ∀ i, 0 ≤ b i) :
    volume.real (combination A.toReal hs (fun i => (b i : ℝ)) : Set Plane) = (combinationAreaQ A b : ℝ) := by
  have h := combination_mixed A hs b b hb hb
  rw [twiceMixed,mixedArea_diagonal volume PlanarCorner.plane_finrank] at h
  simp only [combinationAreaQ,Rat.cast_div,Rat.cast_ofNat]
  linarith

theorem height_sum {ι : Type*} [Fintype ι] (K : ι → ConvexBody Plane) :
    PlanarCorner.height (∑ i, K i) = ∑ i, PlanarCorner.height (K i) := by
  simp only [← PlanarCorner.twice_mixedArea_unitX,twiceMixed_sum_left]
  simp only [mixedArea_sum_left,Finset.mul_sum]

theorem width_sum {ι : Type*} [Fintype ι] (K : ι → ConvexBody Plane) :
    PlanarCorner.width (∑ i, K i) = ∑ i, PlanarCorner.width (K i) := by
  simp only [← PlanarCorner.twice_mixedArea_unitY,mixedArea_sum_left,Finset.mul_sum]

theorem combination_height (A : RationalData s m) (hs : 0 < s) (b : Primitive s m → ℚ)
    (hb : ∀ i, 0 ≤ b i) :
    PlanarCorner.height (combination A.toReal hs (fun i => (b i : ℝ))) = (combinationHeightQ A b : ℝ) := by
  rw [combination,height_sum]
  simp_rw [PlanarCorner.height_smul _ (show (0 : ℝ) ≤ (b _ : ℝ) from by exact_mod_cast hb _),primitive_height A hs]
  simp only [combinationHeightQ,Rat.cast_sum,Rat.cast_mul]

theorem combination_width (A : RationalData s m) (hs : 0 < s) (b : Primitive s m → ℚ)
    (hb : ∀ i, 0 ≤ b i) :
    PlanarCorner.width (combination A.toReal hs (fun i => (b i : ℝ))) = (combinationWidthQ A b : ℝ) := by
  rw [combination,width_sum]
  simp_rw [PlanarCorner.width_smul _ (show (0 : ℝ) ≤ (b _ : ℝ) from by exact_mod_cast hb _),primitive_width A hs]
  simp only [combinationWidthQ,Rat.cast_sum,Rat.cast_mul]

end MixedVolume.PlanarRational

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/PlanarRational.lean -/

/- BEGIN SOURCE: MixedVolume/General/WidthAlgebra.lean -/
section


/-! Absolute linear moments of the automaton bodies.  Functionals of constant
sign on the tag cone depend only on the first two moments; the exceptional
reference normals use the separately verified threshold resolvent. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.WidthAlgebra

open VolumePolynomials AutomatonWords AutomatonZonoids AutomatonMoments MomentGeometry
open ReferenceMoments ReferenceRecursion ReferenceExpansion Set MeasureTheory
open scoped BigOperators

abbrev Plane := AutomatonWords.Plane
variable {s m : ℕ}

theorem linear_apply (l : Plane →L[ℝ] ℝ) (x y : ℝ) :
    l (x,y) = x*l (1,0) + y*l (0,1) := by
  have h : (x,y) = x • ((1,0) : Plane) + y • ((0,1) : Plane) := by ext <;> simp
  rw [h,map_add,map_smul,map_smul]
  rfl

theorem linear_apply_cone (l : Plane →L[ℝ] ℝ) (x y : ℝ) :
    l (x,y) = x*l (1,1) + (y-x)*l (0,1) := by
  rw [linear_apply l x y,linear_apply l 1 1]
  ring

theorem firstTerm_le_massTerm (A : Data s m) (hs : 0 < s) (j : Fin m) (w : Word s) :
    firstTerm A j w ≤ massTerm A j w :=
  mul_le_of_le_one_right (massTerm_nonneg A hs j w) (tag_lt_one w).le

theorem linear_generator_sum (A : Data s m) (hs : 0 < s) (j : Fin m) (l : Plane →L[ℝ] ℝ) :
    (∑' w, l (A.weight w j • generator w)) = l (first A j,mass A j) := by
  have hterm (w : Word s) : l (A.weight w j • generator w) =
      firstTerm A j w*l (1,0) + massTerm A j w*l (0,1) := by
    rw [weighted_generator,linear_apply l (firstTerm A j w) (massTerm A j w)]
  rw [linear_apply l (first A j) (mass A j)]
  simp_rw [hterm]
  rw [Summable.tsum_add ((first_summable A hs j).mul_right _) ((mass_summable A hs j).mul_right _),
    tsum_mul_right,tsum_mul_right]
  rfl

theorem linearWidth_state_cone (A : Data s m) (hs : 0 < s) (j : Fin m)
    (l : Plane →L[ℝ] ℝ) (hcone : 0 ≤ l (0,1)*l (1,1)) :
    linearWidth l (stateBody A hs j) = |l (first A j,mass A j)| := by
  rw [stateBody,linearWidth_series hs,← linear_generator_sum A hs j l]
  rcases mul_nonneg_iff.mp hcone with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩
  · have hterm (w : Word s) : 0 ≤ l (A.weight w j • generator w) := by
      rw [weighted_generator,linear_apply_cone]
      exact add_nonneg (mul_nonneg (firstTerm_nonneg A hs j w) h₁)
        (mul_nonneg (sub_nonneg.mpr (firstTerm_le_massTerm A hs j w)) h₀)
    simp_rw [abs_of_nonneg (hterm _)]
    rw [abs_of_nonneg (tsum_nonneg hterm)]
  · have hterm (w : Word s) : l (A.weight w j • generator w) ≤ 0 := by
      rw [weighted_generator,linear_apply_cone]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (firstTerm_nonneg A hs j w) h₁)
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (firstTerm_le_massTerm A hs j w)) h₀)
    simp_rw [abs_of_nonpos (hterm _)]
    rw [tsum_neg,abs_of_nonpos (tsum_nonpos hterm)]

theorem linearWidth_neg_state (A : Data s m) (hs : 0 < s) (j : Fin m) (l : Plane →L[ℝ] ℝ) :
    linearWidth (-l) (stateBody A hs j) = linearWidth l (stateBody A hs j) := by
  rw [stateBody,linearWidth_series hs,linearWidth_series hs]
  simp only [ContinuousLinearMap.neg_apply,abs_neg]

theorem linearWidth_neg_image (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m)
    (l : Plane →L[ℝ] ℝ) :
    linearWidth (-l) (mapBody (transition a) (stateBody A hs j)) =
      linearWidth l (mapBody (transition a) (stateBody A hs j)) := by
  rw [linearWidth_map,linearWidth_map]
  change linearWidth (-(l.comp (transition a))) _ = _
  exact linearWidth_neg_state A hs j _

theorem threshold_image_width (A : Data s m) (hs : 0 < s) (a b : Fin s) (j : Fin m) :
    linearWidth (referenceNormal a) (mapBody (transition b) (stateBody A hs j)) =
      rho s / base s * headMoment A a b j := by
  rw [stateBody,IndexedSeries.map_segmentSeriesBody,linearWidth_series hs]
  have hterm (w : Word s) :
      |referenceNormal a (transition b (A.weight w j • generator w))| =
        rho s * (massTerm A j w * |digit a - (s : ℝ)*tag (b::w)|) := by
    have h : referenceNormal a (transition b (A.weight w j • generator w)) =
        rho s * massTerm A j w * (digit a - (s : ℝ)*tag (b::w)) := by
      rw [weighted_generator,transition_apply,referenceNormal_apply,tag_cons]
      dsimp [firstTerm]
      ring
    rw [h,abs_mul,abs_mul,abs_of_pos (rho_pos hs),abs_of_nonneg (massTerm_nonneg A hs j w)]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left,head_term_sum A hs a b j]
  ring

def headMomentQ (A : RationalData s m) (a b : Fin s) (j : Fin m) : ℚ :=
  if b = a then thresholdMomentQ A a j else offHeadMomentQ A a b j

theorem cast_headMomentQ (A : RationalData s m) (hs : 0 < s) (a b : Fin s) (j : Fin m) :
    (headMomentQ A a b j : ℝ) = headMoment A.toReal a b j := by
  rw [headMoment_split]
  by_cases h : b = a
  · subst b
    simp only [headMomentQ,if_true,offHeadMoment,lt_self_iff_false,if_false,add_zero]
    exact (congrFun (threshold_eq_rational A hs a) j).symm
  · simp only [headMomentQ,if_neg h,zero_add,cast_offHeadMomentQ A hs]

end MixedVolume.WidthAlgebra

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/WidthAlgebra.lean -/

/- BEGIN SOURCE: MixedVolume/General/ReferenceWidths.lean -/
section


/-! Every reference-pair width is rational.  Only a letter paired with the
identity reference crosses the tag cone; those pairs use the exact threshold
moments, including their transition-image recurrences. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralWidths

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords AutomatonZonoids AutomatonMoments
open GeneralLabels GeneralCalibration ReferenceRecursion ReferenceExpansion ReferenceMoments WidthAlgebra
open Set MeasureTheory
open scoped BigOperators

abbrev Plane := AutomatonWords.Plane
variable {s m : ℕ}

def coordinate (i : Fin 3) : Space 3 →L[ℝ] ℝ := ContinuousLinearMap.proj i

def detFunctional (u v : Space 3) : Space 3 →L[ℝ] ℝ :=
  (u 1*v 2-u 2*v 1) • coordinate 0 + (u 2*v 0-u 0*v 2) • coordinate 1 +
    (u 0*v 1-u 1*v 0) • coordinate 2

theorem detFunctional_apply (u v x : Space 3) : detFunctional u v x = determinant3 u v x := by
  change (u 1*v 2-u 2*v 1)*x 0 + (u 2*v 0-u 0*v 2)*x 1 +
    (u 0*v 1-u 1*v 0)*x 2 = _
  dsimp [determinant3]
  ring

def orientedPair (i j : Reference s) : Space 3 →L[ℝ] ℝ :=
  detFunctional (GeneralLabels.referenceDirection i) (GeneralLabels.referenceDirection j)

theorem orientedPair_swap (i j : Reference s) : orientedPair j i = -orientedPair i j := by
  ext x
  simp only [orientedPair,ContinuousLinearMap.neg_apply,detFunctional_apply,determinant3]
  ring

theorem pairFunctional_oriented (i j : Reference s) :
    pairFunctional i j = if j = axisRef 1 then orientedPair i j else -orientedPair i j := by
  rcases j with j | a | u
  · fin_cases j <;> ext x <;>
      simp [pairFunctional,projection,orientedPair,detFunctional_apply,determinant3,
        GeneralLabels.referenceDirection,axis,axisRef,coordinateProjection_apply,
        determinantFunctional_apply,Pi.single_apply] <;> ring
  · ext x
    simp [pairFunctional,projection,orientedPair,detFunctional_apply,determinant3,
      GeneralLabels.referenceDirection,letterDirection,axisRef,GeneralForcing.projectionLetter_apply,
      determinantFunctional_apply]
    ring
  · ext x
    simp [pairFunctional,projection,orientedPair,detFunctional_apply,determinant3,
      GeneralLabels.referenceDirection,identityDirection,axisRef,GeneralForcing.projectionIdentity_apply,
      determinantFunctional_apply]
    ring

theorem pair_state_oriented (A : Data s m) (hs : 0 < s) (k : Fin m) (i j : Reference s) :
    linearWidth ((pairFunctional i j).comp embedXZ) (stateBody A hs k) =
      linearWidth ((orientedPair i j).comp embedXZ) (stateBody A hs k) := by
  rw [pairFunctional_oriented]
  split_ifs
  · rfl
  · change linearWidth (-((orientedPair i j).comp embedXZ)) _ = _
    exact linearWidth_neg_state A hs k _

theorem pair_image_oriented (A : Data s m) (hs : 0 < s) (a : Fin s) (k : Fin m) (i j : Reference s) :
    linearWidth ((pairFunctional i j).comp embedXY) (mapBody (transition a) (stateBody A hs k)) =
      linearWidth ((orientedPair i j).comp embedXY) (mapBody (transition a) (stateBody A hs k)) := by
  rw [pairFunctional_oriented]
  split_ifs
  · rfl
  · change linearWidth (-((orientedPair i j).comp embedXY)) _ = _
    exact linearWidth_neg_image A hs a k _

def exceptional : Reference s → Reference s → Bool
  | .inr (.inl _), .inr (.inr _) => true
  | .inr (.inr _), .inr (.inl _) => true
  | _, _ => false

theorem oriented_product_swap (i j : Reference s) (x y : Space 3) :
    orientedPair j i x * orientedPair j i y = orientedPair i j x * orientedPair i j y := by
  rw [orientedPair_swap]
  simp only [ContinuousLinearMap.neg_apply,neg_mul_neg]

theorem axis_state_cone (i : Fin 3) (j : Reference s) :
    0 ≤ orientedPair (axisRef i) j (embedXZ (0,1)) * orientedPair (axisRef i) j (embedXZ (1,1)) := by
  rcases j with j | a | u
  · fin_cases i <;> fin_cases j <;>
      norm_num [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
        axisRef,axis,embedXZ,Pi.single_apply]
  · fin_cases i <;>
      simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
        axisRef,axis,letterDirection,embedXZ,Pi.single_apply,base] <;> ring_nf <;> positivity
  · fin_cases i <;>
      norm_num [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
        axisRef,axis,identityDirection,embedXZ,Pi.single_apply]

theorem state_pair_cone (i j : Reference s) (h : exceptional i j = false) :
    0 ≤ orientedPair i j (embedXZ (0,1)) * orientedPair i j (embedXZ (1,1)) := by
  rcases i with i | a | u
  · exact axis_state_cone i j
  · rcases j with j | b | v
    · rw [oriented_product_swap]; exact axis_state_cone j (.inr (.inl a))
    · change 0 ≤ orientedPair (.inr (.inl a)) (.inr (.inl b)) (embedXZ (0,1)) *
        orientedPair (.inr (.inl a)) (.inr (.inl b)) (embedXZ (1,1))
      have hh := sq_nonneg (base s * (((a.val : ℝ)+1)-((b.val : ℝ)+1)))
      convert hh using 1 <;>
        simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
          letterDirection,embedXZ] <;> ring
    · cases h
  · rcases j with j | b | v
    · rw [oriented_product_swap]; exact axis_state_cone j (.inr (.inr u))
    · cases h
    · simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
        identityDirection,embedXZ]

theorem nat_difference_product (a b : ℕ) :
    0 ≤ ((a : ℝ)-(b : ℝ))*((a : ℝ)+1-(b : ℝ)) := by
  by_cases h : b ≤ a
  · have hh : (b : ℝ) ≤ a := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)
  · have hh : (a : ℝ)+1 ≤ b := by exact_mod_cast Nat.lt_of_not_ge h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

theorem axis_image_cone (hs : 0 < s) (i : Fin 3) (j : Reference s) (b : Fin s) :
    0 ≤ orientedPair (axisRef i) j (embedXY (transition b (0,1))) *
      orientedPair (axisRef i) j (embedXY (transition b (1,1))) := by
  have hr := (rho_pos hs).le
  have hq := (base_pos s).le
  rcases j with j | a | u
  · fin_cases i <;> fin_cases j <;>
      simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
        axisRef,axis,embedXY,transition_apply,Pi.single_apply] <;> positivity
  · fin_cases i
    · simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
        axisRef,axis,letterDirection,embedXY,transition_apply,Pi.single_apply]
      positivity
    · simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
        axisRef,axis,letterDirection,embedXY,transition_apply,Pi.single_apply]
      positivity
    · have hh := mul_nonneg (sq_nonneg (rho s)) (nat_difference_product b.val a.val)
      convert hh using 1 <;>
        simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
          axisRef,axis,letterDirection,embedXY,transition_apply,Pi.single_apply]
      field_simp [(base_pos s).ne']
      ring
  · fin_cases i <;>
      simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
        axisRef,axis,identityDirection,embedXY,transition_apply,Pi.single_apply] <;> positivity

theorem image_pair_cone (hs : 0 < s) (i j : Reference s) (b : Fin s) (h : exceptional i j = false) :
    0 ≤ orientedPair i j (embedXY (transition b (0,1))) *
      orientedPair i j (embedXY (transition b (1,1))) := by
  rcases i with i | a | u
  · exact axis_image_cone hs i j b
  · rcases j with j | c | v
    · rw [oriented_product_swap]; exact axis_image_cone hs j (.inr (.inl a)) b
    · have hh := sq_nonneg (rho s * (((c.val : ℝ)+1)-((a.val : ℝ)+1)))
      convert hh using 1 <;>
        simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
          letterDirection,embedXY,transition_apply] <;> ring
    · cases h
  · rcases j with j | c | v
    · rw [oriented_product_swap]; exact axis_image_cone hs j (.inr (.inr u)) b
    · cases h
    · simp [orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
        identityDirection,embedXY]

def detQ (u v x : Fin 3 → ℚ) : ℚ :=
  u 0*(v 1*x 2-v 2*x 1)-u 1*(v 0*x 2-v 2*x 0)+u 2*(v 0*x 1-v 1*x 0)

def statePointQ (A : RationalData s m) (k : Fin m) : Fin 3 → ℚ := ![firstQ A k,0,massQ A k]
def imagePointQ (A : RationalData s m) (a : Fin s) (k : Fin m) : Fin 3 → ℚ :=
  ![rhoQ s/baseQ s*(firstQ A k+((a.val : ℚ)+1)*massQ A k),rhoQ s*massQ A k,0]

def statePairQ (A : RationalData s m) (k : Fin m) : Reference s → Reference s → ℚ
  | .inr (.inl a), .inr (.inr _) => thresholdMomentQ A a k
  | .inr (.inr _), .inr (.inl a) => thresholdMomentQ A a k
  | i,j => |detQ (directionQ i) (directionQ j) (statePointQ A k)|

def imagePairQ (A : RationalData s m) (b : Fin s) (k : Fin m) : Reference s → Reference s → ℚ
  | .inr (.inl a), .inr (.inr _) => rhoQ s/baseQ s * headMomentQ A a b k
  | .inr (.inr _), .inr (.inl a) => rhoQ s/baseQ s * headMomentQ A a b k
  | i,j => |detQ (directionQ i) (directionQ j) (imagePointQ A b k)|

theorem oriented_exception_state (a : Fin s) :
    (orientedPair (letterRef a) identityRef).comp embedXZ = referenceNormal a := by
  apply ContinuousLinearMap.ext
  intro x
  simp [ContinuousLinearMap.comp_apply,orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
    letterRef,identityRef,letterDirection,identityDirection,referenceNormal,digit,embedXZ,base]
  ring

theorem oriented_exception_image (a : Fin s) :
    (orientedPair (letterRef a) identityRef).comp embedXY = referenceNormal a := by
  apply ContinuousLinearMap.ext
  intro x
  simp [ContinuousLinearMap.comp_apply,orientedPair,detFunctional_apply,determinant3,GeneralLabels.referenceDirection,
    letterRef,identityRef,letterDirection,identityDirection,referenceNormal,digit,embedXY,base]
  ring

theorem cast_state_point (A : RationalData s m) (hs : 0 < s) (k : Fin m) :
    (fun i => (statePointQ A k i : ℝ)) = embedXZ (first A.toReal k,mass A.toReal k) := by
  ext i
  fin_cases i <;> simp [statePointQ,embedXZ,congrFun (first_eq_rational A hs) k,
    congrFun (mass_eq_rational A hs) k,RationalSystems.castVector]

theorem cast_image_point (A : RationalData s m) (hs : 0 < s) (b : Fin s) (k : Fin m) :
    (fun i => (imagePointQ A b k i : ℝ)) = embedXY (transition b (first A.toReal k,mass A.toReal k)) := by
  ext i
  fin_cases i <;> simp [imagePointQ,embedXY,transition_apply,congrFun (first_eq_rational A hs) k,
    congrFun (mass_eq_rational A hs) k,RationalSystems.castVector]

theorem cast_detQ (i j : Reference s) (x : Fin 3 → ℚ) :
    (detQ (directionQ i) (directionQ j) x : ℝ) = orientedPair i j (fun k => (x k : ℝ)) := by
  simp only [detQ,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,cast_directionQ,
    orientedPair,detFunctional_apply,determinant3]

theorem state_pair_rational (A : RationalData s m) (hs : 0 < s) (k : Fin m) (i j : Reference s) :
    linearWidth ((pairFunctional i j).comp embedXZ) (stateBody A.toReal hs k) = (statePairQ A k i j : ℝ) := by
  rw [pair_state_oriented]
  have core (r t : Reference s) (h : exceptional r t = false) :
      linearWidth ((orientedPair r t).comp embedXZ) (stateBody A.toReal hs k) =
        (|detQ (directionQ r) (directionQ t) (statePointQ A k)| : ℚ) := by
    rw [linearWidth_state_cone A.toReal hs k _ (state_pair_cone r t h),Rat.cast_abs,
      cast_detQ,cast_state_point A hs k]
    rfl
  rcases i with i | a | u <;> rcases j with j | b | v
  · exact core _ _ rfl
  · exact core _ _ rfl
  · exact core _ _ rfl
  · exact core _ _ rfl
  · exact core _ _ rfl
  · change linearWidth ((orientedPair (letterRef a) identityRef).comp embedXZ) _ = _
    rw [oriented_exception_state,threshold_width]
    exact congrFun (threshold_eq_rational A hs a) k
  · exact core _ _ rfl
  · change linearWidth ((orientedPair identityRef (letterRef b)).comp embedXZ) _ = _
    rw [orientedPair_swap]
    change linearWidth (-((orientedPair (letterRef b) identityRef).comp embedXZ)) _ = _
    rw [linearWidth_neg_state,oriented_exception_state,threshold_width]
    exact congrFun (threshold_eq_rational A hs b) k
  · exact core _ _ rfl

theorem image_pair_rational (A : RationalData s m) (hs : 0 < s) (b : Fin s) (k : Fin m) (i j : Reference s) :
    linearWidth ((pairFunctional i j).comp embedXY) (mapBody (transition b) (stateBody A.toReal hs k)) =
      (imagePairQ A b k i j : ℝ) := by
  rw [pair_image_oriented]
  have core (r t : Reference s) (h : exceptional r t = false) :
      linearWidth ((orientedPair r t).comp embedXY) (mapBody (transition b) (stateBody A.toReal hs k)) =
        (|detQ (directionQ r) (directionQ t) (imagePointQ A b k)| : ℚ) := by
    rw [linearWidth_map,linearWidth_state_cone A.toReal hs k _ (image_pair_cone hs r t b h),
      Rat.cast_abs,cast_detQ,cast_image_point A hs b k]
    rfl
  rcases i with i | a | u <;> rcases j with j | c | v
  · exact core _ _ rfl
  · exact core _ _ rfl
  · exact core _ _ rfl
  · exact core _ _ rfl
  · exact core _ _ rfl
  · change linearWidth ((orientedPair (letterRef a) identityRef).comp embedXY) _ = _
    rw [oriented_exception_image,threshold_image_width]
    simp only [imagePairQ,Rat.cast_mul,Rat.cast_div,cast_rhoQ,cast_baseQ,cast_headMomentQ A hs]
  · exact core _ _ rfl
  · change linearWidth ((orientedPair identityRef (letterRef c)).comp embedXY) _ = _
    rw [orientedPair_swap]
    change linearWidth (-((orientedPair (letterRef c) identityRef).comp embedXY)) _ = _
    rw [linearWidth_neg_image,oriented_exception_image,threshold_image_width]
    simp only [imagePairQ,Rat.cast_mul,Rat.cast_div,cast_rhoQ,cast_baseQ,cast_headMomentQ A hs]
  · exact core _ _ rfl

end MixedVolume.GeneralWidths

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/ReferenceWidths.lean -/

/- BEGIN SOURCE: MixedVolume/General/CanonicalProjections.lean -/
section


/-! The actual coordinate and letter projections of arbitrary nonnegative
state/image combinations, and their explicit rational areas. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralProjections

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords AutomatonZonoids AutomatonMoments
open GeneralLabels GeneralCalibration GeneralForcing ReferenceRecursion ReferenceExpansion
open PlanarRational SeriesMixedArea Set MeasureTheory
open scoped Pointwise BigOperators

abbrev Plane := AutomatonWords.Plane
variable {s m : ℕ}

def stateWeights {R : Type*} [Zero R] (b : Fin m → R) : Primitive s m → R
  | .inl j => b j
  | .inr _ => 0

def imageWeights {R : Type*} [Zero R] (c : Fin s × Fin m → R) : Primitive s m → R
  | .inl _ => 0
  | .inr aj => c aj

def totalWeights {R : Type*} (b : Fin m → R) (c : Fin s × Fin m → R) : Primitive s m → R
  | .inl j => b j
  | .inr aj => c aj

theorem stateWeights_nonneg {R : Type*} [Zero R] [Preorder R] (b : Fin m → R) (hb : ∀ j, 0 ≤ b j) :
    ∀ i : Primitive s m, 0 ≤ stateWeights b i := by
  rintro (j | aj)
  · exact hb j
  · exact le_rfl

theorem imageWeights_nonneg {R : Type*} [Zero R] [Preorder R] (c : Fin s × Fin m → R) (hc : ∀ aj, 0 ≤ c aj) :
    ∀ i : Primitive s m, 0 ≤ imageWeights c i := by
  rintro (j | aj)
  · exact le_rfl
  · exact hc aj

def states (A : Data s m) (hs : 0 < s) (b : Fin m → ℝ) : ConvexBody Plane := ∑ j, b j • stateBody A hs j

def images (A : Data s m) (hs : 0 < s) (c : Fin s × Fin m → ℝ) : ConvexBody Plane :=
  ∑ aj, c aj • mapBody (transition aj.1) (stateBody A hs aj.2)

def baseTuple (A : Data s m) (hs : 0 < s) (b : Fin m → ℝ) (c : Fin s × Fin m → ℝ) : Body 3 :=
  mapBody embedXZ (states A hs b) + mapBody embedXY (images A hs c)

theorem states_eq_combination (A : Data s m) (hs : 0 < s) (b : Fin m → ℝ) :
    states A hs b = combination A hs (stateWeights b) := by
  simp [states,combination,stateWeights,primitiveBody,Fintype.sum_sum_type]

theorem images_eq_combination (A : Data s m) (hs : 0 < s) (c : Fin s × Fin m → ℝ) :
    images A hs c = combination A hs (imageWeights c) := by
  simp [images,combination,imageWeights,primitiveBody,Fintype.sum_sum_type]

theorem states_add_images (A : Data s m) (hs : 0 < s) (b : Fin m → ℝ) (c : Fin s × Fin m → ℝ) :
    states A hs b + images A hs c = combination A hs (totalWeights b c) := by
  simp [states,images,combination,totalWeights,primitiveBody,Fintype.sum_sum_type]

theorem linearWidth_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (l : E →L[ℝ] ℝ) (K : ι → ConvexBody E) : linearWidth l (∑ i, K i) = ∑ i, linearWidth l (K i) := by
  simp only [linearWidth_eq_width]
  rw [show mapBody (horizontalMap l) (∑ i, K i) = ∑ i, mapBody (horizontalMap l) (K i) from
    map_sum (mapBodyHom (horizontalMap l)) _ _,width_sum]

theorem sum_smul_body {ι : Type*} (q : Finset ι) (r : ι → ℝ) (K : ConvexBody Plane)
    (hr : ∀ i ∈ q, 0 ≤ r i) : (∑ i ∈ q, r i • K) = (∑ i ∈ q, r i) • K := by
  classical
  induction q using Finset.induction_on with
  | empty => simp
  | @insert i q hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))]
    exact (body_add_smul K (hr i (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg fun j hj => hr j (Finset.mem_insert_of_mem hj))).symm

theorem state_rankOne (A : Data s m) (hs : 0 < s) (j : Fin m) (l : Plane →L[ℝ] ℝ) (v : Plane) :
    mapBody (CanonicalProjections.rankOne l v) (stateBody A hs j) =
      linearWidth l (stateBody A hs j) • PlanarCorner.segmentBody v := by
  rw [stateBody,← reindex_body (wordEnumeration hs) _ (state_summable A hs j),indexed_nat_eq]
  exact CanonicalProjections.rankOne_series l v _ _

theorem image_rankOne (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m) (l : Plane →L[ℝ] ℝ) (v : Plane) :
    mapBody (CanonicalProjections.rankOne l v) (mapBody (transition a) (stateBody A hs j)) =
      linearWidth l (mapBody (transition a) (stateBody A hs j)) • PlanarCorner.segmentBody v := by
  rw [mapBody_comp,linearWidth_map]
  change mapBody (CanonicalProjections.rankOne (l.comp (transition a)) v) _ = _
  exact state_rankOne A hs j _ _

theorem states_rankOne (A : Data s m) (hs : 0 < s) (b : Fin m → ℝ) (hb : ∀ j, 0 ≤ b j)
    (l : Plane →L[ℝ] ℝ) (v : Plane) :
    mapBody (CanonicalProjections.rankOne l v) (states A hs b) =
      linearWidth l (states A hs b) • PlanarCorner.segmentBody v := by
  rw [states,show mapBody (CanonicalProjections.rankOne l v) (∑ j, b j • stateBody A hs j) =
    ∑ j, mapBody (CanonicalProjections.rankOne l v) (b j • stateBody A hs j) from
    map_sum (mapBodyHom _) _ _,linearWidth_sum]
  simp_rw [mapBody_smul,state_rankOne,smul_smul,linearWidth_smul _ _ (hb _)]
  exact sum_smul_body _ _ _ (fun j _ => mul_nonneg (hb j) measureReal_nonneg)

theorem images_rankOne (A : Data s m) (hs : 0 < s) (c : Fin s × Fin m → ℝ) (hc : ∀ aj, 0 ≤ c aj)
    (l : Plane →L[ℝ] ℝ) (v : Plane) :
    mapBody (CanonicalProjections.rankOne l v) (images A hs c) =
      linearWidth l (images A hs c) • PlanarCorner.segmentBody v := by
  rw [images,show mapBody (CanonicalProjections.rankOne l v)
    (∑ aj, c aj • mapBody (transition aj.1) (stateBody A hs aj.2)) =
    ∑ aj, mapBody (CanonicalProjections.rankOne l v)
      (c aj • mapBody (transition aj.1) (stateBody A hs aj.2)) from
    map_sum (mapBodyHom _) _ _,linearWidth_sum]
  simp_rw [mapBody_smul,image_rankOne,smul_smul,linearWidth_smul _ _ (hc _)]
  exact sum_smul_body _ _ _ (fun aj _ => mul_nonneg (hc aj) measureReal_nonneg)

theorem projected_zero (A : Data s m) (hs : 0 < s) (b : Fin m → ℝ) (c : Fin s × Fin m → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hc : ∀ aj, 0 ≤ c aj) :
    mapBody (coordinateProjection 0) (baseTuple A hs b c) =
      PlanarCorner.height (states A hs b) • PlanarCorner.unitY +
        PlanarCorner.height (images A hs c) • PlanarCorner.unitX := by
  rw [baseTuple,mapBody_add,mapBody_comp,mapBody_comp,
    CanonicalProjections.projection_zero_state,CanonicalProjections.projection_zero_image,
    states_rankOne A hs b hb,images_rankOne A hs c hc]
  rfl

theorem projected_one (A : Data s m) (hs : 0 < s) (b : Fin m → ℝ) (c : Fin s × Fin m → ℝ)
    (hc : ∀ aj, 0 ≤ c aj) :
    mapBody (coordinateProjection 1) (baseTuple A hs b c) =
      states A hs b + PlanarCorner.width (images A hs c) • PlanarCorner.unitX := by
  rw [baseTuple,mapBody_add,mapBody_comp,mapBody_comp,
    CanonicalProjections.projection_one_state,CanonicalProjections.projection_one_image,
    ProjectedForcing.mapBody_id,images_rankOne A hs c hc]
  rfl

theorem projected_two (A : Data s m) (hs : 0 < s) (b : Fin m → ℝ) (c : Fin s × Fin m → ℝ)
    (hb : ∀ j, 0 ≤ b j) :
    mapBody (coordinateProjection 2) (baseTuple A hs b c) =
      PlanarCorner.width (states A hs b) • PlanarCorner.unitX + images A hs c := by
  rw [baseTuple,mapBody_add,mapBody_comp,mapBody_comp,
    CanonicalProjections.projection_two_state,CanonicalProjections.projection_two_image,
    ProjectedForcing.mapBody_id,states_rankOne A hs b hb]
  rfl

theorem projectionLetter_embedXZ (hs : 0 < s) (a : Fin s) :
    (projectionLetter a).comp embedXZ = (base s/rho s) • transition a := by
  have h := scaled_projectionLetter_embedXZ a
  have hh := congrArg (fun f : Plane →L[ℝ] Plane => (base s/rho s) • f) h
  rw [smul_smul,show base s/rho s*(rho s/base s) = 1 from by field_simp [(rho_pos hs).ne',(base_pos s).ne'],one_smul] at hh
  exact hh

def letterWeights {R : Type*} [Zero R] [Add R] [Mul R]
    (factor : R) (a : Fin s) (b : Fin m → R) (c : Fin s × Fin m → R) : Primitive s m → R
  | .inl _ => 0
  | .inr (d,j) => c (d,j) + if d = a then factor*b j else 0

theorem projected_letter (A : Data s m) (hs : 0 < s) (a : Fin s)
    (b : Fin m → ℝ) (c : Fin s × Fin m → ℝ) (hb : ∀ j, 0 ≤ b j) (hc : ∀ aj, 0 ≤ c aj) :
    mapBody (projectionLetter a) (baseTuple A hs b c) =
      combination A hs (letterWeights (base s/rho s) a b c) := by
  rw [baseTuple,mapBody_add,mapBody_comp,mapBody_comp,projectionLetter_embedXZ hs,
    GeneralForcing.projectionLetter_embedXY,ProjectedForcing.mapBody_id,ProjectedForcing.mapBody_smul_map]
  have hr : 0 ≤ base s/rho s := div_nonneg (base_pos s).le (rho_pos hs).le
  simp only [states,show mapBody (transition a) (∑ j, b j • stateBody A hs j) =
    ∑ j, mapBody (transition a) (b j • stateBody A hs j) from map_sum (mapBodyHom _) _ _,
    mapBody_smul,Finset.smul_sum,smul_smul]
  simp only [combination,letterWeights,Fintype.sum_sum_type,body_zero_smul,Finset.sum_const_zero,zero_add,
    Fintype.sum_prod_type,primitiveBody,images]
  have he (d : Fin s) (j : Fin m) :
      (c (d,j) + if d = a then base s/rho s*b j else 0) • mapBody (transition d) (stateBody A hs j) =
        c (d,j) • mapBody (transition d) (stateBody A hs j) +
          (if d = a then (base s/rho s*b j) • mapBody (transition d) (stateBody A hs j) else 0) := by
    split_ifs with h
    · rw [body_add_smul _ (hc _) (mul_nonneg hr (hb j))]
    · simp
  have hselected :
      (∑ d : Fin s, ∑ j : Fin m,
        if d = a then (base s/rho s*b j) • mapBody (transition d) (stateBody A hs j) else 0) =
      ∑ j : Fin m, (base s/rho s*b j) • mapBody (transition a) (stateBody A hs j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp_rw [he,Finset.sum_add_distrib]
  rw [hselected]
  ac_rfl

theorem projected_identity (A : Data s m) (hs : 0 < s) (b : Fin m → ℝ) (c : Fin s × Fin m → ℝ) :
    mapBody projectionIdentity (baseTuple A hs b c) = combination A hs (totalWeights b c) := by
  rw [baseTuple,mapBody_add,mapBody_comp,mapBody_comp,projectionIdentity_embedXZ,projectionIdentity_embedXY,
    ProjectedForcing.mapBody_id,ProjectedForcing.mapBody_id,states_add_images]

end MixedVolume.GeneralProjections

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/CanonicalProjections.lean -/

/- BEGIN SOURCE: MixedVolume/General/CanonicalArithmetic.lean -/
section


/-! The complete finite arithmetic formula for the canonical volume.  This
formula is defined over every rational algebra, so its parameter degree and
its exact rational computation can be verified from the same expression. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.CanonicalArithmetic

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords AutomatonZonoids AutomatonMoments
open GeneralLabels GeneralCalibration ReferenceRecursion ReferenceExpansion GeneralWidths
open PlanarRational GeneralProjections Set MeasureTheory
open scoped Pointwise BigOperators

variable {s m : ℕ}

section Arithmetic
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def linear {ι : Type*} [Fintype ι] (c : ι → ℚ) (b : ι → R) : R :=
  ∑ i, b i * algebraMap ℚ R (c i)

def area (A : RationalData s m) (b : Primitive s m → R) : R :=
  algebraMap ℚ R (1/2) * ∑ i, ∑ j, b i*b j*algebraMap ℚ R (mixedQ A i j)

def height (A : RationalData s m) (b : Primitive s m → R) : R := linear (heightQ A) b

def width (A : RationalData s m) (b : Primitive s m → R) : R := linear (widthQ A) b

def initialStats (A : RationalData s m) (b : Fin m → R) (c : Fin s × Fin m → R) : Stats R s where
  volume := area A (stateWeights b)*height A (imageWeights c) + height A (stateWeights b)*area A (imageWeights c)
  area r := match r with
    | .inl i => ![height A (stateWeights b)*height A (imageWeights c),
        area A (stateWeights b)+width A (imageWeights c)*height A (stateWeights b),
        area A (imageWeights c)+width A (stateWeights b)*height A (imageWeights c)] i
    | .inr (.inl a) => area A (letterWeights (algebraMap ℚ R (baseQ s/rhoQ s)) a b c)
    | .inr (.inr _) => area A (totalWeights b c)
  width i j := linear (fun k => statePairQ A k i j) b + linear (fun aj => imagePairQ A aj.1 aj.2 i j) c

end Arithmetic

def references (s : ℕ) : List (Reference s) :=
  List.ofFn (fun i : Fin 3 => axisRef i) ++ List.ofFn (fun a : Fin s => letterRef a) ++ [identityRef]

def formula {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : RationalData s m) (w : Label s m → R) : R :=
  (run (fun i j k => algebraMap ℚ R (tripleQ i j k)) (fun r => w (ref r))
    (initialStats A (fun j => w (stateLabel j)) (fun aj => w (imageLabel aj.1 aj.2))) (references s)).volume

def mapStats {R S : Type*} (f : R → S) (z : Stats R s) : Stats S s where
  volume := f z.volume
  area i := f (z.area i)
  width i j := f (z.width i j)

section Naturality
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]

theorem map_linear {ι : Type*} [Fintype ι] (f : R →ₐ[ℚ] S) (c : ι → ℚ) (b : ι → R) :
    f (linear c b) = linear c (fun i => f (b i)) := by
  simp [linear,map_sum,f.commutes]

theorem map_area (f : R →ₐ[ℚ] S) (A : RationalData s m) (b : Primitive s m → R) :
    f (area A b) = area A (fun i => f (b i)) := by
  simp [area,map_sum,f.commutes]

theorem map_height (f : R →ₐ[ℚ] S) (A : RationalData s m) (b : Primitive s m → R) :
    f (height A b) = height A (fun i => f (b i)) := map_linear f _ _

theorem map_width (f : R →ₐ[ℚ] S) (A : RationalData s m) (b : Primitive s m → R) :
    f (width A b) = width A (fun i => f (b i)) := map_linear f _ _

theorem map_initialStats (f : R →ₐ[ℚ] S) (A : RationalData s m) (b : Fin m → R) (c : Fin s × Fin m → R) :
    mapStats f (initialStats A b c) = initialStats A (fun j => f (b j)) (fun aj => f (c aj)) := by
  have hstate : (fun i => f (stateWeights (s := s) b i)) = stateWeights (fun j => f (b j)) := by
    funext i; rcases i with j | aj <;> simp [stateWeights]
  have himage : (fun i => f (imageWeights c i)) = imageWeights (fun aj => f (c aj)) := by
    funext i; rcases i with j | aj <;> simp [imageWeights]
  have htotal : (fun i => f (totalWeights b c i)) = totalWeights (fun j => f (b j)) (fun aj => f (c aj)) := by
    funext i; rcases i with j | aj <;> rfl
  have hletter (a : Fin s) : (fun i => f (letterWeights (algebraMap ℚ R (baseQ s/rhoQ s)) a b c i)) =
      letterWeights (algebraMap ℚ S (baseQ s/rhoQ s)) a (fun j => f (b j)) (fun aj => f (c aj)) := by
    funext i
    rcases i with j | ⟨d,j⟩
    · simp [letterWeights]
    · by_cases h : d = a <;> simp [letterWeights,h,f.commutes]
  apply Stats.ext
  · simp only [mapStats,initialStats,map_add,map_mul,map_area,map_height,hstate,himage]
  · funext i
    rcases i with i | a | u
    · fin_cases i <;> simp [mapStats,initialStats,map_area,map_height,map_width,hstate,himage]
    · simp only [mapStats,initialStats,map_area,hletter]
    · simp only [mapStats,initialStats,map_area,htotal]
  · funext i j
    simp only [mapStats,initialStats,map_add,map_linear]

theorem map_step (f : R →ₐ[ℚ] S) (D : Reference s → Reference s → Reference s → R)
    (u : R) (j : Reference s) (z : Stats R s) :
    mapStats f (step D u j z) = step (fun i j k => f (D i j k)) (f u) j (mapStats f z) := by
  apply Stats.ext
  · simp [step,mapStats]
  · funext i; simp [step,mapStats]
  · funext i k; simp [step,mapStats]

theorem map_run (f : R →ₐ[ℚ] S) (D : Reference s → Reference s → Reference s → R)
    (u : Reference s → R) (z : Stats R s) (refs : List (Reference s)) :
    mapStats f (run D u z refs) =
      run (fun i j k => f (D i j k)) (fun j => f (u j)) (mapStats f z) refs := by
  induction refs generalizing z with
  | nil => rfl
  | cons j refs ih => rw [run,run,ih,map_step]

theorem map_formula (f : R →ₐ[ℚ] S) (A : RationalData s m) (w : Label s m → R) :
    f (formula A w) = formula A (fun i => f (w i)) := by
  have h := map_run f (fun i j k => algebraMap ℚ R (tripleQ i j k)) (fun r => w (ref r))
    (initialStats A (fun j => w (stateLabel j)) (fun aj => w (imageLabel aj.1 aj.2))) (references s)
  rw [map_initialStats] at h
  simp only [f.commutes] at h
  exact congrArg Stats.volume h

end Naturality

theorem area_eq_Q (A : RationalData s m) (b : Primitive s m → ℚ) :
    area A b = combinationAreaQ A b := by
  simp only [area,combinationAreaQ,combinationMixedQ,Algebra.algebraMap_self,RingHom.id_apply]
  ring

theorem actual_area (A : RationalData s m) (hs : 0 < s) (b : Primitive s m → ℚ) (hb : ∀ i, 0 ≤ b i) :
    volume.real (combination A.toReal hs (fun i => (b i : ℝ)) : Set AutomatonWords.Plane) =
      area A (fun i => (b i : ℝ)) := by
  rw [combination_area A hs b hb,← area_eq_Q]
  exact map_area (Algebra.ofId ℚ ℝ) A b

theorem actual_height (A : RationalData s m) (hs : 0 < s) (b : Primitive s m → ℚ) (hb : ∀ i, 0 ≤ b i) :
    PlanarCorner.height (combination A.toReal hs (fun i => (b i : ℝ))) = height A (fun i => (b i : ℝ)) := by
  rw [combination_height A hs b hb]
  simp [height,linear,combinationHeightQ]

theorem actual_width (A : RationalData s m) (hs : 0 < s) (b : Primitive s m → ℚ) (hb : ∀ i, 0 ≤ b i) :
    PlanarCorner.width (combination A.toReal hs (fun i => (b i : ℝ))) = width A (fun i => (b i : ℝ)) := by
  rw [combination_width A hs b hb]
  simp [width,linear,combinationWidthQ]

theorem all_reference_sum (K : Body 3) (u : Reference s → ℝ) :
    addReferences K u (references s) = K + ∑ r, u r • centeredBody (GeneralLabels.referenceDirection r) := by
  rw [addReferences_eq_sum]
  simp [references,List.map_append,List.sum_append,List.map_ofFn,List.sum_ofFn,
    Fintype.sum_sum_type,Fintype.sum_unique,Fin.sum_univ_three,
    axisRef,letterRef,identityRef,add_assoc]

end MixedVolume.CanonicalArithmetic

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/CanonicalArithmetic.lean -/

/- BEGIN SOURCE: MixedVolume/General/CanonicalVolume.lean -/
section


/-! Verification that the finite rational arithmetic expression evaluates the
entire canonical volume polynomial, and therefore also every signed real
substitution used in the reduction. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.CanonicalVolume

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords AutomatonZonoids AutomatonMoments
open GeneralLabels GeneralCalibration ReferenceRecursion ReferenceExpansion GeneralWidths
open PlanarRational GeneralProjections CanonicalArithmetic CanonicalGeometry GeneralTarget Set MeasureTheory
open scoped Pointwise BigOperators

abbrev Plane := AutomatonWords.Plane
variable {s m : ℕ}

@[simp] theorem cast_stateWeights (b : Fin m → ℚ) (i : Primitive s m) :
    ((stateWeights b i : ℚ) : ℝ) = stateWeights (fun j => (b j : ℝ)) i := by
  cases i <;> simp [stateWeights]

@[simp] theorem cast_imageWeights (c : Fin s × Fin m → ℚ) (i : Primitive s m) :
    ((imageWeights c i : ℚ) : ℝ) = imageWeights (fun aj => (c aj : ℝ)) i := by
  cases i <;> simp [imageWeights]

@[simp] theorem cast_totalWeights (b : Fin m → ℚ) (c : Fin s × Fin m → ℚ) (i : Primitive s m) :
    ((totalWeights b c i : ℚ) : ℝ) = totalWeights (fun j => (b j : ℝ)) (fun aj => (c aj : ℝ)) i := by
  cases i <;> rfl

@[simp] theorem cast_letterWeights (a : Fin s) (b : Fin m → ℚ) (c : Fin s × Fin m → ℚ) (i : Primitive s m) :
    ((letterWeights (baseQ s/rhoQ s) a b c i : ℚ) : ℝ) =
      letterWeights (base s/rho s) a (fun j => (b j : ℝ)) (fun aj => (c aj : ℝ)) i := by
  rcases i with j | ⟨d,j⟩
  · simp [letterWeights]
  · by_cases h : d = a <;> simp [letterWeights,h]

theorem states_area (A : RationalData s m) (hs : 0 < s) (b : Fin m → ℚ) (hb : ∀ j, 0 ≤ b j) :
    volume.real (states A.toReal hs (fun j => (b j : ℝ)) : Set Plane) =
      area A (stateWeights (fun j => (b j : ℝ))) := by
  rw [states_eq_combination]
  simpa only [cast_stateWeights] using actual_area A hs (stateWeights b) (stateWeights_nonneg b hb)

theorem images_area (A : RationalData s m) (hs : 0 < s) (c : Fin s × Fin m → ℚ) (hc : ∀ aj, 0 ≤ c aj) :
    volume.real (images A.toReal hs (fun aj => (c aj : ℝ)) : Set Plane) =
      area A (imageWeights (fun aj => (c aj : ℝ))) := by
  rw [images_eq_combination]
  simpa only [cast_imageWeights] using actual_area A hs (imageWeights c) (imageWeights_nonneg c hc)

theorem states_height (A : RationalData s m) (hs : 0 < s) (b : Fin m → ℚ) (hb : ∀ j, 0 ≤ b j) :
    PlanarCorner.height (states A.toReal hs (fun j => (b j : ℝ))) =
      height A (stateWeights (fun j => (b j : ℝ))) := by
  rw [states_eq_combination]
  simpa only [cast_stateWeights] using actual_height A hs (stateWeights b) (stateWeights_nonneg b hb)

theorem images_height (A : RationalData s m) (hs : 0 < s) (c : Fin s × Fin m → ℚ) (hc : ∀ aj, 0 ≤ c aj) :
    PlanarCorner.height (images A.toReal hs (fun aj => (c aj : ℝ))) =
      height A (imageWeights (fun aj => (c aj : ℝ))) := by
  rw [images_eq_combination]
  simpa only [cast_imageWeights] using actual_height A hs (imageWeights c) (imageWeights_nonneg c hc)

theorem states_width (A : RationalData s m) (hs : 0 < s) (b : Fin m → ℚ) (hb : ∀ j, 0 ≤ b j) :
    PlanarCorner.width (states A.toReal hs (fun j => (b j : ℝ))) =
      width A (stateWeights (fun j => (b j : ℝ))) := by
  rw [states_eq_combination]
  simpa only [cast_stateWeights] using actual_width A hs (stateWeights b) (stateWeights_nonneg b hb)

theorem images_width (A : RationalData s m) (hs : 0 < s) (c : Fin s × Fin m → ℚ) (hc : ∀ aj, 0 ≤ c aj) :
    PlanarCorner.width (images A.toReal hs (fun aj => (c aj : ℝ))) =
      width A (imageWeights (fun aj => (c aj : ℝ))) := by
  rw [images_eq_combination]
  simpa only [cast_imageWeights] using actual_width A hs (imageWeights c) (imageWeights_nonneg c hc)

theorem actual_initialStats (A : RationalData s m) (hs : 0 < s)
    (b : Fin m → ℚ) (c : Fin s × Fin m → ℚ) (hb : ∀ j, 0 ≤ b j) (hc : ∀ aj, 0 ≤ c aj) :
    actualStats (baseTuple A.toReal hs (fun j => (b j : ℝ)) (fun aj => (c aj : ℝ))) =
      initialStats A (fun j => (b j : ℝ)) (fun aj => (c aj : ℝ)) := by
  have hbr : ∀ j, (0 : ℝ) ≤ b j := fun j => by exact_mod_cast hb j
  have hcr : ∀ aj, (0 : ℝ) ≤ c aj := fun aj => by exact_mod_cast hc aj
  have hSH : 0 ≤ PlanarCorner.height (states A.toReal hs (fun j => (b j : ℝ))) :=
    measureReal_nonneg
  have hIH : 0 ≤ PlanarCorner.height (images A.toReal hs (fun aj => (c aj : ℝ))) :=
    measureReal_nonneg
  have hSW : 0 ≤ PlanarCorner.width (states A.toReal hs (fun j => (b j : ℝ))) :=
    measureReal_nonneg
  have hIW : 0 ≤ PlanarCorner.width (images A.toReal hs (fun aj => (c aj : ℝ))) :=
    measureReal_nonneg
  apply Stats.ext
  · change bodyVolume (ScalarCombination.planePair _ _) = _
    rw [ScalarCombination.volume_planePair,states_area A hs b hb,images_height A hs c hc,
      states_height A hs b hb,images_area A hs c hc]
    rfl
  · funext r
    rcases r with i | a | u
    · fin_cases i
      · change projectionArea (coordinateProjection 0) _ = _
        rw [projectionArea,projected_zero _ _ _ _ hbr hcr,add_comm,
          PlanarCorner.area_add_scaled_unitY _ hSH,
          PlanarCorner.area_smul _ hIH,PlanarCorner.unitX,PlanarCorner.area_segmentBody,
          PlanarCorner.width_smul _ hIH]
        change _ + _ * (_ * PlanarCorner.width PlanarCorner.unitX) = _
        rw [PlanarCorner.width_unitX,states_height A hs b hb,images_height A hs c hc]
        change _ = height A (stateWeights (fun j => (b j : ℝ))) *
          height A (imageWeights (fun aj => (c aj : ℝ)))
        ring
      · change projectionArea (coordinateProjection 1) _ = _
        rw [projectionArea,projected_one _ _ _ _ hcr,PlanarCorner.area_add_scaled_unitX _ hIW,
          states_area A hs b hb,images_width A hs c hc,states_height A hs b hb]
        rfl
      · change projectionArea (coordinateProjection 2) _ = _
        rw [projectionArea,projected_two _ _ _ _ hbr,add_comm,PlanarCorner.area_add_scaled_unitX _ hSW,
          images_area A hs c hc,states_width A hs b hb,images_height A hs c hc]
        rfl
    · change projectionArea (GeneralForcing.projectionLetter a) _ = _
      rw [projectionArea,projected_letter _ _ _ _ _ hbr hcr]
      have hfac : (0 : ℚ) ≤ baseQ s/rhoQ s := by
        dsimp [baseQ,rhoQ]
        positivity
      have hfacCast : algebraMap ℚ ℝ (baseQ s/rhoQ s) = base s/rho s := by
        rw [eq_ratCast,Rat.cast_div,cast_baseQ,cast_rhoQ]
      have hn : ∀ i : Primitive s m, 0 ≤ letterWeights (baseQ s/rhoQ s) a b c i := by
        rintro (j | ⟨d,j⟩)
        · exact le_rfl
        · dsimp [letterWeights]
          split_ifs
          · exact add_nonneg (hc (d,j)) (mul_nonneg hfac (hb j))
          · simpa only [add_zero] using hc (d,j)
      simpa only [cast_letterWeights,initialStats,hfacCast] using
        actual_area A hs (letterWeights (baseQ s/rhoQ s) a b c) hn
    · change projectionArea GeneralForcing.projectionIdentity _ = _
      rw [projectionArea,projected_identity]
      have hn : ∀ i : Primitive s m, 0 ≤ totalWeights b c i := by
        rintro (j | aj)
        · exact hb j
        · exact hc aj
      simpa only [cast_totalWeights,initialStats] using actual_area A hs (totalWeights b c) hn
  · funext i j
    change linearWidth (pairFunctional i j) (baseTuple _ _ _ _) = _
    rw [baseTuple,linearWidth_add,linearWidth_map,linearWidth_map,states,images,linearWidth_sum,linearWidth_sum]
    simp_rw [linearWidth_smul _ _ (hbr _),linearWidth_smul _ _ (hcr _),state_pair_rational A hs,image_pair_rational A hs]
    rfl

theorem sumBody_eq_references (A : Data s m) (hs : 0 < s) (w : Label s m → ℝ) :
    sumBody (canonical A hs) w =
      addReferences (baseTuple A hs (fun j => w (stateLabel j)) (fun aj => w (imageLabel aj.1 aj.2)))
        (fun r => w (ref r)) (references s) := by
  rw [all_reference_sum,baseTuple]
  have hm (f : Plane →L[ℝ] Space 3) {ι : Type} [Fintype ι] (K : ι → ConvexBody Plane) :
      mapBody f (∑ i, K i) = ∑ i, mapBody f (K i) := map_sum (mapBodyHom f) _ _
  have hz (r : ℝ) : r • (0 : Body 3) = 0 := by
    apply ConvexBody.ext
    rw [ConvexBody.coe_smul,ConvexBody.coe_zero]
    change r • ({0} : Set (Space 3)) = {0}
    rw [Set.smul_set_singleton,_root_.smul_zero]
  simp only [states,images,hm,mapBody_smul,sumBody,Fintype.sum_sum_type,Fintype.sum_unique,
    canonical,hz,add_zero,stateLabel,imageLabel,ref,Fintype.sum_prod_type]
  ac_nf at ⊢ <;> exact add_left_comm _ _ _

theorem formula_volume_rational_weights (A : RationalData s m) (hs : 0 < s)
    (w : Label s m → ℚ) (hw : ∀ i, 0 ≤ w i) :
    formula A (fun i => (w i : ℝ)) = bodyVolume (sumBody (canonical A.toReal hs) (fun i => (w i : ℝ))) := by
  rw [sumBody_eq_references]
  have h := actualStats_run
    (baseTuple A.toReal hs (fun j => (w (stateLabel j) : ℝ)) (fun aj => (w (imageLabel aj.1 aj.2) : ℝ)))
    (fun r => (w (ref r) : ℝ)) (fun r => by exact_mod_cast hw (ref r)) (references s)
  rw [actual_initialStats A hs _ _ (fun j => hw _) (fun aj => hw _)] at h
  exact (congrArg Stats.volume h).symm

def canonicalPolynomialQ (A : RationalData s m) : MvPolynomial (Label s m) ℚ :=
  formula A (fun i => MvPolynomial.X i)

theorem eval_canonicalPolynomialQ {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : RationalData s m) (w : Label s m → R) :
    MvPolynomial.aeval w (canonicalPolynomialQ A) = formula A w := by
  rw [canonicalPolynomialQ,map_formula]
  simp only [MvPolynomial.aeval_X]

theorem canonicalPolynomialQ_eq (A : RationalData s m) (hs : 0 < s) :
    MvPolynomial.map (algebraMap ℚ ℝ) (canonicalPolynomialQ A) = indexedPolynomial (canonical A.toReal hs) := by
  apply MvPolynomial.funext_set (fun _ => Set.range (fun n : ℕ => (n : ℝ)))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
  intro w hw
  choose n hn using (fun i => hw i (Set.mem_univ _))
  let q : Label s m → ℚ := fun i => n i
  have hq : (fun i => (q i : ℝ)) = w := by
    funext i
    simpa only [q,Rat.cast_natCast] using hn i
  have hnon : ∀ i, 0 ≤ q i := fun i => Nat.cast_nonneg _
  have hwr : ∀ i, 0 ≤ w i := by
    rw [← hq]
    intro i
    change (0 : ℝ) ≤ (q i : ℝ)
    exact Rat.cast_nonneg.mpr (hnon i)
  rw [MvPolynomial.eval_map,indexedPolynomial_eval _ _ hwr]
  change MvPolynomial.aeval w (canonicalPolynomialQ A) = _
  rw [eval_canonicalPolynomialQ,← hq]
  exact formula_volume_rational_weights A hs q hnon

theorem canonicalPolynomialQ_homogeneous (A : RationalData s m) (hs : 0 < s) :
    (canonicalPolynomialQ A).IsHomogeneous 3 := by
  apply MvPolynomial.IsHomogeneous.of_map (f := algebraMap ℚ ℝ) Rat.cast_injective
  rw [canonicalPolynomialQ_eq A hs]
  exact indexedPolynomial_homogeneous _

theorem targetPolynomial_eval_formula (A : RationalData s m) (hs : 0 < s) (δ : Fin m → ℝ)
    (w : Label s m → ℝ) :
    MvPolynomial.eval w (targetPolynomial A.toReal hs δ) = formula A (shiftWeight δ w) := by
  rw [targetPolynomial_eval,← canonicalPolynomialQ_eq A hs,MvPolynomial.eval_map]
  exact eval_canonicalPolynomialQ A (shiftWeight δ w)

end MixedVolume.CanonicalVolume

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/CanonicalVolume.lean -/

/- BEGIN SOURCE: MixedVolume/General/ParameterDegree.lean -/
section


/-! The complete arithmetic formula has parameter degree at most two when
only state coefficients depend linearly on the parameters. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.ParameterDegree

open AutomatonWords AutomatonMoments GeneralLabels ReferenceRecursion PlanarRational GeneralProjections
open CanonicalArithmetic MvPolynomial
open scoped BigOperators

variable {s m : ℕ} {σ : Type*}

theorem degree_add {p q : MvPolynomial σ ℚ} {d : ℕ} (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    (p+q).totalDegree ≤ d := (totalDegree_add p q).trans (max_le hp hq)

theorem degree_mul {p q : MvPolynomial σ ℚ} {d e : ℕ} (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ e) :
    (p*q).totalDegree ≤ d+e := (totalDegree_mul p q).trans (Nat.add_le_add hp hq)

theorem degree_C (r : ℚ) : (C r : MvPolynomial σ ℚ).totalDegree ≤ 0 := by simp

theorem linear_degree {ι : Type*} [Fintype ι] (c : ι → ℚ) (b : ι → MvPolynomial σ ℚ)
    {d : ℕ} (hb : ∀ i, (b i).totalDegree ≤ d) : (linear c b).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro i _
  simpa only [Nat.add_zero,MvPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply] using
    degree_mul (hb i) (degree_C (c i))

theorem height_degree (A : RationalData s m) (b : Primitive s m → MvPolynomial σ ℚ)
    {d : ℕ} (hb : ∀ i, (b i).totalDegree ≤ d) : (height A b).totalDegree ≤ d := linear_degree _ _ hb

theorem width_degree (A : RationalData s m) (b : Primitive s m → MvPolynomial σ ℚ)
    {d : ℕ} (hb : ∀ i, (b i).totalDegree ≤ d) : (width A b).totalDegree ≤ d := linear_degree _ _ hb

theorem area_degree (A : RationalData s m) (b : Primitive s m → MvPolynomial σ ℚ)
    {d : ℕ} (hb : ∀ i, (b i).totalDegree ≤ d) : (area A b).totalDegree ≤ d+d := by
  simp only [CanonicalArithmetic.area,MvPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply]
  apply (degree_mul (e := d+d) (degree_C (1/2)) ?_).trans (by omega)
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  simpa only [Nat.add_zero,MvPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply] using
    degree_mul (degree_mul (hb i) (hb j)) (degree_C (mixedQ A i j))

def DegreeBound (z : Stats (MvPolynomial σ ℚ) s) : Prop :=
  z.volume.totalDegree ≤ 2 ∧ (∀ i, (z.area i).totalDegree ≤ 2) ∧
    (∀ i j, (z.width i j).totalDegree ≤ 1)

theorem initial_degree (A : RationalData s m) (b : Fin m → MvPolynomial σ ℚ)
    (c : Fin s × Fin m → MvPolynomial σ ℚ)
    (hb : ∀ j, (b j).totalDegree ≤ 1) (hc : ∀ aj, (c aj).totalDegree ≤ 0) :
    DegreeBound (initialStats A b c) := by
  have hs : ∀ i : Primitive s m, (stateWeights b i).totalDegree ≤ 1 := by
    rintro (j | aj)
    · exact hb j
    · simp [stateWeights]
  have hi : ∀ i : Primitive s m, (imageWeights c i).totalDegree ≤ 0 := by
    rintro (j | aj)
    · simp [imageWeights]
    · exact hc aj
  have hAs : (area A (stateWeights b)).totalDegree ≤ 2 := area_degree A _ hs
  have hAi : (area A (imageWeights c)).totalDegree ≤ 0 := area_degree A _ hi
  have hHs := height_degree A _ hs
  have hHi := height_degree A _ hi
  have hWs := width_degree A _ hs
  have hWi := width_degree A _ hi
  refine ⟨?_,?_,?_⟩
  · exact degree_add ((degree_mul hAs hHi).trans (by omega)) ((degree_mul hHs hAi).trans (by omega))
  · intro r
    rcases r with i | a | u
    · fin_cases i
      · exact (degree_mul hHs hHi).trans (by omega)
      · exact degree_add hAs ((degree_mul hWi hHs).trans (by omega))
      · exact degree_add (hAi.trans (by omega)) ((degree_mul hWs hHi).trans (by omega))
    · apply area_degree A _ (d := 1)
      rintro (j | ⟨d,j⟩)
      · simp [letterWeights]
      · dsimp [letterWeights]
        apply degree_add ((hc _).trans (by omega))
        split_ifs
        · simpa only [Nat.zero_add,MvPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply] using
            degree_mul (degree_C (baseQ s/rhoQ s)) (hb j)
        · simp
    · apply area_degree A _ (d := 1)
      rintro (j | aj)
      · exact hb j
      · exact (hc aj).trans (by omega)
  · intro i j
    exact degree_add (linear_degree _ _ hb) ((linear_degree _ _ hc).trans (by omega))

theorem step_degree (z : Stats (MvPolynomial σ ℚ) s) (hz : DegreeBound z)
    (u : MvPolynomial σ ℚ) (hu : u.totalDegree ≤ 0) (j : Reference s) :
    DegreeBound (step (fun i j k => C (tripleQ i j k)) u j z) := by
  refine ⟨degree_add hz.1 ?_,?_,?_⟩
  · simpa only [Nat.zero_add] using degree_mul hu (hz.2.1 j)
  · intro i
    exact degree_add (hz.2.1 i) ((degree_mul hu (hz.2.2 j i)).trans (by omega))
  · intro i k
    exact degree_add (hz.2.2 i k) ((degree_mul hu (degree_C (tripleQ i k j))).trans (by omega))

theorem run_degree (z : Stats (MvPolynomial σ ℚ) s) (hz : DegreeBound z)
    (u : Reference s → MvPolynomial σ ℚ) (hu : ∀ j, (u j).totalDegree ≤ 0)
    (refs : List (Reference s)) :
    DegreeBound (run (fun i j k => C (tripleQ i j k)) u z refs) := by
  induction refs generalizing z with
  | nil => exact hz
  | cons j refs ih => exact ih _ (step_degree z hz (u j) (hu j) j)

theorem formula_degree (A : RationalData s m) (w : Label s m → MvPolynomial σ ℚ)
    (hr : ∀ r, (w (ref r)).totalDegree ≤ 0)
    (hb : ∀ j, (w (stateLabel j)).totalDegree ≤ 1)
    (hc : ∀ a j, (w (imageLabel a j)).totalDegree ≤ 0) :
    (formula A w).totalDegree ≤ 2 := by
  have h := run_degree (initialStats A (fun j => w (stateLabel j)) (fun aj => w (imageLabel aj.1 aj.2)))
    (initial_degree A _ _ hb (fun aj => hc aj.1 aj.2)) (fun r => w (ref r)) hr (references s)
  simpa only [CanonicalArithmetic.formula,MvPolynomial.algebraMap_apply,
    Algebra.algebraMap_self_apply] using h.1

end MixedVolume.ParameterDegree

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/ParameterDegree.lean -/

/- BEGIN SOURCE: MixedVolume/General/RationalReduction.lean -/
section


/-! The complete rational quadratic map in Theorem 4.3.  Coefficients are
extracted by a finite exact interpolation identity from the verified full
arithmetic volume formula. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.RationalReduction

open VolumePolynomials AutomatonWords AutomatonMoments GeneralLabels GeneralTarget GeneralDeficit GeneralLocus
open CanonicalArithmetic CanonicalVolume ParameterDegree RationalExtraction MvPolynomial
open scoped BigOperators

variable {s m : ℕ}
abbrev Parameter (m : ℕ) := Fin m ⊕ Unit

def assignment {R : Type*} (p : Fin m → R) (theta : R) : Parameter m → R
  | .inl j => p j
  | .inr _ => theta

def gammaQ (A : RationalData s m) : ℚ := ∑ j, A.stationary j*A.f j

def deltaQ (A : RationalData s m) (p : Fin m → ℚ) (theta : ℚ) (j : Fin m) : ℚ :=
  ((1+theta)/(1+gammaQ A))*A.stationary j-p j

theorem cast_gammaQ (A : RationalData s m) : (gammaQ A : ℝ) = A.toReal.gamma := by
  simp [gammaQ,Data.gamma,dotProduct,RationalData.toReal]

theorem cast_deltaQ (A : RationalData s m) (p : Fin m → ℚ) (theta : ℚ) (j : Fin m) :
    (deltaQ A p theta j : ℝ) = targetDelta A.toReal (fun k => (p k : ℝ)) (theta : ℝ) j := by
  simp [deltaQ,targetDelta,eta,cast_gammaQ,RationalData.toReal]

def deltaSymbol (A : RationalData s m) (j : Fin m) : MvPolynomial (Parameter m) ℚ :=
  C (A.stationary j/(1+gammaQ A))*(1+X (.inr ())) - X (.inl j)

theorem eval_deltaSymbol (A : RationalData s m) (p : Fin m → ℝ) (theta : ℝ) (j : Fin m) :
    MvPolynomial.aeval (assignment p theta) (deltaSymbol A j) = targetDelta A.toReal p theta j := by
  simp [deltaSymbol,assignment,targetDelta,eta,cast_gammaQ,RationalData.toReal]
  ring

theorem deltaSymbol_degree (A : RationalData s m) (j : Fin m) : (deltaSymbol A j).totalDegree ≤ 1 := by
  have hx (i : Parameter m) : (X i : MvPolynomial (Parameter m) ℚ).totalDegree ≤ 1 :=
    (isHomogeneous_X ℚ i).totalDegree_le
  have hsum : (1+X (.inr ()) : MvPolynomial (Parameter m) ℚ).totalDegree ≤ 1 :=
    degree_add (by simp) (hx _)
  have hm := degree_mul (degree_C (A.stationary j/(1+gammaQ A))) hsum
  exact (totalDegree_sub _ _).trans (max_le hm (hx _))

def shiftedSample (A : RationalData s m) (w : Label s m → ℚ) : Label s m → MvPolynomial (Parameter m) ℚ
  | .inr (.inl j) => C (w (stateLabel j)) + deltaSymbol A j*C (w deficitLabel)
  | i => C (w i)

theorem eval_shiftedSample (A : RationalData s m) (p : Fin m → ℝ) (theta : ℝ)
    (w : Label s m → ℚ) (i : Label s m) :
    MvPolynomial.aeval (assignment p theta) (shiftedSample A w i) =
      shiftWeight (targetDelta A.toReal p theta) (fun i => (w i : ℝ)) i := by
  rcases i with r | j | aj | u <;> simp [shiftedSample,shiftWeight,eval_deltaSymbol,stateLabel]

def sample (k : Fin (interpolationSize (numberOfBodies s m) 3)) (i : Label s m) : ℚ :=
  interpolationWeight k (labelEquiv s m i)

def coefficientSymbol (A : RationalData s m) (α : MultiIndex (numberOfBodies s m) 3) :
    MvPolynomial (Parameter m) ℚ :=
  ∑ k, C (coefficientExtractionWeight α k) * formula A (shiftedSample A (sample k))

def coefficientMap (A : RationalData s m) (p : Fin m → ℝ) (theta : ℝ) :
    Coefficients (numberOfBodies s m) 3 := fun α => MvPolynomial.aeval (assignment p theta) (coefficientSymbol A α)

/-- An entirely finite rational coefficient algorithm for rational inputs. -/
def rationalArray (A : RationalData s m) (p : Fin m → ℚ) (theta : ℚ)
    (α : MultiIndex (numberOfBodies s m) 3) : ℚ :=
  ∑ k, coefficientExtractionWeight α k *
    formula A (fun i => match i with
      | .inr (.inl j) => sample k (stateLabel j) + deltaQ A p theta j*sample k deficitLabel
      | i => sample k i)

theorem coefficientSymbol_degree_le_two (A : RationalData s m) (α : MultiIndex (numberOfBodies s m) 3) :
    (coefficientSymbol A α).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro k _
  apply (degree_mul (e := 2) (degree_C _) ?_).trans (by omega)
  apply formula_degree A _
  · intro r; exact degree_C _
  · intro j
    exact degree_add ((degree_C _).trans (by omega))
      ((degree_mul (deltaSymbol_degree A j) (degree_C _)).trans (by omega))
  · intro a j; exact degree_C _

theorem coefficientMap_eq (A : RationalData s m) (hs : 0 < s) (p : Fin m → ℝ) (theta : ℝ) :
    coefficientMap A p theta = GeneralLocus.coefficientArray A.toReal hs p theta := by
  ext α
  rw [coefficientMap,coefficientSymbol,map_sum]
  rw [coefficient_eq_rational_samples (GeneralLocus.coefficientArray A.toReal hs p theta) α]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul,MvPolynomial.aeval_C,map_formula]
  rw [GeneralLocus.evaluate_coefficientArray,targetPolynomial_eval_formula]
  congr 2
  funext i
  exact eval_shiftedSample A p theta (sample k) i

theorem rationalArray_cast (A : RationalData s m) (hs : 0 < s) (p : Fin m → ℚ) (theta : ℚ) :
    (fun α => (rationalArray A p theta α : ℝ)) =
      GeneralLocus.coefficientArray A.toReal hs (fun j => (p j : ℝ)) (theta : ℝ) := by
  have hmap (u : Label s m → ℚ) :
      ((formula A u : ℚ) : ℝ) = formula A (fun i => (u i : ℝ)) := by
    simpa only [eq_ratCast] using map_formula (Algebra.ofId ℚ ℝ) A u
  ext α
  rw [rationalArray,Rat.cast_sum]
  rw [coefficient_eq_rational_samples (GeneralLocus.coefficientArray A.toReal hs (fun j => (p j : ℝ)) (theta : ℝ)) α]
  apply Finset.sum_congr rfl
  intro k _
  rw [Rat.cast_mul,hmap]
  rw [GeneralLocus.evaluate_coefficientArray,targetPolynomial_eval_formula]
  congr 2
  funext i
  rcases i with r | j | aj | u <;> simp [shiftWeight,cast_deltaQ,sample,stateLabel]

/-- Theorem 4.3: a fixed rational quadratic map in all initial-row and
cutpoint parameters, into the complete ordinary cubic coefficient array. -/
theorem theorem_4_3 (A : RationalData s m) (hs : 0 < s) :
    (∀ α : MultiIndex (numberOfBodies s m) 3, (coefficientSymbol A α).totalDegree ≤ 2) ∧
    (∀ (p : Fin m → ℝ), ProbabilityRow p → ∀ theta : ℝ, 0 < theta → theta < 1 →
      (coefficientMap A p theta ∈ VolumeLocus (numberOfBodies s m) 3 ↔
        A.toReal.UniversalCutpoint p theta)) := by
  refine ⟨coefficientSymbol_degree_le_two A,?_⟩
  intro p hp theta htheta₀ htheta₁
  rw [coefficientMap_eq A hs]
  exact GeneralLocus.coefficientArray_mem_iff A.toReal hs p hp theta htheta₀ htheta₁

end MixedVolume.RationalReduction

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/RationalReduction.lean -/

