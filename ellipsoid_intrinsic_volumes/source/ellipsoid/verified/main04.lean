module

public import ellipsoid.verified.main03
public import tau_ceti.analysis.convex.stiemke
public import Mathlib.Analysis.Calculus.Deriv.Prod

/- Generated ordinary proof stage. See audit/staged_ellipsoid_main/Main04/manifest.json. -/

@[expose] public section

section CanonicalSource30
/- Source: Ellipsoid/MatrixExtension.lean -/



noncomputable section

open Matrix
open scoped BigOperators

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def principalSelector (s : Finset ι) : Matrix s ι ℝ :=
  fun i j => if i.val = j then 1 else 0

def extendPrincipal (s : Finset ι) (A : Matrix s s ℝ) : Matrix ι ι ℝ :=
  (principalSelector s)ᵀ * A * principalSelector s

theorem extendPrincipal_apply (s : Finset ι) (A : Matrix s s ℝ) (i j : ι) :
    extendPrincipal s A i j = if hi : i ∈ s then
      if hj : j ∈ s then A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := by
  unfold extendPrincipal
  simp only [Matrix.mul_apply, Matrix.transpose_apply, principalSelector,
    Finset.sum_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · rw [dif_pos hi, dif_pos hj]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · rw [Finset.sum_eq_single ⟨i, hi⟩]
        · simp
        · intro a ha hai
          have hai' : a.val ≠ i := fun h => hai (Subtype.ext h)
          simp [hai']
        · simp
      · intro b hb hbj
        have hbj' : b.val ≠ j := fun h => hbj (Subtype.ext h)
        simp [hbj']
      · simp
    · rw [dif_pos hi, dif_neg hj]
      apply Finset.sum_eq_zero
      intro b hb
      have hbj : b.val ≠ j := fun h => hj (h ▸ b.property)
      simp [hbj]
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro b hb
    split_ifs
    · apply Finset.sum_eq_zero
      intro a ha
      have hai : a.val ≠ i := fun h => hi (h ▸ a.property)
      simp [hai]
    · rfl

theorem extendPrincipal_posSemidef (s : Finset ι) {A : Matrix s s ℝ}
    (hA : A.PosSemidef) : (extendPrincipal s A).PosSemidef := by
  simpa only [extendPrincipal, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hA.conjTranspose_mul_mul_same (principalSelector s)

end EllipsoidVerification
end
end CanonicalSource30

section CanonicalSource31
/- Source: Ellipsoid/JacobianBlocks.lean -/



noncomputable section

open Matrix Finset MeasureTheory
open scoped BigOperators

namespace EllipsoidVerification

def internalDegree {n : ℕ} (i : Fin (n - 1)) : ℝ := (i.val : ℝ) + 1

def jacobianCoefficientBlock {n : ℕ} (e : Coefficients n) (l : Fin (n + 1)) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := fun i j =>
  let k := internalDegree i
  let z := internalDegree j
  let a := (l.val : ℝ)
  if a < min k z then
    (min k z - a) * mellinMoment e (3 * min k z) *
      mellinMoment e (2 * max k z - min k z + 2 * a)
  else if max k z < a then
    (a - max k z) * mellinMoment e (3 * max k z) *
      mellinMoment e (2 * min k z - max k z + 2 * a)
  else 0

def indicesRightOf {n : ℕ} (l : Fin (n + 1)) : Finset (Fin (n - 1)) :=
  Finset.univ.filter (fun i => (l.val : ℝ) < internalDegree i)

def indicesLeftOf {n : ℕ} (l : Fin (n + 1)) : Finset (Fin (n - 1)) :=
  Finset.univ.filter (fun i => internalDegree i < (l.val : ℝ))

theorem internalDegree_pos {n : ℕ} (i : Fin (n - 1)) : 0 < internalDegree i := by
  unfold internalDegree
  positivity

theorem internalDegree_lt {n : ℕ} (i : Fin (n - 1)) : internalDegree i < n := by
  have hi : i.val + 1 < n := by omega
  unfold internalDegree
  exact_mod_cast hi

theorem internalDegree_injective {n : ℕ} : Function.Injective (@internalDegree n) := by
  intro i j hij
  apply Fin.ext
  dsimp [internalDegree] at hij
  exact_mod_cast add_right_cancel hij

theorem jacobianCoefficientBlock_split {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (l : Fin (n + 1)) :
    jacobianCoefficientBlock e l =
      extendPrincipal (indicesRightOf l)
        (orderedMomentKernel (mellinMeasure e (3 * l.val))
          (fun i : indicesRightOf l => internalDegree i.val - l.val)) +
      extendPrincipal (indicesLeftOf l)
        (orderedMomentKernel (reciprocalMellinMeasure e (3 * l.val))
          (fun i : indicesLeftOf l => (l.val : ℝ) - internalDegree i.val)) := by
  ext i j
  simp only [Matrix.add_apply, extendPrincipal_apply, indicesRightOf, indicesLeftOf,
    Finset.mem_filter, Finset.mem_univ, true_and]
  unfold jacobianCoefficientBlock orderedMomentKernel
  simp only [positiveMoment_mellinMeasure he, positiveMoment_reciprocalMellinMeasure he]
  rcases le_total (internalDegree i) (internalDegree j) with hij | hji
  · simp only [min_eq_left hij, max_eq_right hij,
      min_sub_sub_right, max_sub_sub_right, min_sub_sub_left, max_sub_sub_left]
    split_ifs <;> try simp_all
    all_goals first | (exfalso; linarith) | (congr 2 <;> ring)
  · simp only [min_eq_right hji, max_eq_left hji,
      min_sub_sub_right, max_sub_sub_right, min_sub_sub_left, max_sub_sub_left]
    split_ifs <;> try simp_all
    all_goals first | (exfalso; linarith) | (congr 2 <;> ring)

theorem jacobianCoefficientBlock_posSemidef {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) (l : Fin (n + 1)) :
    (jacobianCoefficientBlock e l).PosSemidef := by
  have hl0 : (0 : ℝ) ≤ l.val := Nat.cast_nonneg _
  have hln : (l.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ l.isLt
  have hright := orderedMomentKernel_posDef_of_injective (mellinMeasure_ne_zero hn he (3 * l.val))
    (p := fun i : indicesRightOf l => internalDegree i.val - l.val)
    (by intro i j h; apply Subtype.ext; exact internalDegree_injective (sub_left_injective h))
    (fun i => sub_pos.mpr (by simpa [indicesRightOf] using i.property))
    (fun i => integrable_mellinMeasure_power he (by nlinarith [internalDegree_pos i.val])
      (by nlinarith [internalDegree_lt i.val]))
    (fun i j hij => integrable_mellinMeasure_power he
      (by nlinarith [internalDegree_pos i.val, internalDegree_pos j.val,
        show (l.val : ℝ) < internalDegree i.val by simpa [indicesRightOf] using i.property])
      (by nlinarith [internalDegree_lt i.val, internalDegree_lt j.val,
        show (l.val : ℝ) < internalDegree i.val by simpa [indicesRightOf] using i.property]))
  have hleft := orderedMomentKernel_posDef_of_injective
    (reciprocalMellinMeasure_ne_zero hn he (3 * l.val))
    (p := fun i : indicesLeftOf l => (l.val : ℝ) - internalDegree i.val)
    (by intro i j h; apply Subtype.ext; exact internalDegree_injective (sub_right_injective h))
    (fun i => sub_pos.mpr (by simpa [indicesLeftOf] using i.property))
    (fun i => integrable_reciprocalMellinMeasure_power he
      (by nlinarith [internalDegree_pos i.val]) (by nlinarith [internalDegree_lt i.val]))
    (fun i j hij => integrable_reciprocalMellinMeasure_power he
      (by nlinarith [internalDegree_pos i.val, internalDegree_pos j.val,
        show internalDegree i.val < (l.val : ℝ) by simpa [indicesLeftOf] using i.property])
      (by nlinarith [internalDegree_lt i.val, internalDegree_lt j.val,
        show internalDegree i.val < (l.val : ℝ) by simpa [indicesLeftOf] using i.property]))
  rw [jacobianCoefficientBlock_split he]
  exact (extendPrincipal_posSemidef _ hright.posSemidef).add
    (extendPrincipal_posSemidef _ hleft.posSemidef)

theorem jacobianCoefficientBlock_zero_posDef {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) :
    (jacobianCoefficientBlock e 0).PosDef := by
  have h := orderedMomentKernel_posDef_of_injective (mellinMeasure_ne_zero hn he 0)
    (p := @internalDegree n)
    internalDegree_injective internalDegree_pos
    (fun i => integrable_mellinMeasure_power he (a := 0) (r := 3 * internalDegree i)
      (by nlinarith [internalDegree_pos i])
      (by nlinarith [internalDegree_lt i]))
    (fun i j hij => integrable_mellinMeasure_power he (a := 0)
      (r := 2 * internalDegree j - internalDegree i)
      (by nlinarith [internalDegree_pos i])
      (by nlinarith [internalDegree_pos i, internalDegree_lt j]))
  convert h using 1
  ext i j
  simp only [jacobianCoefficientBlock, Fin.val_zero, Nat.cast_zero, zero_mul, mul_zero,
    lt_min (internalDegree_pos i) (internalDegree_pos j), if_true,
    orderedMomentKernel, positiveMoment_mellinMeasure he, zero_add, sub_zero, add_zero]

end EllipsoidVerification
end
end CanonicalSource31

section CanonicalSource32
/- Source: Ellipsoid/JacobianPositivity.lean -/



noncomputable section

open Matrix Finset
open scoped BigOperators

namespace EllipsoidVerification

def jacobianHeadMoment {n : ℕ} (e : Coefficients n) (k j : Fin (n - 1)) : ℝ :=
  ∑ l : Fin (n + 1), if (l.val : ℝ) < internalDegree k then
    (internalDegree k - l.val) * e l *
      mellinMoment e (2 * internalDegree j - internalDegree k + 2 * l.val) else 0

def jacobianTailMoment {n : ℕ} (e : Coefficients n) (k j : Fin (n - 1)) : ℝ :=
  ∑ l : Fin (n + 1), if internalDegree k < (l.val : ℝ) then
    (l.val - internalDegree k) * e l *
      mellinMoment e (2 * internalDegree j - internalDegree k + 2 * l.val) else 0

/-- The diagonal uses the average of the two equal expressions. The equality
of those expressions is proved by the Mellin integration-by-parts identity. -/
def balancedJacobian {n : ℕ} (e : Coefficients n) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := fun k j =>
  if k < j then (1 / 2 : ℝ) * jacobianHeadMoment e k j
  else if j < k then (1 / 2 : ℝ) * jacobianTailMoment e k j
  else (1 / 4 : ℝ) * (jacobianHeadMoment e k j + jacobianTailMoment e k j)

def jacobianRescaling {n : ℕ} (e : Coefficients n) : Fin (n - 1) → ℝ :=
  fun k => mellinMoment e (3 * internalDegree k)

theorem jacobianRescaling_pos {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n - 1)) : 0 < jacobianRescaling e k :=
  mellinMoment_pos he (by nlinarith [internalDegree_pos k])
    (by nlinarith [internalDegree_lt k])

theorem jacobianCoefficientBlock_symm {n : ℕ} (e : Coefficients n) (l : Fin (n + 1)) :
    (jacobianCoefficientBlock e l).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, jacobianCoefficientBlock, min_comm, max_comm]

set_option backward.isDefEq.respectTransparency false in
theorem symmetricPart_balancedJacobian_decomposition {n : ℕ} (e : Coefficients n) :
    symmetricPart (Matrix.diagonal (jacobianRescaling e) * balancedJacobian e) =
      (1 / 4 : ℝ) • ∑ l : Fin (n + 1), e l • jacobianCoefficientBlock e l := by
  ext i j
  wlog hij : i ≤ j generalizing i j
  · have hji := this j i (le_of_not_ge hij)
    simpa only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Matrix.diagonal_mul, Matrix.sum_apply, smul_eq_mul,
      (jacobianCoefficientBlock_symm e _).apply, add_comm] using hji
  have hdeg : internalDegree i ≤ internalDegree j := by
    dsimp [internalDegree]
    have hnat : i.val ≤ j.val := hij
    have hreal : (i.val : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hnat
    linarith only [hreal]
  rcases eq_or_lt_of_le hij with rfl | hijlt
  · simp only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Matrix.diagonal_mul, balancedJacobian, lt_self_iff_false, if_false,
      Matrix.sum_apply, smul_eq_mul, jacobianRescaling]
    unfold jacobianHeadMoment jacobianTailMoment
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [jacobianCoefficientBlock, min_self, max_self]
    split_ifs <;> first | (exfalso; linarith) | ring
  · have hnlt : ¬ j < i := not_lt.mpr hij
    simp only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Matrix.diagonal_mul, balancedJacobian, hijlt, hnlt, if_true, if_false,
      Matrix.sum_apply, smul_eq_mul, jacobianRescaling]
    unfold jacobianHeadMoment jacobianTailMoment
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [jacobianCoefficientBlock, min_eq_left hdeg, max_eq_right hdeg]
    split_ifs <;> first | (exfalso; linarith) | ring

/-- Proposition 4.2 for the explicit, balanced derivative formula. -/
theorem symmetricPart_balancedJacobian_posDef {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) :
    (symmetricPart (Matrix.diagonal (jacobianRescaling e) * balancedJacobian e)).PosDef := by
  rw [symmetricPart_balancedJacobian_decomposition]
  apply Matrix.PosDef.smul _ (by norm_num)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
  apply Matrix.PosDef.posSemidef_add
  · apply Matrix.posSemidef_sum
    intro l hl
    exact (jacobianCoefficientBlock_posSemidef hn he l).smul (he.1 l)
  · exact (jacobianCoefficientBlock_zero_posDef hn he).smul he.2.1

theorem balancedJacobian_principal_minors_pos {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) :
    principalJacobianPositive (balancedJacobian e) := by
  intro s
  exact principal_minor_pos_of_diagonal_stability (jacobianRescaling_pos he)
    (symmetricPart_balancedJacobian_posDef hn he) s

end EllipsoidVerification
end
end CanonicalSource32

section CanonicalSource33
/- Source: Ellipsoid/JacobianBalance.lean -/



noncomputable section

open MeasureTheory Matrix Finset
open scoped BigOperators

namespace EllipsoidVerification

/-- The equality of the head and tail diagonal formulas in Lemma 4.1 is
the Mellin recurrence with parameter `s = 1/2` and exponent `r = k`. -/
theorem jacobianHeadMoment_eq_tail_diagonal {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n - 1)) :
    jacobianHeadMoment e k k = jacobianTailMoment e k k := by
  have h := coefficientMellinPower_recurrence he
    (s := (1 / 2 : ℝ)) (r := internalDegree k) (internalDegree_pos k)
    (by nlinarith [internalDegree_lt k])
  have hdiff : jacobianHeadMoment e k k - jacobianTailMoment e k k =
      ∑ l : Fin (n + 1), (internalDegree k - l.val) * e l *
        mellinMoment e (internalDegree k + 2 * l.val) := by
    unfold jacobianHeadMoment jacobianTailMoment
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show 2 * internalDegree k - internalDegree k + 2 * (l.val : ℝ) =
        internalDegree k + 2 * l.val by ring]
    rcases lt_trichotomy (l.val : ℝ) (internalDegree k) with hlt | heq | hgt
    · simp only [hlt, not_lt.mpr hlt.le, if_true, if_false, sub_zero]
    · simp [heq]
    · simp only [hgt, not_lt.mpr hgt.le, if_true, if_false, zero_sub]
      ring
  apply sub_eq_zero.mp
  rw [hdiff]
  convert h using 1
  apply Finset.sum_congr rfl
  intro l hl
  norm_num [coefficientMellinPower, mellinMoment]

theorem coefficientJacobian_eq_balancedJacobian {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) : coefficientJacobian e = balancedJacobian e := by
  funext k j
  have hh : (∑ l : Fin (n + 1), if l.val < k.val + 1 then
      (((k.val + 1 : ℕ) : ℝ) - l.val) * e l * mellinMoment e
          (2 * ((j.val + 1 : ℕ) : ℝ) - ((k.val + 1 : ℕ) : ℝ) + 2 * l.val)
      else 0) = jacobianHeadMoment e k j := by
    unfold jacobianHeadMoment
    apply Finset.sum_congr rfl
    intro l hl
    have htest : (l.val : ℝ) < internalDegree k ↔ l.val < k.val + 1 := by
      simpa only [internalDegree, Nat.cast_add, Nat.cast_one] using
        (Nat.cast_lt (α := ℝ) (m := l.val) (n := k.val + 1))
    simp only [htest]
    simp only [internalDegree, Nat.cast_add, Nat.cast_one]
  have ht : (∑ l : Fin (n + 1), if k.val + 1 < l.val then
      ((l.val : ℝ) - (k.val + 1 : ℕ)) * e l * mellinMoment e
          (2 * ((j.val + 1 : ℕ) : ℝ) - ((k.val + 1 : ℕ) : ℝ) + 2 * l.val)
      else 0) = jacobianTailMoment e k j := by
    unfold jacobianTailMoment
    apply Finset.sum_congr rfl
    intro l hl
    have htest : internalDegree k < (l.val : ℝ) ↔ k.val + 1 < l.val := by
      simpa only [internalDegree, Nat.cast_add, Nat.cast_one] using
        (Nat.cast_lt (α := ℝ) (m := k.val + 1) (n := l.val))
    simp only [htest]
    simp only [internalDegree, Nat.cast_add, Nat.cast_one]
  simp only [coefficientJacobian, hh, ht, balancedJacobian]
  rcases lt_trichotomy k j with hlt | rfl | hgt
  · simp [hlt, hlt.le]
  · rw [jacobianHeadMoment_eq_tail_diagonal he]
    simp
    ring
  · simp [hgt, not_le.mpr hgt, not_lt.mpr hgt.le]

theorem coefficientJacobian_principal_minors_pos {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) :
    principalJacobianPositive (coefficientJacobian e) := by
  rw [coefficientJacobian_eq_balancedJacobian he]
  exact balancedJacobian_principal_minors_pos hn he

end EllipsoidVerification
end
end CanonicalSource33

section CanonicalSource34
/- Source: Ellipsoid/CoefficientDerivative.lean -/



noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

theorem fderiv_mellin_product_single {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) (l j q : Fin (n + 1)) (c : ℝ)
    {r : ℝ} (hr : 0 < r) (hrn : r < 3 * n) :
    fderiv ℝ (fun e : Coefficients n => c * e l * e j * mellinMoment e r) e
      ((Pi.single q (1 : ℝ) : Coefficients n)) =
        c * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) * mellinMoment e r -
        (3 / 2 : ℝ) * c * e l * e j *
          coefficientMellinPower e (5 / 2) (r + 2 * q.val) := by
  have hm : DifferentiableAt ℝ (fun z : Coefficients n => mellinMoment z r) e :=
    (hasFDerivAt_coefficientMellinPower he hr (by nlinarith : r < 2 * n * (3 / 2 : ℝ))).differentiableAt
  have hl := hasFDerivAt_apply (𝕜 := ℝ) l e
  have hj := hasFDerivAt_apply (𝕜 := ℝ) j e
  have h := ((hl.const_mul c).fun_mul hj).fun_mul hm.hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hm' := fderiv_coefficientMellinPower_single he (s := (3 / 2 : ℝ)) hr
    (by nlinarith : r < 2 * n * (3 / 2 : ℝ)) q
  norm_num only at hm'
  change fderiv ℝ (fun z : Coefficients n => mellinMoment z r) e ((Pi.single q (1 : ℝ) : Coefficients n)) = _ at hm'
  rw [hm']
  ring

def coefficientRawDerivative {n : ℕ} (e : Coefficients n) (k : ℕ)
    (q : Fin (n + 1)) : ℝ :=
  ∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
    ((j.val : ℝ) - l.val) * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) *
        mellinMoment e (2 * (l.val : ℝ) + 2 * j.val - k) -
      (3 / 2 : ℝ) * ((j.val : ℝ) - l.val) * e l * e j *
        coefficientMellinPower e (5 / 2) (2 * (l.val : ℝ) + 2 * j.val - k + 2 * q.val)
    else 0

theorem fderiv_coefficientTransform_single_raw {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {k : ℕ} (hk : 0 < k) (hkn : k < n)
    (q : Fin (n + 1)) :
    fderiv ℝ (fun e : Coefficients n => coefficientTransform e k) e ((Pi.single q (1 : ℝ) : Coefficients n)) =
      coefficientRawDerivative e k q := by
  have hEq : (fun z : Coefficients n => coefficientTransform z k) =ᶠ[𝓝 e]
      (fun z => coefficientExpansion z k) := by
    filter_upwards [(isOpen_positiveCoefficientDomain n).mem_nhds he] with z hz
    exact coefficientTransform_eq_expansion hz hk hkn
  rw [hEq.fderiv_eq]
  have hd (l j : Fin (n + 1)) : DifferentiableAt ℝ (fun z : Coefficients n =>
      if l.val < k ∧ k ≤ j.val then ((j.val : ℝ) - l.val) * z l * z j *
        mellinMoment z (2 * (l.val : ℝ) + 2 * j.val - k) else 0) e := by
    by_cases hc : l.val < k ∧ k ≤ j.val
    · simp only [hc, true_and, and_true, if_true]
      have hm := (hasFDerivAt_coefficientMellinPower he
        (cut_moment_range hk hkn hc.1 hc.2).1
        (by nlinarith [(cut_moment_range hk hkn hc.1 hc.2).2] :
          2 * (l.val : ℝ) + 2 * j.val - k < 2 * n * (3 / 2 : ℝ))).differentiableAt
      exact (((hasFDerivAt_apply (𝕜 := ℝ) l e).differentiableAt.const_mul _).fun_mul
        (hasFDerivAt_apply (𝕜 := ℝ) j e).differentiableAt).fun_mul hm
    · simp only [hc, if_false]
      exact differentiableAt_const _
  unfold coefficientExpansion coefficientRawDerivative
  rw [fderiv_fun_sum (fun l _ => DifferentiableAt.fun_sum (fun j _ => hd l j))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro l hl
  rw [fderiv_fun_sum (fun j _ => hd l j)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : l.val < k ∧ k ≤ j.val
  · simp only [hc, true_and, and_true, if_true]
    exact fderiv_mellin_product_single he l j q _
      (cut_moment_range hk hkn hc.1 hc.2).1 (cut_moment_range hk hkn hc.1 hc.2).2
  · simp [hc]

theorem coefficientRawDerivative_split {n : ℕ} (e : Coefficients n) (k : ℕ)
    (q : Fin (n + 1)) :
    coefficientRawDerivative e k q =
      (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
        ((j.val : ℝ) - l.val) * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) *
          mellinMoment e (2 * (l.val : ℝ) + 2 * j.val - k) else 0) -
      (3 / 2 : ℝ) * ∑ l : Fin (n + 1), ∑ j : Fin (n + 1),
        if l.val < k ∧ k ≤ j.val then ((j.val : ℝ) - l.val) * e l * e j *
          coefficientMellinPower e (5 / 2) (2 * q.val - k + 2 * l.val + 2 * j.val) else 0 := by
  unfold coefficientRawDerivative
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : l.val < k ∧ k ≤ j.val
  · simp only [hc, true_and, and_true, if_true]
    rw [show 2 * (l.val : ℝ) + 2 * j.val - k + 2 * q.val =
      2 * (q.val : ℝ) - k + 2 * l.val + 2 * j.val by ring]
    ring
  · simp [hc]

theorem coefficientRawDerivative_head {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {k : ℕ} (hk : 0 < k) (hkn : k < n)
    (q : Fin (n + 1)) (hq : k ≤ q.val) (hqn : q.val < n) :
    coefficientRawDerivative e k q =
      (1 / 2 : ℝ) * ∑ l : Fin (n + 1), if l.val < k then
        ((k : ℝ) - l.val) * e l * mellinMoment e (2 * q.val - k + 2 * l.val) else 0 := by
  have hr (l : Fin (n + 1)) (hl : l.val < k) :
      0 < 2 * (q.val : ℝ) - k + 2 * l.val ∧
        2 * (q.val : ℝ) - k + 2 * l.val < 3 * n := by
    have hl0 := Nat.cast_nonneg (α := ℝ) l.val
    have hkl : (l.val : ℝ) < k := by exact_mod_cast hl
    have hkq : (k : ℝ) ≤ q.val := by exact_mod_cast hq
    have hqnr : (q.val : ℝ) < n := by exact_mod_cast hqn
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have hknr : (k : ℝ) < n := by exact_mod_cast hkn
    constructor <;> linarith
  rw [coefficientRawDerivative_split, head_cross_mellin_reduction he k
    (2 * (q.val : ℝ) - k) (fun l hl => (hr l hl).1) (fun l hl => (hr l hl).2)]
  have hd : (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
      ((j.val : ℝ) - l.val) * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) *
        mellinMoment e (2 * (l.val : ℝ) + 2 * j.val - k) else 0) =
      ∑ l : Fin (n + 1), if l.val < k then ((q.val : ℝ) - l.val) * e l *
        mellinMoment e (2 * q.val - k + 2 * l.val) else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlk : l.val < k
    · have hlq : l ≠ q := by intro h; subst h; omega
      simp only [hlk, true_and, Pi.single_eq_of_ne hlq, zero_mul, zero_add]
      rw [Finset.sum_eq_single q]
      · simp [hq, show 2 * (l.val : ℝ) + 2 * q.val - k =
          2 * (q.val : ℝ) - k + 2 * l.val by ring]
      · intro j hj hjq
        simp [Pi.single_eq_of_ne hjq]
      · simp
    · simp [hlk]
  rw [hd, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlk : l.val < k <;> simp only [hlk, if_true, if_false, mul_zero, sub_zero] <;> ring

theorem coefficientRawDerivative_tail {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {k : ℕ} (hk : 0 < k) (hkn : k < n)
    (q : Fin (n + 1)) (hq0 : 0 < q.val) (hq : q.val < k) :
    coefficientRawDerivative e k q =
      (1 / 2 : ℝ) * ∑ j : Fin (n + 1), if k < j.val then
        ((j.val : ℝ) - k) * e j * mellinMoment e (2 * q.val - k + 2 * j.val) else 0 := by
  have hr (j : Fin (n + 1)) (hj : k ≤ j.val) :
      0 < 2 * (q.val : ℝ) - k + 2 * j.val ∧
        2 * (q.val : ℝ) - k + 2 * j.val < 3 * n := by
    have hq0r : (0 : ℝ) < q.val := by exact_mod_cast hq0
    have hqk : (q.val : ℝ) < k := by exact_mod_cast hq
    have hkj : (k : ℝ) ≤ j.val := by exact_mod_cast hj
    have hjn : (j.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hknr : (k : ℝ) < n := by exact_mod_cast hkn
    constructor <;> linarith
  rw [coefficientRawDerivative_split, tail_cross_mellin_reduction he k
    (2 * (q.val : ℝ) - k) (fun j hj => (hr j hj).1) (fun j hj => (hr j hj).2)]
  have hd : (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
      ((j.val : ℝ) - l.val) * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) *
        mellinMoment e (2 * (l.val : ℝ) + 2 * j.val - k) else 0) =
      ∑ j : Fin (n + 1), if k ≤ j.val then ((j.val : ℝ) - q.val) * e j *
        mellinMoment e (2 * q.val - k + 2 * j.val) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjk : k ≤ j.val
    · have hjq : j ≠ q := by intro h; subst h; omega
      simp only [hjk, and_true, Pi.single_eq_of_ne hjq, mul_zero, add_zero]
      rw [Finset.sum_eq_single q]
      · simp [hq, show 2 * (q.val : ℝ) + 2 * j.val - k =
          2 * (q.val : ℝ) - k + 2 * j.val by ring]
      · intro l hl hlq
        simp [Pi.single_eq_of_ne hlq]
      · simp
    · simp [hjk]
  rw [hd, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rcases lt_trichotomy k j.val with hlt | heq | hgt
  · simp only [hlt, hlt.le, if_true]
    ring
  · simp [← heq]
    ring
  · simp [not_le.mpr hgt, not_lt.mpr hgt.le]

/-- The Jacobian formula is now identified with the derivative of the literal
improper integral. It is not an independently stipulated matrix. -/
theorem fderiv_coefficientTransform_single {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k q : Fin (n - 1)) :
    fderiv ℝ (fun e : Coefficients n => coefficientTransform e (k.val + 1)) e
      (Pi.single (⟨q.val + 1, by omega⟩ : Fin (n + 1)) 1) = coefficientJacobian e k q := by
  rw [fderiv_coefficientTransform_single_raw (admissible_mem_positiveCoefficientDomain he)
    (by omega) (by omega)]
  unfold coefficientJacobian
  dsimp only
  have hkbound := k.isLt
  have hqbound := q.isLt
  by_cases hkq : k ≤ q
  · rw [if_pos hkq, coefficientRawDerivative_head (k := k.val + 1) he
      (by omega) (by omega) (⟨q.val + 1, by omega⟩ : Fin (n + 1))
      (by change k.val + 1 ≤ q.val + 1; exact Nat.add_le_add_right hkq 1)
      (by change q.val + 1 < n; omega)]
  · rw [if_neg hkq, coefficientRawDerivative_tail (k := k.val + 1) he
      (by omega) (by omega) (⟨q.val + 1, by omega⟩ : Fin (n + 1))
      (by change 0 < q.val + 1; omega)
      (by change q.val + 1 < k.val + 1; exact Nat.add_lt_add_right (lt_of_not_ge hkq) 1)]

end EllipsoidVerification
end
end CanonicalSource34

section CanonicalSource35
/- Source: Ellipsoid/DiagonalStability.lean -/



noncomputable section

open Matrix Finset
open scoped BigOperators

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def DiagonallyStable (A : Matrix ι ι ℝ) : Prop :=
  ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
    (symmetricPart (Matrix.diagonal d * A)).PosDef

theorem DiagonallyStable.exists_positive_coordinate {A : Matrix ι ι ℝ}
    (hA : DiagonallyStable A) {x : ι → ℝ} (hx : x ≠ 0) :
    ∃ i, 0 < x i * (A *ᵥ x) i := by
  obtain ⟨d, hd, hpd⟩ := hA
  have hp := quadratic_pos_of_symmetricPart_posDef hpd hx
  by_contra h
  push_neg at h
  have hsum : ∑ i, d i * (x i * (A *ᵥ x) i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hd i).le (h i)
  have heq : x ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ x) =
      ∑ i, d i * (x i * (A *ᵥ x) i) := by
    simp only [← Matrix.mulVec_mulVec, dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq] at hp
  exact (not_lt_of_ge hsum) hp

theorem DiagonallyStable.no_nonnegative_transpose_reverse {A : Matrix ι ι ℝ}
    (hA : DiagonallyStable A) {y : ι → ℝ}
    (hy : 0 ≤ y) (hAy : Aᵀ *ᵥ y ≤ 0) : y = 0 := by
  obtain ⟨d, hd, hpd⟩ := hA
  let x : ι → ℝ := fun i => y i / d i
  have hx : 0 ≤ x := fun i => div_nonneg (hy i) (hd i).le
  by_contra hy0
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hy0
    funext i
    have hi := congrFun hx0 i
    exact (div_eq_zero_iff).mp hi |>.resolve_right (hd i).ne'
  have hp := quadratic_pos_of_symmetricPart_posDef hpd hx0
  have hsum : (Aᵀ *ᵥ y) ⬝ᵥ x ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hAy i) (hx i)
  have heq : x ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ x) = (Aᵀ *ᵥ y) ⬝ᵥ x := by
    simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_mul,
      Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [x]
    field_simp [(hd i).ne', (hd j).ne']
  rw [heq] at hp
  exact (not_lt_of_ge hsum) hp

def alternativeGraph (A : Matrix ι ι ℝ) : (ι → ℝ) →ₗ[ℝ] (ι ⊕ ι → ℝ) where
  toFun y := Sum.elim (fun i => -(Aᵀ *ᵥ y) i) y
  map_add' x y := by
    funext i
    cases i <;> simp [Matrix.mulVec_add, add_comm]
  map_smul' r y := by
    funext i
    cases i <;> simp [Matrix.mulVec_smul, mul_neg]

/-- The positive direction used in the rectangle univalence proof is
derived from Stiemke's theorem of the alternative, not assumed. -/
theorem DiagonallyStable.exists_pos_mulVec_pos {A : Matrix ι ι ℝ}
    (hA : DiagonallyStable A) :
    ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ ∀ i, 0 < (A *ᵥ v) i := by
  have hcone : ∀ z ∈ (alternativeGraph A).range, (0 : ι ⊕ ι → ℝ) ≤ z → z = 0 := by
    rintro z ⟨y, rfl⟩ hz
    have hy : 0 ≤ y := fun i => hz (Sum.inr i)
    have hAy : Aᵀ *ᵥ y ≤ 0 := fun i => by
      have hi := hz (Sum.inl i)
      simpa only [alternativeGraph, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
        Pi.zero_apply, neg_nonneg] using hi
    have hy0 := hA.no_nonnegative_transpose_reverse hy hAy
    simp [hy0]
  obtain ⟨w, hw, horth⟩ := TauCeti.exists_pos_forall_sum_mul_eq_zero_iff.mpr hcone
  refine ⟨fun i => w (Sum.inl i), fun i => hw _, fun j => ?_⟩
  have hj := horth (alternativeGraph A (Pi.single j 1)) ⟨Pi.single j 1, rfl⟩
  have heq : (A *ᵥ (fun i => w (Sum.inl i))) j = w (Sum.inr j) := by
    simp only [Fintype.sum_sum_type, alternativeGraph, LinearMap.coe_mk, AddHom.coe_mk,
      Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, mul_neg, Finset.sum_neg_distrib] at hj
    dsimp [Matrix.mulVec, dotProduct]
    have hcomm : (∑ i, w (Sum.inl i) * A j i) = ∑ i, A j i * w (Sum.inl i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hcomm] at hj
    linarith
  rw [heq]
  exact hw (Sum.inr j)

theorem DiagonallyStable.submatrix {A : Matrix ι ι ℝ} (hA : DiagonallyStable A)
    (s : Finset ι) :
    DiagonallyStable (A.submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
  obtain ⟨d, hd, hpd⟩ := hA
  refine ⟨fun i => d i.val, fun i => hd i.val, ?_⟩
  have h := hpd.submatrix (e := fun i : s => i.val) (fun a b h => Subtype.ext h)
  convert h using 1
  ext i j
  simp [symmetricPart, Matrix.diagonal_mul, mul_add]

end EllipsoidVerification
end
end CanonicalSource35

section CanonicalSource36
/- Source: Ellipsoid/RectangleIsolation.lean -/



noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixDerivative (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  A.toLin'.toContinuousLinearMap

@[simp] theorem matrixDerivative_apply (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    matrixDerivative A x = A *ᵥ x := rfl

def weightedPair (d x y : ι → ℝ) : ℝ := ∑ i, d i * x i * y i

theorem weightedPair_bound (d x y : ι → ℝ) :
    |weightedPair d x y| ≤ (∑ i, |d i|) * ‖x‖ * ‖y‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_mul]
  have hx : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x i)
  have hy : |y i| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y i)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hx (abs_nonneg _)) hy
    (abs_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))

theorem weightedPair_matrix (A : Matrix ι ι ℝ) (d x : ι → ℝ) :
    weightedPair d x (A *ᵥ x) = x ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ x) := by
  simp only [weightedPair, ← Matrix.mulVec_mulVec, dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem quadratic_uniform_lower {A : Matrix ι ι ℝ}
    (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ι → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) := by
  have hcont : Continuous (fun x : ι → ℝ => x ⬝ᵥ (A *ᵥ x)) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨c, hc, hbound⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_forall_le'
    hcont.continuousOn (fun x hx => hA x (by
      intro hx0
      simpa [hx0] using hx))
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hunit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [Metric.mem_sphere, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), hn.ne']
  have hb := hbound _ hunit
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hb
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)
  convert hh using 1
  field_simp [hn.ne'] <;> ring

/-- At a lower corner, a differentiable map with diagonally stable
derivative cannot return to the lower image orthant arbitrarily nearby. -/
theorem isolated_lower_corner {F : (ι → ℝ) → (ι → ℝ)} {a : ι → ℝ}
    {A : Matrix ι ι ℝ} (hF : HasFDerivAt F (matrixDerivative A) a)
    (hA : DiagonallyStable A) :
    ∀ᶠ x in 𝓝 a, a ≤ x → F x ≤ F a → x = a := by
  obtain ⟨d, hd, hpd⟩ := hA
  obtain ⟨c, hc, hcoerce⟩ := quadratic_uniform_lower
    (fun x hx => quadratic_pos_of_symmetricPart_posDef hpd hx)
  let B : ℝ := max (∑ i, |d i|) 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have heps : 0 < c / (2 * B) := div_pos hc (by positivity)
  filter_upwards [hF.isLittleO.def heps] with x hx hax hFx
  by_contra hxa
  let v := x - a
  let e := F x - F a - A *ᵥ v
  have hv : 0 ≤ v := fun i => sub_nonneg.mpr (hax i)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
  have hnegative : weightedPair d v (F x - F a) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hd i).le (hv i)) (sub_nonpos.mpr (hFx i))
  have herror : ‖e‖ ≤ c / (2 * B) * ‖v‖ := hx
  have hsplit : weightedPair d v e = weightedPair d v (F x - F a) -
      v ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ v) := by
    rw [← weightedPair_matrix]
    simp only [weightedPair, e, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hquad : v ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ v) ≤ |weightedPair d v e| := by
    calc
      v ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ v) ≤ -weightedPair d v e := by
        rw [hsplit]
        linarith
      _ ≤ |weightedPair d v e| := neg_le_abs _
  have hpair : |weightedPair d v e| ≤ B * ‖v‖ * ‖e‖ :=
    (weightedPair_bound d v e).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v)) (norm_nonneg e))
  have htotal := (hcoerce v).trans (hquad.trans hpair)
  have hupper := mul_le_mul_of_nonneg_left herror (by positivity : 0 ≤ B * ‖v‖)
  have halgebra : B * ‖v‖ * (c / (2 * B) * ‖v‖) = c / 2 * ‖v‖ ^ 2 := by
    field_simp [hB.ne'] <;> ring
  rw [halgebra] at hupper
  have hfinal := htotal.trans hupper
  nlinarith [mul_pos hc (sq_pos_of_pos hvpos)]

end EllipsoidVerification
end
end CanonicalSource36

section CanonicalSource37
/- Source: Ellipsoid/RectangleFaces.lean -/



noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def faceLinear (s : Finset ι) : (s → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => if h : i ∈ s then ContinuousLinearMap.proj ⟨i, h⟩ else 0

def faceRestrict (s : Finset ι) : (ι → ℝ) →L[ℝ] (s → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.val

def faceInsert (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) : ι → ℝ :=
  fun i => if h : i ∈ s then y ⟨i, h⟩ else a i

theorem faceInsert_eq_affine (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) :
    faceInsert a s y = faceLinear s y + (fun i => if i ∈ s then 0 else a i) := by
  funext i
  simp [faceInsert, faceLinear]
  split_ifs <;> simp

@[fun_prop] theorem continuous_faceInsert (a : ι → ℝ) (s : Finset ι) :
    Continuous (faceInsert a s) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ s
  · simpa only [faceInsert, dif_pos hi] using
      (continuous_apply (⟨i, hi⟩ : s))
  · simpa only [faceInsert, dif_neg hi] using
      (continuous_const : Continuous (fun _ : s → ℝ => a i))

theorem hasFDerivAt_faceInsert (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) :
    HasFDerivAt (faceInsert a s) (faceLinear s) y := by
  simpa only [← faceInsert_eq_affine] using (faceLinear s).hasFDerivAt.add_const
    (fun i => if i ∈ s then (0 : ℝ) else a i)

@[simp] theorem faceInsert_restrict_self (a : ι → ℝ) (s : Finset ι) :
    faceInsert a s (faceRestrict s a) = a := by
  funext i
  simp [faceInsert, faceRestrict]

@[simp] theorem faceRestrict_insert (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) :
    faceRestrict s (faceInsert a s y) = y := by
  funext i
  simp [faceInsert, faceRestrict, i.property]

theorem faceInsert_mem_box {a b : ι → ℝ} (hab : a ≤ b) (s : Finset ι)
    {y : s → ℝ} (hy : y ∈ Icc (faceRestrict s a) (faceRestrict s b)) :
    faceInsert a s y ∈ Icc a b := by
  constructor <;> intro i <;> by_cases hi : i ∈ s
  · simpa [faceInsert, hi, faceRestrict] using hy.1 ⟨i, hi⟩
  · simp [faceInsert, hi]
  · simpa [faceInsert, hi, faceRestrict] using hy.2 ⟨i, hi⟩
  · simpa [faceInsert, hi] using hab i

set_option backward.isDefEq.respectTransparency false in
theorem faceDerivative_matrix (s : Finset ι) (A : Matrix ι ι ℝ) :
    (faceRestrict s).comp ((matrixDerivative A).comp (faceLinear s)) =
      matrixDerivative (A.submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
  obtain ⟨B, rfl⟩ := (Matrix.of : (ι → ι → ℝ) ≃ Matrix ι ι ℝ).surjective A
  ext y i
  simp only [ContinuousLinearMap.comp_apply, faceRestrict, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply, matrixDerivative_apply, Matrix.mulVec, dotProduct,
    Matrix.submatrix_apply, Matrix.of_apply, faceLinear, dite_apply,
    ContinuousLinearMap.zero_apply, mul_dite, mul_zero]
  trans ∑ j : ι, if h : j ∈ s then B i.val j * y ⟨j, h⟩ else 0
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j ∈ s
    · simp only [dif_pos h, ContinuousLinearMap.proj_apply]
    · simp only [dif_neg h, ContinuousLinearMap.zero_apply, mul_zero]
  · simpa only [Finset.univ_eq_attach] using
      (Finset.sum_attach_eq_sum_dite s (fun j : s => B i.val j.val * y j)).symm

def faceMap (F : (ι → ℝ) → (ι → ℝ)) (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) : s → ℝ :=
  faceRestrict s (F (faceInsert a s y))

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_faceMap {F : (ι → ℝ) → (ι → ℝ)} {a : ι → ℝ}
    (s : Finset ι) {y : s → ℝ} {A : Matrix ι ι ℝ}
    (hF : HasFDerivAt F (matrixDerivative A) (faceInsert a s y)) :
    HasFDerivAt (faceMap F a s)
      (matrixDerivative (A.submatrix (fun i : s => i.val) (fun i : s => i.val))) y := by
  change HasFDerivAt ((faceRestrict s) ∘ (F ∘ (faceInsert a s)))
    (matrixDerivative (A.submatrix (fun i : s => i.val) (fun i : s => i.val))) y
  exact ((faceRestrict s).hasFDerivAt.comp y
    (hF.comp y (hasFDerivAt_faceInsert a s y))).congr_fderiv
      (faceDerivative_matrix s A)

theorem continuousOn_faceMap {F : (ι → ℝ) → (ι → ℝ)} {a b : ι → ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b)) (s : Finset ι) :
    ContinuousOn (faceMap F a s) (Icc (faceRestrict s a) (faceRestrict s b)) := by
  exact (faceRestrict s).continuous.comp_continuousOn
    (hF.comp (continuous_faceInsert a s).continuousOn (fun y hy => faceInsert_mem_box hab s hy))

end EllipsoidVerification
end
end CanonicalSource37

section CanonicalSource38
/- Source: Ellipsoid/RectangleDescent.lean -/



noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eventually_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hd : d < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
  have h := hf.tendsto_slope_zero_right.eventually (Iio_mem_nhds hd)
  filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
  simp only [zero_add, smul_eq_mul] at ht
  exact sub_neg.mp (neg_of_mul_neg_right ht (inv_nonneg.mpr ht0.le))

set_option backward.isDefEq.respectTransparency false in
/-- At a point strictly above the lower corner, diagonal stability gives
a simultaneous descent of all coordinates and all output coordinates. -/
theorem rectangle_strict_descent [Nonempty ι]
    {F : (ι → ℝ) → (ι → ℝ)} {a c : ι → ℝ} {A : Matrix ι ι ℝ}
    (hac : ∀ i, a i < c i) (hF : HasFDerivAt F (matrixDerivative A) c)
    (hA : DiagonallyStable A) {U : Set (ι → ℝ)} (hU : U ∈ 𝓝 c) :
    ∃ z ∈ U, a ≤ z ∧ z ≤ c ∧ F z ≤ F c ∧ (∑ i, z i) < ∑ i, c i := by
  obtain ⟨v, hv, hAv⟩ := hA.exists_pos_mulVec_pos
  let line : ℝ → (ι → ℝ) := fun t => c - t • v
  have hline : HasDerivAt line (-v) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_sub c
    change HasDerivAt (fun t : ℝ => c - t • v) (-v) 0
    exact h.congr_deriv (by rw [one_smul])
  have hcomp : HasDerivAt (fun t => F (line t)) (-(A *ᵥ v)) 0 := by
    have hFline : HasFDerivAt F (matrixDerivative A) (line 0) := by
      simpa only [line, zero_smul, sub_zero] using hF
    have hh := hFline.comp_hasDerivAt 0 hline
    change HasDerivAt (F ∘ line) (-(A *ᵥ v)) 0
    exact hh.congr_deriv (by rw [matrixDerivative_apply, Matrix.mulVec_neg])
  have hdecrease : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, F (line t) i < F c i := by
    apply Filter.eventually_all.mpr
    intro i
    have hh := eventually_lt_of_hasDerivAt_neg ((hasDerivAt_pi.mp hcomp) i)
      (neg_lt_zero.mpr (hAv i))
    simpa [line] using hh
  have hlower : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, a i < line t i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℝ => line t i) 0 := by dsimp [line]; fun_prop
    have hh := hc.eventually (Ioi_mem_nhds (show a i < line 0 i by simpa [line] using hac i))
    exact hh.filter_mono nhdsWithin_le_nhds
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), line t ∈ U := by
    have hc : ContinuousAt line 0 := hline.continuousAt
    have hh := hc.eventually (show U ∈ 𝓝 (line 0) by simpa [line] using hU)
    exact hh.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hlow, hdec, hmemt⟩ :=
    (hpos.and (hlower.and (hdecrease.and hmem))).exists
  refine ⟨line t, hmemt, fun i => (hlow i).le, fun i => ?_,
    fun i => (hdec i).le, ?_⟩
  · change c i - t * v i ≤ c i
    nlinarith [mul_pos ht (hv i)]
  · have hsum : 0 < ∑ i, v i :=
      Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty
    simp only [line, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    nlinarith [mul_pos ht hsum]

end EllipsoidVerification
end
end CanonicalSource38

section CanonicalSource39
/- Source: Ellipsoid/RectangleCorner.lean -/



noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The lower-corner form of rectangle univalence. Its proof uses a compact
minimal counterexample and induction over faces, including all boundary
points. Diagonal stability is proved for the paper's actual Jacobian in the
analytic branch; it is not an extra hypothesis on the principal theorem. -/
theorem rectangle_corner_order
    {F : (ι → ℝ) → (ι → ℝ)} {A : (ι → ℝ) → Matrix ι ι ℝ}
    {a b : ι → ℝ} (hab : a ≤ b)
    (hF : ∀ z ∈ Icc a b, HasFDerivAt F (matrixDerivative (A z)) z)
    (hA : ∀ z ∈ Icc a b, DiagonallyStable (A z))
    {x : ι → ℝ} (hx : x ∈ Icc a b) (hFx : F x ≤ F a) : x = a := by
  classical
  induction hcard : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | h N ih =>
    by_contra hxa
    let S : Set (ι → ℝ) := Icc a b ∩ F ⁻¹' Iic (F a)
    have hcont : ContinuousOn F (Icc a b) := fun z hz =>
      (hF z hz).continuousAt.continuousWithinAt
    have hclosed : IsClosed S :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
    have hnear := isolated_lower_corner (hF a ⟨le_rfl, hab⟩) (hA a ⟨le_rfl, hab⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
    have haway {z : ι → ℝ} (hz : z ∈ S) (hz0 : z ≠ a) : ε ≤ dist z a := by
      by_contra h
      exact hz0 (hball (show z ∈ Metric.ball a ε by
        simpa only [Metric.mem_ball] using lt_of_not_ge h) hz.1.1 hz.2)
    let T : Set (ι → ℝ) := S \ Metric.ball a (ε / 2)
    have hT : IsCompact T := hcompact.diff Metric.isOpen_ball
    have hxT : x ∈ T := by
      refine ⟨⟨hx, hFx⟩, ?_⟩
      have hh := haway ⟨hx, hFx⟩ hxa
      simp only [Metric.mem_ball]
      linarith
    obtain ⟨c, hc, hmin⟩ := hT.exists_isMinOn ⟨x, hxT⟩
      (show ContinuousOn (fun z : ι → ℝ => ∑ i, z i) T by fun_prop)
    have hcS : c ∈ S := hc.1
    have hc0 : c ≠ a := by
      intro hc0
      have hh := hc.2
      simp [hc0, half_pos hε] at hh
    have hclower : ∀ i, a i < c i := by
      intro i
      by_contra hci
      have hcieq : c i = a i := le_antisymm (le_of_not_gt hci) (hcS.1.1 i)
      let s : Finset ι := Finset.univ.erase i
      have hsCard : Fintype.card s < N := by
        rw [Fintype.card_coe, ← hcard]
        exact Finset.card_erase_lt_of_mem (Finset.mem_univ i)
      have hinsert : faceInsert a s (faceRestrict s c) = c := by
        funext j
        by_cases hj : j ∈ s
        · simp [faceInsert, faceRestrict, hj]
        · have hji : j = i := by simpa [s] using hj
          subst j
          simp [faceInsert, s, hcieq]
      have hfaces := ih (Fintype.card s) hsCard (ι := s)
        (F := faceMap F a s)
        (A := fun y => (A (faceInsert a s y)).submatrix
          (fun j : s => j.val) (fun j : s => j.val))
        (a := faceRestrict s a) (b := faceRestrict s b)
        (fun j => hab j.val)
        (fun y hy => hasFDerivAt_faceMap s (hF _ (faceInsert_mem_box hab s hy)))
        (fun y hy => (hA _ (faceInsert_mem_box hab s hy)).submatrix s)
        (x := faceRestrict s c)
        (show faceRestrict s c ∈ Icc (faceRestrict s a) (faceRestrict s b) from
          ⟨fun j => hcS.1.1 j.val, fun j => hcS.1.2 j.val⟩)
        (by
          simp only [faceMap, hinsert, faceInsert_restrict_self]
          exact fun j => hcS.2 j.val)
        rfl
      apply hc0
      funext j
      by_cases hji : j = i
      · simpa [hji] using hcieq
      · exact congrFun hfaces ⟨j, by simpa [s] using hji⟩
    cases isEmpty_or_nonempty ι with
    | inl hi =>
      letI := hi
      exact hc0 (Subsingleton.elim c a)
    | inr hi =>
      letI := hi
      have hdist := haway hcS hc0
      let U : Set (ι → ℝ) := {z | ε / 2 < dist z a}
      have hU : U ∈ 𝓝 c :=
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
          (show c ∈ U by dsimp [U]; linarith)
      obtain ⟨z, hzU, haz, hzc, hFzc, hsum⟩ := rectangle_strict_descent hclower
        (hF c hcS.1) (hA c hcS.1) hU
      have hzT : z ∈ T := by
        refine ⟨⟨⟨haz, hzc.trans hcS.1.2⟩, hFzc.trans hcS.2⟩, ?_⟩
        have hzdist : ε / 2 < dist z a := hzU
        exact fun hz => (not_lt_of_ge hzdist.le) (Metric.mem_ball.mp hz)
      exact (not_lt_of_ge (hmin hzT)) hsum

end EllipsoidVerification
end
end CanonicalSource39
