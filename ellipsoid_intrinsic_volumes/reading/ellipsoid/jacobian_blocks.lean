module

public import Ellipsoid.MellinMeasures
public import Ellipsoid.MatrixExtension

@[expose] public section

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
