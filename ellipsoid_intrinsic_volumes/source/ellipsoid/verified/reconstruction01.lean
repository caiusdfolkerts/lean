module

public import ellipsoid.verified.main04

/- Generated ordinary proof stage. See audit/staged_ellipsoid_reconstruction/Reconstruction01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Ellipsoid/RectangleUnivalence.lean -/



noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixDerivative_mul (A B : Matrix ι ι ℝ) :
    matrixDerivative (A * B) = (matrixDerivative A).comp (matrixDerivative B) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, matrixDerivative_apply, Matrix.mulVec_mulVec]

theorem DiagonallyStable.sign_conjugate {A : Matrix ι ι ℝ} (hA : DiagonallyStable A)
    (s : ι → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    DiagonallyStable (Matrix.diagonal s * A * Matrix.diagonal s) := by
  obtain ⟨d, hd, hpd⟩ := hA
  refine ⟨d, hd, ?_⟩
  have hinj : Function.Injective (Matrix.diagonal s : Matrix ι ι ℝ).mulVec := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    simp only [Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (by rcases hs i with h | h <;> simp [h]) hi
  have h := hpd.conjTranspose_mul_mul_same hinj
  simp only [Matrix.diagonal_conjTranspose, star_trivial] at h
  convert h using 1
  ext i j
  simp only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    star_trivial, smul_eq_mul, Matrix.diagonal_apply]
  ring

def comparisonSigns (x y : ι → ℝ) : ι → ℝ :=
  fun i => if x i ≤ y i then 1 else -1

theorem comparisonSigns_values (x y : ι → ℝ) (i : ι) :
    comparisonSigns x y i = 1 ∨ comparisonSigns x y i = -1 := by
  unfold comparisonSigns
  split_ifs <;> simp

def comparisonWidths (x y : ι → ℝ) : ι → ℝ := fun i => |y i - x i|

theorem comparisonSigns_widths (x y : ι → ℝ) :
    x + (Matrix.diagonal (comparisonSigns x y) *ᵥ comparisonWidths x y) = y := by
  funext i
  simp only [Pi.add_apply, Matrix.mulVec_diagonal, comparisonWidths, comparisonSigns]
  by_cases hi : x i ≤ y i
  · rw [if_pos hi, abs_of_nonneg (sub_nonneg.mpr hi)]
    ring
  · rw [if_neg hi, abs_of_neg (sub_neg.mpr (lt_of_not_ge hi))]
    ring

theorem comparison_box_maps {a b x y : ι → ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    {z : ι → ℝ} (hz : z ∈ Icc 0 (comparisonWidths x y)) :
    x + Matrix.diagonal (comparisonSigns x y) *ᵥ z ∈ Icc a b := by
  constructor <;> intro i
  all_goals
    have hz0 := hz.1 i
    have hz1 := hz.2 i
    simp only [Pi.zero_apply, comparisonWidths] at hz0 hz1
    simp only [Pi.add_apply, Matrix.mulVec_diagonal, comparisonSigns]
    by_cases hi : x i ≤ y i
    · rw [if_pos hi]
      rw [abs_of_nonneg (sub_nonneg.mpr hi)] at hz1
      nlinarith [hx.1 i, hx.2 i, hy.1 i, hy.2 i]
    · rw [if_neg hi]
      rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hi))] at hz1
      nlinarith [hx.1 i, hx.2 i, hy.1 i, hy.2 i]

set_option backward.isDefEq.respectTransparency false in
/-- Rectangle univalence in the form required by the coefficient proof.
The derivative is taken in a neighborhood of every point of the closed
rectangle; the conclusion includes all its faces and repeated-root data. -/
theorem injOn_rectangle_of_diagonal_stability
    {F : (ι → ℝ) → (ι → ℝ)} {A : (ι → ℝ) → Matrix ι ι ℝ} {a b : ι → ℝ}
    (hF : ∀ z ∈ Icc a b, HasFDerivAt F (matrixDerivative (A z)) z)
    (hA : ∀ z ∈ Icc a b, DiagonallyStable (A z)) : Set.InjOn F (Icc a b) := by
  intro x hx y hy hxy
  let S : Matrix ι ι ℝ := Matrix.diagonal (comparisonSigns x y)
  let T : (ι → ℝ) → (ι → ℝ) := fun z => x + S *ᵥ z
  let G : (ι → ℝ) → (ι → ℝ) := fun z => S *ᵥ F (T z)
  let B : (ι → ℝ) → Matrix ι ι ℝ := fun z => S * A (T z) * S
  have hT (z : ι → ℝ) : HasFDerivAt T (matrixDerivative S) z := by
    simpa [T] using (matrixDerivative S).hasFDerivAt.const_add x
  have hG (z : ι → ℝ) (hz : z ∈ Icc 0 (comparisonWidths x y)) :
      HasFDerivAt G (matrixDerivative (B z)) z := by
    have hTz := comparison_box_maps hx hy hz
    have h := (matrixDerivative S).hasFDerivAt.comp z ((hF (T z) hTz).comp z (hT z))
    simpa only [G, B, Function.comp_def, matrixDerivative_mul,
      ContinuousLinearMap.comp_assoc, matrixDerivative_apply] using h
  have hB (z : ι → ℝ) (hz : z ∈ Icc 0 (comparisonWidths x y)) : DiagonallyStable (B z) :=
    (hA (T z) (comparison_box_maps hx hy hz)).sign_conjugate
      (comparisonSigns x y) (comparisonSigns_values x y)
  have hw0 : (0 : ι → ℝ) ≤ comparisonWidths x y := fun i => abs_nonneg _
  have hGh : G (comparisonWidths x y) = G 0 := by
    have ht : T (comparisonWidths x y) = y := comparisonSigns_widths x y
    simp only [G, ht, T, Matrix.mulVec_zero, add_zero, hxy]
  have hw := rectangle_corner_order hw0 hG hB ⟨hw0, le_rfl⟩ hGh.le
  funext i
  have hi := congrFun hw i
  exact (sub_eq_zero.mp (abs_eq_zero.mp hi)).symm

end EllipsoidVerification
end
end CanonicalSource0

section CanonicalSource1
/- Source: Ellipsoid/CoefficientInjectivity.lean -/



noncomputable section

open Set Matrix Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def internalCoefficientInclusion (m : ℕ) : (Fin m → ℝ) →L[ℝ] Coefficients (m + 1) :=
  ContinuousLinearMap.pi fun j =>
    if h0 : j.val = 0 then 0 else if hn : j.val = m + 1 then 0 else
      ContinuousLinearMap.proj ⟨j.val - 1, by omega⟩

theorem fixedEndpoints_eq_affine (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    fixedEndpoints m e0 en x = fixedEndpoints m e0 en 0 + internalCoefficientInclusion m x := by
  funext j
  simp only [fixedEndpoints, internalCoefficientInclusion,
    ContinuousLinearMap.pi_apply, Pi.add_apply]
  split_ifs <;> simp

theorem internalCoefficientInclusion_single (m : ℕ) (q : Fin m) :
    internalCoefficientInclusion m (Pi.single q 1) =
      Pi.single (⟨q.val + 1, by omega⟩ : Fin (m + 2)) 1 := by
  let q' : Fin (m + 1 + 1) := ⟨q.val + 1, by omega⟩
  change _ = (Pi.single q' 1 : Coefficients (m + 1))
  funext j
  simp only [internalCoefficientInclusion, ContinuousLinearMap.pi_apply]
  by_cases h0 : j.val = 0
  · have hne : j ≠ q' := by
      intro h
      have hh : j.val = q.val + 1 := congrArg Fin.val h
      omega
    simp only [dif_pos h0, ContinuousLinearMap.zero_apply, Pi.single_eq_of_ne hne]
  by_cases hn : j.val = m + 1
  · have hne : j ≠ q' := by
      intro h
      have hh : j.val = q.val + 1 := congrArg Fin.val h
      have hq := q.isLt
      omega
    simp only [dif_neg h0, dif_pos hn, ContinuousLinearMap.zero_apply,
      Pi.single_eq_of_ne hne]
  simp only [dif_neg h0, dif_neg hn, ContinuousLinearMap.proj_apply]
  let j' : Fin m := ⟨j.val - 1, by have hj := j.isLt; omega⟩
  change (Pi.single q 1 : Fin m → ℝ) j' =
    (Pi.single q' 1 : Coefficients (m + 1)) j
  by_cases hj : j = q'
  · have hp : j' = q := by
      apply Fin.ext
      have hh : j.val = q.val + 1 := congrArg Fin.val hj
      change j.val - 1 = q.val
      omega
    rw [hp, hj]
    simp
  · have hp : j' ≠ q := by
      intro h
      have hh : j.val - 1 = q.val := congrArg Fin.val h
      apply hj
      apply Fin.ext
      change j.val = q.val + 1
      omega
    simp only [Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hj]

theorem hasFDerivAt_fixedEndpoints (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    HasFDerivAt (fixedEndpoints m e0 en) (internalCoefficientInclusion m) x := by
  have h : HasFDerivAt
      (fun y => fixedEndpoints m e0 en 0 + internalCoefficientInclusion m y)
      (internalCoefficientInclusion m) x :=
    ((internalCoefficientInclusion m).hasFDerivAt (x := x)).const_add
      (fixedEndpoints m e0 en 0)
  simpa only [← fixedEndpoints_eq_affine] using h

@[fun_prop] theorem continuous_fixedEndpoints (m : ℕ) (e0 en : ℝ) :
    Continuous (fixedEndpoints m e0 en) := by
  have h : Continuous
      (fun y => fixedEndpoints m e0 en 0 + internalCoefficientInclusion m y) :=
    continuous_const.add (internalCoefficientInclusion m).continuous
  simpa only [← fixedEndpoints_eq_affine] using h

def fixedCoefficientJacobian (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ := coefficientJacobian (fixedEndpoints m e0 en x)

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_coefficientMap {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    HasFDerivAt (coefficientMap m e0 en)
      (matrixDerivative (fixedCoefficientJacobian m e0 en x)) x := by
  let e := fixedEndpoints m e0 en x
  have he : coefficientAdmissible e := fixedEndpoints_admissible h0 hn hx
  have hU := (isOpen_positiveCoefficientDomain (m + 1)).mem_nhds
    (admissible_mem_positiveCoefficientDomain he)
  let L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := ContinuousLinearMap.pi fun k =>
    (fderiv ℝ (fun z : Coefficients (m + 1) => coefficientTransform z (k.val + 1)) e).comp
      (internalCoefficientInclusion m)
  have hL : HasFDerivAt (coefficientMap m e0 en) L x := by
    apply hasFDerivAt_pi.mpr
    intro k
    have hf := ((contDiffOn_coefficientTransform (k := k.val + 1) (by omega) (by omega)).contDiffAt hU
      |>.differentiableAt (by simp)).hasFDerivAt
    exact hf.comp x (hasFDerivAt_fixedEndpoints m e0 en x)
  have heq : L = matrixDerivative (fixedCoefficientJacobian m e0 en x) := by
    apply ContinuousLinearMap.ext
    intro u
    have hu := pi_eq_sum_univ' u
    rw [hu]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
    funext k
    have hleft : L (Pi.single q 1) k = coefficientJacobian e k q := by
      change (fderiv ℝ (fun z : Coefficients (m + 1) =>
        coefficientTransform z (k.val + 1)) e)
          (internalCoefficientInclusion m (Pi.single q 1)) = _
      rw [internalCoefficientInclusion_single]
      exact fderiv_coefficientTransform_single he k q
    have hright : matrixDerivative (fixedCoefficientJacobian m e0 en x)
        (Pi.single q 1) k = coefficientJacobian e k q := by
      change ((show Matrix (Fin m) (Fin m) ℝ from coefficientJacobian e) *ᵥ
        (Pi.single q 1 : Fin m → ℝ)) k = _
      exact congrFun (Matrix.mulVec_single_one
        (show Matrix (Fin m) (Fin m) ℝ from coefficientJacobian e) q) k
    exact hleft.trans hright.symm
  simpa only [heq] using hL

theorem fixedCoefficientJacobian_diagonallyStable {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    DiagonallyStable (fixedCoefficientJacobian m e0 en x) := by
  have he := fixedEndpoints_admissible h0 hn hx
  refine ⟨jacobianRescaling (fixedEndpoints m e0 en x), jacobianRescaling_pos he, ?_⟩
  rw [fixedCoefficientJacobian, coefficientJacobian_eq_balancedJacobian he]
  exact symmetricPart_balancedJacobian_posDef (by omega) he

/-- The injectivity clause of Theorem 2.1 on the entire closed orthant.
The endpoints are fixed positive numbers; internal coefficients can vanish. -/
theorem coefficientMap_injOn_nonnegative {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Set.InjOn (coefficientMap m e0 en) {x : Fin m → ℝ | 0 ≤ x} := by
  intro x hx y hy hxy
  let b : Fin m → ℝ := fun i => max (x i) (y i)
  have hx' : x ∈ Icc 0 b := ⟨hx, fun i => le_max_left _ _⟩
  have hy' : y ∈ Icc 0 b := ⟨hy, fun i => le_max_right _ _⟩
  exact injOn_rectangle_of_diagonal_stability
    (fun z hz => hasFDerivAt_coefficientMap h0 hn hz.1)
    (fun z hz => fixedCoefficientJacobian_diagonallyStable h0 hn hz.1) hx' hy' hxy

theorem coefficientMap_principalJacobianPositive {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    principalJacobianPositive (fixedCoefficientJacobian m e0 en x) :=
  coefficientJacobian_principal_minors_pos (by omega) (fixedEndpoints_admissible h0 hn hx)

end EllipsoidVerification
end
end CanonicalSource1

section CanonicalSource2
/- Source: Ellipsoid/PrincipalReconstruction.lean -/



noncomputable section

open Polynomial Set
open scoped BigOperators

namespace EllipsoidVerification

theorem axisCoefficients_zero {n : ℕ} (a : Fin n → ℝ) : axisCoefficients a 0 = 1 := by
  simp [axisCoefficients, axisCoefficientPolynomial, Polynomial.coeff_zero_prod]

theorem axisCoefficients_last {n : ℕ} (a : Fin n → ℝ) :
    axisCoefficients a (Fin.last n) = (∏ i, a i) ^ 2 := by
  have h := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ)
    (fun i : Fin n => 1 + C (a i ^ 2) * X) 1 (fun i hi => by
      apply Polynomial.natDegree_add_le_of_degree_le (by simp)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  simp only [Finset.card_univ, Fintype.card_fin, mul_one, Polynomial.coeff_add,
    Polynomial.coeff_one, Polynomial.coeff_C_mul_X, one_ne_zero, if_false, if_true,
    zero_add] at h
  simpa only [axisCoefficients, axisCoefficientPolynomial, Fin.val_last, Finset.prod_pow] using h

def internalCoefficients (m : ℕ) (e : Coefficients (m + 1)) : Fin m → ℝ :=
  fun i => e ⟨i.val + 1, by omega⟩

theorem fixedEndpoints_internalCoefficients (m : ℕ) (e : Coefficients (m + 1)) :
    fixedEndpoints m (e 0) (e (Fin.last (m + 1))) (internalCoefficients m e) = e := by
  funext j
  unfold fixedEndpoints
  split_ifs with h0 hn
  · congr 1
    exact Fin.ext h0.symm
  · congr 1
    exact Fin.ext hn.symm
  · dsimp [internalCoefficients]
    exact congrArg e (Fin.ext (show j.val - 1 + 1 = j.val by omega))

theorem axisPolynomial_eq_of_axisCoefficients_eq {n : ℕ} {a b : Fin n → ℝ}
    (h : axisCoefficients a = axisCoefficients b) :
    axisCoefficientPolynomial a = axisCoefficientPolynomial b := by
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ n
  · exact congrFun h ⟨k, by omega⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((axisCoefficientPolynomial_natDegree_le a).trans_lt (lt_of_not_ge hk)),
      Polynomial.coeff_eq_zero_of_natDegree_lt
      ((axisCoefficientPolynomial_natDegree_le b).trans_lt (lt_of_not_ge hk))]

/-- The exact principal reconstruction theorem. The intrinsic volumes are
the coefficients of the actual parallel-body volumes, and the conclusion is
an actual Euclidean isometry between the ellipsoid bodies. -/
theorem intrinsic_reconstruction : IntrinsicReconstruction := by
  intro n E F hV
  cases n with
  | zero =>
      exact E.congruent_of_semiaxes_perm F (Equiv.refl _) (fun i => Fin.elim0 i)
  | succ m =>
      let e := axisCoefficients E.semiaxis
      let f := axisCoefficients F.semiaxis
      have he := axisCoefficients_admissible E.semiaxis E.semiaxis_pos
      have hf := axisCoefficients_admissible F.semiaxis F.semiaxis_pos
      have hprod : (∏ i, E.semiaxis i) = ∏ i, F.semiaxis i := by
        have h := hV (m + 1) (by omega) le_rfl
        rw [E.volume_top (by omega), F.volume_top (by omega)] at h
        exact mul_left_cancel₀ (unitBallVolume_pos (m + 1)).ne' h
      have hen : e (Fin.last (m + 1)) = f (Fin.last (m + 1)) := by
        simp only [e, f, axisCoefficients_last, hprod]
      have he0 : e 0 = 1 := axisCoefficients_zero _
      have hf0 : f 0 = 1 := axisCoefficients_zero _
      let x := internalCoefficients m e
      let y := internalCoefficients m f
      have hx : (0 : Fin m → ℝ) ≤ x := fun i => he.1 _
      have hy : (0 : Fin m → ℝ) ≤ y := fun i => hf.1 _
      have hxe : fixedEndpoints m 1 (e (Fin.last (m + 1))) x = e := by
        simpa only [he0] using fixedEndpoints_internalCoefficients m e
      have hyf : fixedEndpoints m 1 (e (Fin.last (m + 1))) y = f := by
        simpa only [hf0, hen] using fixedEndpoints_internalCoefficients m f
      have hxy : coefficientMap m 1 (e (Fin.last (m + 1))) x =
          coefficientMap m 1 (e (Fin.last (m + 1))) y := by
        funext k
        have h := hV (k.val + 1) (by omega) (by omega)
        rw [E.volume_eq_coefficientTransform (by omega) (by omega),
          F.volume_eq_coefficientTransform (by omega) (by omega)] at h
        simpa only [coefficientMap, hxe, hyf, e, f] using
          mul_left_cancel₀ (unitBallVolume_pos (k.val + 1)).ne' h
      have hcoordinates := coefficientMap_injOn_nonnegative (m := m) (by norm_num)
        he.2.2 hx hy hxy
      have hef : e = f := by
        rw [← hxe, ← hyf, hcoordinates]
      exact E.congruent_of_axisPolynomial_eq F (axisPolynomial_eq_of_axisCoefficients_eq hef)

end EllipsoidVerification
end
end CanonicalSource2
