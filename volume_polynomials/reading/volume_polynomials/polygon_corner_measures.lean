module

public import VolumePolynomials.CornerAreaIdentity
public import VolumePolynomials.SlopeAtomKernel
public import VolumePolynomials.FourthMoment

@[expose] public section
set_option autoImplicit false

/-! # Literal finite corner measures and their geometric second moment

The four measures are constructed from the actual facet representation. Axis
vectors have zero mass. Their admissibility follows from the actual projection
widths, and the spectral second moment is exactly twice the area deficit.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped ENNReal NNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

def signIndex (x : ℝ) : Fin 2 := if 0 ≤ x then 0 else 1

def atomSlope (e : Plane) : ℝ := Real.log (|e.2| / |e.1|)

def atomWeight (e : Plane) : ℝ≥0 :=
  NNReal.mk (Real.sqrt (|e.1| * |e.2|)) (Real.sqrt_nonneg _)

def slopeAtom (e : Plane) : Measure ℝ := atomWeight e • Measure.dirac (atomSlope e)

instance slopeAtom_finite (e : Plane) : IsFiniteMeasure (slopeAtom e) := by
  first
  | unfold slopeAtom
    infer_instance

def atomFeature (e : Plane) : Lp ℝ 2 (volume : Measure ℝ) :=
  (atomWeight e : ℝ) • cornerFeature (atomSlope e)

def cornerAtom (e : Plane) (i j : Fin 2) : Measure ℝ :=
  if signIndex e.1 = i ∧ signIndex e.2 = j then slopeAtom e else 0

instance cornerAtom_finite (e : Plane) (i j : Fin 2) : IsFiniteMeasure (cornerAtom e i j) := by
  first
  | unfold cornerAtom
    split_ifs <;> infer_instance

def cornerMatrix {ι : Type*} [Fintype ι] (e : ι → Plane) :
    Matrix (Fin 2) (Fin 2) (Measure ℝ) := fun i j => ∑ k, cornerAtom (e k) i j

instance cornerMatrix_finite {ι : Type*} [Fintype ι] (e : ι → Plane) (i j : Fin 2) :
    IsFiniteMeasure (cornerMatrix e i j) := by
  first
  | unfold cornerMatrix
    infer_instance

theorem integrable_slopeAtom (e : Plane) (f : ℝ → ℝ) : Integrable f (slopeAtom e) :=
  (integrable_dirac (f := f) (a := atomSlope e) enorm_lt_top).smul_measure_nnreal

theorem integrable_cornerAtom (e : Plane) (i j : Fin 2) (f : ℝ → ℝ) :
    Integrable f (cornerAtom e i j) := by
  first
  | unfold cornerAtom
    split_ifs
    · exact integrable_slopeAtom e f
    · exact integrable_zero_measure

theorem integrable_cornerMatrix {ι : Type*} [Fintype ι] (e : ι → Plane)
    (i j : Fin 2) (f : ℝ → ℝ) : Integrable f (cornerMatrix e i j) := by
  first
  | exact integrable_finsetSum_measure.mpr (fun k _ => integrable_cornerAtom (e k) i j f)

theorem integral_slopeAtom (e : Plane) (f : ℝ → ℝ) :
    (∫ x, f x ∂slopeAtom e) = (atomWeight e : ℝ) * f (atomSlope e) := by
  first
  | change (∫ x, f x ∂(atomWeight e • Measure.dirac (atomSlope e))) = _
    rw [integral_smul_nnreal_measure, integral_dirac]
    rfl

theorem slopeAtom_exponential_moments (e : Plane) :
    (∫ x, Real.exp ((-1 / 2 : ℝ) * x) ∂slopeAtom e) ≤ |e.1| ∧
      (∫ x, Real.exp ((1 / 2 : ℝ) * x) ∂slopeAtom e) ≤ |e.2| := by
  first
  | rw [integral_slopeAtom, integral_slopeAtom]
    change Real.sqrt (|e.1| * |e.2|) * Real.exp ((-1 / 2 : ℝ) * Real.log (|e.2| / |e.1|)) ≤ |e.1| ∧
      Real.sqrt (|e.1| * |e.2|) * Real.exp ((1 / 2 : ℝ) * Real.log (|e.2| / |e.1|)) ≤ |e.2|
    by_cases hx : e.1 = 0
    · simp [hx, abs_nonneg e.2]
    by_cases hy : e.2 = 0
    · simp [hy, abs_nonneg e.1]
    have h := HalfZonotope.atom_exponential_moments (abs_pos.mpr hx) (abs_pos.mpr hy)
    constructor
    · convert h.1.le using 1 <;> congr 2 <;> ring
    · convert h.2.le using 1 <;> congr 2 <;> ring

theorem integral_cornerMatrix_row {ι : Type*} [Fintype ι] (e : ι → Plane)
    (i : Fin 2) (f : ℝ → ℝ) :
    (∑ j, ∫ x, f x ∂cornerMatrix e i j) =
      ∑ k, if signIndex (e k).1 = i then ∫ x, f x ∂slopeAtom (e k) else 0 := by
  first
  | simp only [cornerMatrix, integral_finsetSum_measure
      (fun k _ => integrable_cornerAtom (e k) i _ f)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hi : signIndex (e k).1 = i
    · simp only [cornerAtom, hi, true_and, ite_true]
      by_cases hs : 0 ≤ (e k).2 <;> simp [signIndex, hs]
    · simp [cornerAtom, hi]

theorem integral_cornerMatrix_col {ι : Type*} [Fintype ι] (e : ι → Plane)
    (j : Fin 2) (f : ℝ → ℝ) :
    (∑ i, ∫ x, f x ∂cornerMatrix e i j) =
      ∑ k, if signIndex (e k).2 = j then ∫ x, f x ∂slopeAtom (e k) else 0 := by
  first
  | simp only [cornerMatrix, integral_finsetSum_measure
      (fun k _ => integrable_cornerAtom (e k) _ j f)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hj : signIndex (e k).2 = j
    · simp only [cornerAtom, hj, and_true, ite_true]
      by_cases hs : 0 ≤ (e k).1 <;> simp [signIndex, hs]
    · simp [cornerAtom, hj]

theorem sign_part_bound (x a : ℝ) (r : Fin 2) (ha : a ≤ |x|) :
    (if signIndex x = r then a else 0) ≤
      if r = 0 then max x 0 else max (-x) 0 := by
  first
  | fin_cases r
    · by_cases hx : 0 ≤ x
      · simpa [signIndex, hx, abs_of_nonneg hx, max_eq_left hx] using ha
      · simp [signIndex, hx, max_eq_right (le_of_not_ge hx)]
    · by_cases hx : 0 ≤ x
      · simp [signIndex, hx, max_eq_right (neg_nonpos.mpr hx)]
      · simpa [signIndex, hx, abs_of_nonpos (le_of_not_ge hx),
          max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))] using ha

theorem Represents.row_moment_le_width {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (i : Fin 2) :
    (∑ j, ∫ x, Real.exp ((-1 / 2 : ℝ) * x) ∂cornerMatrix e i j) ≤ width P := by
  first
  | rw [integral_cornerMatrix_row]
    calc
      _ ≤ ∑ k, if i = 0 then max (e k).1 0 else max (-(e k).1) 0 :=
        Finset.sum_le_sum (fun k _ => sign_part_bound _ _ i (slopeAtom_exponential_moments (e k)).1)
      _ = width P := by
        first
        | fin_cases i
          · simpa using h.signed_variation.1
          · simpa using h.signed_variation.2.2.1

theorem Represents.col_moment_le_height {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (j : Fin 2) :
    (∑ i, ∫ x, Real.exp ((1 / 2 : ℝ) * x) ∂cornerMatrix e i j) ≤ height P := by
  first
  | rw [integral_cornerMatrix_col]
    calc
      _ ≤ ∑ k, if j = 0 then max (e k).2 0 else max (-(e k).2) 0 :=
        Finset.sum_le_sum (fun k _ => sign_part_bound _ _ j (slopeAtom_exponential_moments (e k)).2)
      _ = height P := by
        first
        | fin_cases j
          · simpa using h.signed_variation.2.1
          · simpa using h.signed_variation.2.2.2

theorem cornerMatrix_moment_eq_ofReal_integral {ι : Type*} [Fintype ι]
    (e : ι → Plane) (i j : Fin 2) (a : ℝ) :
    slopeExponentialMoment (cornerMatrix e i j) a =
      ENNReal.ofReal (∫ x, Real.exp (a * x) ∂cornerMatrix e i j) := by
  first
  | exact (ofReal_integral_eq_lintegral_ofReal (integrable_cornerMatrix e i j _)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm

/-- Admissibility is proved for the genuine nonnegative exponential integrals. -/
theorem Represents.admissible {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e)
    (hw : width P = 1) (hh : height P = 1) : IsAdmissibleSlopeMatrix (cornerMatrix e) := by
  first
  | constructor
    · intro i
      simp_rw [cornerMatrix_moment_eq_ofReal_integral]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg
        (fun x => (Real.exp_pos ((-1 / 2 : ℝ) * x)).le))]
      have hm := h.row_moment_le_width i
      rw [hw] at hm
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hm
    · intro j
      simp_rw [cornerMatrix_moment_eq_ofReal_integral]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg
        (fun x => (Real.exp_pos ((1 / 2 : ℝ) * x)).le))]
      have hm := h.col_moment_le_height j
      rw [hh] at hm
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hm

@[simp] theorem cornerMean_slopeAtom (e : Plane) : cornerMean (slopeAtom e) = atomFeature e := by
  first
  | simp only [cornerMean, slopeAtom, integral_smul_nnreal_measure, integral_dirac,
      NNReal.smul_def, atomFeature]

theorem inner_atomFeature (e f : Plane) :
    ⟪atomFeature e, atomFeature f⟫_ℝ = min (|e.1| * |f.2|) (|f.1| * |e.2|) := by
  first
  | simp only [atomFeature, real_inner_smul_left, real_inner_smul_right,
      inner_cornerFeature, atomWeight, NNReal.coe_mk, atomSlope]
    rw [← mul_assoc]
    change Real.sqrt (|f.1| * |f.2|) * Real.sqrt (|e.1| * |e.2|) *
      cornerKernel (Real.log (|e.2| / |e.1|)) (Real.log (|f.2| / |f.1|)) = _
    rw [mul_comm (Real.sqrt (|f.1| * |f.2|)) (Real.sqrt (|e.1| * |e.2|))]
    exact HalfZonotope.weighted_cornerKernel (abs_nonneg e.1) (abs_nonneg e.2)
      (abs_nonneg f.1) (abs_nonneg f.2)

theorem cornerMean_cornerAtom (e : Plane) (i j : Fin 2) :
    cornerMean (cornerAtom e i j) =
      if signIndex e.1 = i ∧ signIndex e.2 = j then atomFeature e else 0 := by
  first
  | unfold cornerAtom
    split_ifs
    · exact cornerMean_slopeAtom e
    · simp [cornerMean]

theorem cornerMean_cornerMatrix {ι : Type*} [Fintype ι] (e : ι → Plane) (i j : Fin 2) :
    cornerMean (cornerMatrix e i j) = ∑ k, cornerMean (cornerAtom (e k) i j) := by
  first
  | exact integral_finsetSum_measure (fun k _ => integrable_cornerFeature (cornerAtom (e k) i j))

theorem signIndex_eq_iff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    signIndex a = signIndex b ↔ 0 < a * b := by
  first
  | rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
    · simp [signIndex, not_le_of_gt ha, not_le_of_gt hb, mul_pos_of_neg_of_neg ha hb]
    · simp [signIndex, not_le_of_gt ha, hb.le, not_lt_of_ge
        (mul_nonpos_of_nonpos_of_nonneg ha.le hb.le)]
    · simp [signIndex, ha.le, not_le_of_gt hb, not_lt_of_ge
        (mul_nonpos_of_nonneg_of_nonpos ha.le hb.le)]
    · simp [signIndex, ha.le, hb.le, mul_pos ha hb]

theorem cornerAtom_inner_sum (e f : Plane) :
    (∑ i, ∑ j, ⟪cornerMean (cornerAtom e i j), cornerMean (cornerAtom f i j)⟫_ℝ) =
      if signIndex e.1 = signIndex f.1 ∧ signIndex e.2 = signIndex f.2
        then ⟪atomFeature e, atomFeature f⟫_ℝ else 0 := by
  first
  | have h (i j : Fin 2) :
        ⟪cornerMean (cornerAtom e i j), cornerMean (cornerAtom f i j)⟫_ℝ =
          if signIndex e.1 = i then if signIndex e.2 = j then
            (if signIndex e.1 = signIndex f.1 ∧ signIndex e.2 = signIndex f.2
              then ⟪atomFeature e, atomFeature f⟫_ℝ else 0) else 0 else 0 := by
      first
      | rw [cornerMean_cornerAtom, cornerMean_cornerAtom]
        by_cases hi : signIndex e.1 = i <;> by_cases hj : signIndex e.2 = j
        · subst i
          subst j
          by_cases hf : signIndex e.1 = signIndex f.1 ∧ signIndex e.2 = signIndex f.2
          · simp [hf.1, hf.2]
          · have hf' : ¬(signIndex f.1 = signIndex e.1 ∧ signIndex f.2 = signIndex e.2) :=
              fun h => hf ⟨h.1.symm, h.2.symm⟩
            simp [hf, hf']
        · simp [hi, hj]
        · simp [hi, hj]
        · simp [hi, hj]
    simp_rw [h]
    simp

theorem pairKernel_eq_cornerAtom_inner (e f : Plane) :
    pairKernel e f = ∑ i, ∑ j,
      ⟪cornerMean (cornerAtom e i j), cornerMean (cornerAtom f i j)⟫_ℝ := by
  first
  | rw [cornerAtom_inner_sum, inner_atomFeature, pairKernel_eq_min]
    by_cases he1 : e.1 = 0
    · simp [he1, mul_nonneg (abs_nonneg f.1) (abs_nonneg e.2)]
    by_cases he2 : e.2 = 0
    · simp [he2, mul_nonneg (abs_nonneg e.1) (abs_nonneg f.2)]
    by_cases hf1 : f.1 = 0
    · simp [hf1, mul_nonneg (abs_nonneg e.1) (abs_nonneg f.2)]
    by_cases hf2 : f.2 = 0
    · simp [hf2, mul_nonneg (abs_nonneg f.1) (abs_nonneg e.2)]
    simp only [signIndex_eq_iff he1 hf1, signIndex_eq_iff he2 hf2]
    congr 1
    rw [mul_comm |e.2| |f.1|]

theorem cornerPairing_eq_matrix_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) :
    cornerPairing e f = ∑ i, ∑ j,
      ⟪cornerMean (cornerMatrix e i j), cornerMean (cornerMatrix f i j)⟫_ℝ := by
  first
  | simp_rw [cornerMean_cornerMatrix, sum_inner, inner_sum]
    simp_rw [cornerPairing, pairKernel_eq_cornerAtom_inner]
    let g (a : ι) (b : κ) (i j : Fin 2) :=
      ⟪cornerMean (cornerAtom (e a) i j), cornerMean (cornerAtom (f b) i j)⟫_ℝ
    change (∑ a, ∑ b, ∑ i, ∑ j, g a b i j) = ∑ i, ∑ j, ∑ a, ∑ b, g a b i j
    calc
      _ = ∑ a, ∑ i, ∑ b, ∑ j, g a b i j :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ i, ∑ a, ∑ b, ∑ j, g a b i j := Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ b, g a b i j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
      _ = ∑ i, ∑ j, ∑ a, ∑ b, g a b i j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

/-- Formula (4.7) for the actual polygon and the actual Cauchy spectral measure. -/
theorem Represents.second_moment {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) :
    slopeSecondMoment (cornerMatrix e) =
      2 * (width P * height P - volume.real (P : Set Plane)) := by
  first
  | have ha := h.area_identity
    rw [cornerPairing_eq_matrix_inner] at ha
    simp only [real_inner_self_eq_norm_sq] at ha
    rw [slopeSecondMoment_eq_entry_energies]
    linarith

theorem Represents.unit_second_moment {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e)
    (hw : width P = 1) (hh : height P = 1) :
    slopeSecondMoment (cornerMatrix e) = 2 * (1 - volume.real (P : Set Plane)) := by
  first
  | rw [h.second_moment, hw, hh, one_mul]

end VolumePolynomials.PlanarEdges
