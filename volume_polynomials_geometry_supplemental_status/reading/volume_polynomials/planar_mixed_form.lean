module

public import VolumePolynomials.MixedVolumeMultilinear
public import VolumePolynomials.HyperbolicForm
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option autoImplicit false

/-! # The actual planar mixed-area form

Mixed area is the normalized coefficient of the genuine volume polynomial.
Brunn--Minkowski proves its reverse Cauchy--Schwarz inequality. Every finite
family of convex bodies then gives a symmetric bilinear form on its real
coefficient space; positivity of coefficients is removed by an explicit shift.
No virtual-body existence or unproved Alexandrov--Fenchel assertion is used.
-/

noncomputable section
open Set MeasureTheory Module LinearMap
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarMixedForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedArea (A B : ConvexBody E) : ℝ := mixedVolume μ ![A, B]

theorem mixedArea_nonnegative (A B : ConvexBody E) : 0 ≤ mixedArea μ A B :=
  mixedVolume_nonnegative μ _

theorem mixedArea_symm (A B : ConvexBody E) : mixedArea μ A B = mixedArea μ B A := by
  first
  | have h := mixedVolume_reindex μ ![A, B] (Equiv.swap (0 : Fin 2) 1)
    have he : (fun i => ![A, B] (Equiv.swap (0 : Fin 2) 1 i)) = ![B, A] := by
      first
      | funext i
        fin_cases i <;> simp
    rw [he] at h
    exact h.symm

theorem mixedArea_add_left (A B C : ConvexBody E) :
    mixedArea μ (A + B) C = mixedArea μ A C + mixedArea μ B C := by
  first
  | simpa only [mixedArea, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_add μ ![A, C] 0 A B

theorem mixedArea_add_right (A B C : ConvexBody E) :
    mixedArea μ A (B + C) = mixedArea μ A B + mixedArea μ A C := by
  first
  | rw [mixedArea_symm μ A, mixedArea_add_left,
      mixedArea_symm μ B A, mixedArea_symm μ C A]

theorem mixedArea_smul_left (A B : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedArea μ (r • A) B = r * mixedArea μ A B := by
  first
  | simpa only [mixedArea, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_smul μ ![A, B] 0 A hr

theorem mixedArea_smul_right (A B : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedArea μ A (r • B) = r * mixedArea μ A B := by
  first
  | rw [mixedArea_symm, mixedArea_smul_left μ B A hr, mixedArea_symm μ B A]

@[simp] theorem mixedArea_zero_left (A : ConvexBody E) : mixedArea μ 0 A = 0 := by
  first
  | simpa only [mixedArea, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_zero_arg μ ![A, A] 0

@[simp] theorem mixedArea_zero_right (A : ConvexBody E) : mixedArea μ A 0 = 0 := by
  first
  | rw [mixedArea_symm, mixedArea_zero_left]

theorem mixedArea_translate (A B : ConvexBody E) (v w : E) :
    mixedArea μ (translateBody v A) (translateBody w B) = mixedArea μ A B := by
  first
  | have h := mixedVolume_translate μ ![A, B] ![v, w]
    have he : (fun i : Fin 2 => translateBody (![v, w] i) (![A, B] i)) =
        ![translateBody v A, translateBody w B] := by
      first
      | funext i
        fin_cases i <;> rfl
    simpa only [he, mixedArea] using h

theorem mixedArea_translate_right (A B : ConvexBody E) (v : E) :
    mixedArea μ A (translateBody v B) = mixedArea μ A B := by
  first
  | simpa only [translateBody_zero] using mixedArea_translate μ A B 0 v

@[simp] theorem mixedArea_point_left (v : E) (A : ConvexBody E) :
    mixedArea μ (pointBody v) A = 0 := by
  first
  | have h := mixedArea_translate μ (0 : ConvexBody E) A v 0
    rw [translateBody_zero] at h
    change mixedArea μ (pointBody v + 0) A = _ at h
    simpa only [add_zero, mixedArea_zero_left] using h

theorem mixedArea_diagonal (hdim : finrank ℝ E = 2) (A : ConvexBody E) :
    mixedArea μ A A = μ.real (A : Set E) := by
  first
  | have he : (![A, A] : Fin 2 → ConvexBody E) = fun _ => A := by
      first
      | funext i
        fin_cases i <;> rfl
    simpa only [mixedArea, he] using mixedVolume_diagonal μ hdim A

theorem area_add (hdim : finrank ℝ E = 2) (A B : ConvexBody E) :
    μ.real (A + B : ConvexBody E) =
      μ.real (A : Set E) + 2 * mixedArea μ A B + μ.real (B : Set E) := by
  first
  | rw [← mixedArea_diagonal μ hdim, mixedArea_add_left,
      mixedArea_add_right, mixedArea_add_right, mixedArea_symm μ B A,
      mixedArea_diagonal μ hdim, mixedArea_diagonal μ hdim]
    ring

/-- Brunn--Minkowski transported through an actual continuous linear coordinate
equivalence. It applies to every norm on the two-dimensional ambient space and
every specified additive Haar measure. -/
theorem sqrt_area_add (hdim : finrank ℝ E = 2) (A B : ConvexBody E) :
    Real.sqrt (μ.real (A : Set E)) + Real.sqrt (μ.real (B : Set E)) ≤
      Real.sqrt (μ.real (A + B : ConvexBody E)) := by
  first
  | letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) := inferInstanceAs (Measure.IsAddHaarMeasure μ)
    let T : E ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      ContinuousLinearEquiv.ofFinrankEq (hdim.trans finrank_euclideanSpace_fin.symm)
    let C := mapBody T.toContinuousLinearMap A
    let D := mapBody T.toContinuousLinearMap B
    let c : ℝ := LinearFrame.volumeFactor T
    have hc : 0 ≤ c := NNReal.coe_nonneg _
    have hscale (K : ConvexBody E) :
        μ.real (K : Set E) = c * volume.real
          (mapBody T.toContinuousLinearMap K : Set (EuclideanSpace ℝ (Fin 2))) := by
      first
      | rw [coe_mapBody, ContinuousLinearEquiv.coe_coe]
        exact LinearFrame.realVolume_eq_factor_mul_image T (K : Set E)
    have h := TauCeti.volume_real_rpow_add_volume_real_rpow_le
      (E := EuclideanSpace ℝ (Fin 2)) (by simp) C.nonempty
      C.isCompact.measurableSet.nullMeasurableSet D.nonempty
      D.isCompact.measurableSet.nullMeasurableSet (C + D).isCompact.measure_ne_top
    have hexp : (finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ)⁻¹ = 1 / 2 := by simp
    have h' : Real.sqrt (volume.real (C : Set (EuclideanSpace ℝ (Fin 2)))) +
        Real.sqrt (volume.real (D : Set (EuclideanSpace ℝ (Fin 2)))) ≤
        Real.sqrt (volume.real
          ((C + D : ConvexBody (EuclideanSpace ℝ (Fin 2))) :
            Set (EuclideanSpace ℝ (Fin 2)))) := by
      first
      | simpa only [hexp, ← Real.sqrt_eq_rpow, ConvexBody.coe_add] using h
    rw [hscale A, hscale B, hscale (A + B), mapBody_add]
    simp only [Real.sqrt_mul hc]
    simpa only [mul_add, C, D] using mul_le_mul_of_nonneg_left h' (Real.sqrt_nonneg c)

/-- The planar Minkowski inequality for literal Haar area and literal mixed area. -/
theorem sqrt_area_mul_le_mixedArea (hdim : finrank ℝ E = 2) (A B : ConvexBody E) :
    Real.sqrt (μ.real (A : Set E)) * Real.sqrt (μ.real (B : Set E)) ≤
      mixedArea μ A B := by
  first
  | have h := sqrt_area_add μ hdim A B
    have hs := mul_self_le_mul_self (by positivity :
        0 ≤ Real.sqrt (μ.real (A : Set E)) + Real.sqrt (μ.real (B : Set E))) h
    have hA := Real.sq_sqrt (show 0 ≤ μ.real (A : Set E) from measureReal_nonneg)
    have hB := Real.sq_sqrt (show 0 ≤ μ.real (B : Set E) from measureReal_nonneg)
    have hsum := Real.sq_sqrt (show 0 ≤ μ.real (A + B : ConvexBody E) from measureReal_nonneg)
    have harea := area_add μ hdim A B
    nlinarith

theorem minkowski_squared (hdim : finrank ℝ E = 2) (A B : ConvexBody E) :
    μ.real (A : Set E) * μ.real (B : Set E) ≤ mixedArea μ A B ^ 2 := by
  first
  | have h := sqrt_area_mul_le_mixedArea μ hdim A B
    have hs := mul_self_le_mul_self (by positivity :
      0 ≤ Real.sqrt (μ.real (A : Set E)) * Real.sqrt (μ.real (B : Set E))) h
    have he : (Real.sqrt (μ.real (A : Set E)) * Real.sqrt (μ.real (B : Set E))) ^ 2 =
        μ.real (A : Set E) * μ.real (B : Set E) := by
      first
      | rw [mul_pow, Real.sq_sqrt measureReal_nonneg, Real.sq_sqrt measureReal_nonneg]
    nlinarith

theorem mixedArea_sum_left {ι : Type*} (s : Finset ι)
    (K : ι → ConvexBody E) (B : ConvexBody E) :
    mixedArea μ (∑ i ∈ s, K i) B = ∑ i ∈ s, mixedArea μ (K i) B := by
  first
  | classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [Finset.sum_insert hi, mixedArea_add_left, ih,
        Finset.sum_insert hi]

theorem mixedArea_sum_right {ι : Type*} (s : Finset ι)
    (K : ι → ConvexBody E) (A : ConvexBody E) :
    mixedArea μ A (∑ i ∈ s, K i) = ∑ i ∈ s, mixedArea μ A (K i) := by
  first
  | rw [mixedArea_symm, mixedArea_sum_left]
    exact Finset.sum_congr rfl (fun i _ => mixedArea_symm μ (K i) A)

def form {ι : Type*} [Fintype ι] (K : ι → ConvexBody E) : LinearMap.BilinForm ℝ (ι → ℝ) :=
  Matrix.toBilin'Aux (fun i j => mixedArea μ (K i) (K j))

theorem form_apply {ι : Type*} [Fintype ι] (K : ι → ConvexBody E) (x y : ι → ℝ) :
    form μ K x y = ∑ i, ∑ j, x i * mixedArea μ (K i) (K j) * y j := by
  first
  | classical
    exact Matrix.toBilin'_apply _ _ _

@[simp] theorem form_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ConvexBody E) (i j : ι) :
    form μ K (Pi.single i 1) (Pi.single j 1) = mixedArea μ (K i) (K j) :=
  Matrix.toBilin'Aux_single _ _ _

set_option maxHeartbeats 800000 in
theorem form_one_positive_of_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ConvexBody E) (i j : ι) (hij : 0 < mixedArea μ (K i) (K j)) :
    0 < form μ K (fun _ : ι => (1 : ℝ)) (fun _ : ι => (1 : ℝ)) := by
  first
  | rw [form_apply]
    simp only [one_mul, mul_one]
    have hrow : mixedArea μ (K i) (K j) ≤ ∑ k, mixedArea μ (K i) (K k) :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun k : ι => mixedArea μ (K i) (K k))
        (fun k _ => mixedArea_nonnegative μ (K i) (K k)) (Finset.mem_univ j)
    have hsum : (∑ k, mixedArea μ (K i) (K k)) ≤
        ∑ l, ∑ k, mixedArea μ (K l) (K k) :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun l : ι => ∑ k, mixedArea μ (K l) (K k))
        (fun l _ => Finset.sum_nonneg (fun k _ =>
          mixedArea_nonnegative μ (K l) (K k))) (Finset.mem_univ i)
    exact hij.trans_le (hrow.trans hsum)

theorem form_symmetric {ι : Type*} [Fintype ι] (K : ι → ConvexBody E)
    (x y : ι → ℝ) : form μ K x y = form μ K y x := by
  first
  | simp only [form_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mixedArea_symm μ (K j) (K i)]
    ring

theorem form_eq_mixedArea {ι : Type*} [Fintype ι] (K : ι → ConvexBody E)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    form μ K x y = mixedArea μ (∑ i, x i • K i) (∑ i, y i • K i) := by
  first
  | rw [form_apply, mixedArea_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [mixedArea_smul_left μ _ _ (hx i), mixedArea_sum_right, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mixedArea_smul_right μ _ _ (hy j)]
    ring

theorem form_one_one {ι : Type*} [Fintype ι] (K : ι → ConvexBody E) :
    form μ K (fun _ => 1) (fun _ => 1) = mixedArea μ (∑ i, K i) (∑ i, K i) := by
  first
  | simpa only [one_smul] using
      form_eq_mixedArea μ K (fun _ => 1) (fun _ => 1) (fun _ => zero_le_one)
        (fun _ => zero_le_one)

/-- The one-positive-direction property in the complete real coefficient space.
All signed vectors are covered by shifting them into the nonnegative orthant. -/
theorem form_nonpositive_on_orthogonal {ι : Type*} [Fintype ι]
    (hdim : finrank ℝ E = 2) (K : ι → ConvexBody E)
    (hpositive : 0 < form μ K (fun _ => 1) (fun _ => 1))
    (x : ι → ℝ) (hx : form μ K x (fun _ => 1) = 0) :
    form μ K x x ≤ 0 := by
  first
  | classical
    let t : ℝ := ∑ i, |x i|
    let e : ι → ℝ := fun _ => 1
    let y : ι → ℝ := x + t • e
    have hy (i : ι) : 0 ≤ y i := by
      first
      | have hi : |x i| ≤ t := Finset.single_le_sum (fun j _ => abs_nonneg (x j))
          (Finset.mem_univ i)
        dsimp only [y, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
        linarith [neg_abs_le (x i)]
    have he : ∀ i, 0 ≤ e i := fun _ => zero_le_one
    have h := minkowski_squared μ hdim (∑ i, y i • K i) (∑ i, e i • K i)
    rw [← mixedArea_diagonal μ hdim, ← mixedArea_diagonal μ hdim,
      ← form_eq_mixedArea μ K y y hy hy, ← form_eq_mixedArea μ K e e he he,
      ← form_eq_mixedArea μ K y e hy he] at h
    have hex : form μ K e x = 0 := (form_symmetric μ K e x).trans hx
    have hxe : form μ K x e = 0 := hx
    simp only [y, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hxe, hex, mul_zero, zero_add, add_zero] at h
    have hprod : form μ K x x * form μ K e e ≤ 0 := by nlinarith
    by_contra hxx
    exact (not_lt_of_ge hprod) (mul_pos (lt_of_not_ge hxx) hpositive)

/-- The planar Alexandrov--Fenchel inequality for every real coefficient vector
and every vector with nonnegative quadratic value. -/
theorem form_reverse_cauchy_schwarz {ι : Type*} [Fintype ι]
    (hdim : finrank ℝ E = 2) (K : ι → ConvexBody E)
    (hpositive : 0 < form μ K (fun _ => 1) (fun _ => 1))
    (x y : ι → ℝ) (hy : 0 ≤ form μ K y y) :
    form μ K x x * form μ K y y ≤ form μ K x y ^ 2 :=
  bilinear_reverse_cauchy_schwarz (form μ K) (form_symmetric μ K) (fun _ => 1)
    (form_nonpositive_on_orthogonal μ hdim K hpositive) x y hy

end VolumePolynomials.PlanarMixedForm

namespace VolumePolynomials

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Ordinary Cauchy--Schwarz on the negative orthogonal hyperplane, including
null directions. -/
theorem bilinear_negative_cauchy_schwarz (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (e : V)
    (hneg : ∀ x, B x e = 0 → B x x ≤ 0)
    (x y : V) (hx : B x e = 0) (hy : B y e = 0) :
    B x y ^ 2 ≤ B x x * B y y := by
  first
  | have hyy := hneg y hy
    have hquad (r : ℝ) : B x x + 2 * r * B x y + r ^ 2 * B y y ≤ 0 := by
      first
      | have hz : B (x + r • y) e = 0 := by
          first
          | simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hx, hy, mul_zero, add_zero]
        have h := hneg (x + r • y) hz
        simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
          LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hB y x] at h
        nlinarith
    rcases hyy.eq_or_lt with hzero | hstrict
    · have hxy : B x y = 0 := by
        first
        | by_contra hne
          have h := hquad ((1 - B x x) / (2 * B x y))
          rw [hzero] at h
          have he : B x x + 2 * ((1 - B x x) / (2 * B x y)) * B x y = 1 := by
            first
            | field_simp [hne]
              ring
          nlinarith
      rw [hxy, hzero]
      simp
    · have h := hquad (-B x y / B y y)
      have he : B x x + 2 * (-B x y / B y y) * B x y +
          (-B x y / B y y) ^ 2 * B y y =
          (B x x * B y y - B x y ^ 2) / B y y := by
        first
        | field_simp [ne_of_lt hstrict]
          ring
      rw [he] at h
      have hn : 0 ≤ B x x * B y y - B x y ^ 2 := by
        first
        | by_contra hnum
          exact (not_lt_of_ge h) (div_pos_of_neg_of_neg (lt_of_not_ge hnum) hstrict)
      linarith

end VolumePolynomials
