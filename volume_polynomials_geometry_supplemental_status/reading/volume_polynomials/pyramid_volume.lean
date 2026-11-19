module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import VolumePolynomials.ExtrusionTransport
public import VolumePolynomials.LinearFrame

@[expose] public section
set_option autoImplicit false

/-!
# Pyramid volume from scaled product fibers

The pyramid is the actual image of a compact base and a closed parameter
interval. Tonelli's theorem and Haar scaling give its volume, including bases
of lower dimension. There is no simplex decomposition or polytope volume axiom.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal

namespace VolumePolynomials.PyramidVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial segments from the origin to a set. -/
def radialHull (A : Set E) : Set E :=
  (fun p : ℝ × E => p.1 • p.2) '' (Icc (0 : ℝ) 1 ×ˢ A)

theorem radialHull_compact {A : Set E} (hA : IsCompact A) : IsCompact (radialHull A) :=
  (isCompact_Icc.prod hA).image (by fun_prop)

theorem image_radialHull {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) (A : Set E) :
    L '' radialHull A = radialHull (L '' A) := by
  first
  | ext y
    constructor
    · rintro ⟨z, ⟨⟨r, x⟩, ⟨hr, hx⟩, rfl⟩, rfl⟩
      exact ⟨(r, L x), ⟨hr, ⟨x, hx, rfl⟩⟩, (map_smul L r x).symm⟩
    · rintro ⟨⟨r, z⟩, ⟨hr, ⟨x, hx, rfl⟩⟩, rfl⟩
      exact ⟨r • x, ⟨(r, x), ⟨hr, hx⟩, rfl⟩, map_smul L r x⟩

/-- Unit-height pyramid with its base in the first-coordinate-one hyperplane. -/
def unitPyramid (A : Set E) : Set (ℝ × E) :=
  (fun p : ℝ × E => (p.1, p.1 • p.2)) '' (Icc (0 : ℝ) 1 ×ˢ A)

theorem unitPyramid_compact {A : Set E} (hA : IsCompact A) :
    IsCompact (unitPyramid A) :=
  (isCompact_Icc.prod hA).image (by fun_prop)

theorem unitPyramid_fiber (A : Set E) (s : ℝ) :
    Prod.mk s ⁻¹' unitPyramid A = if s ∈ Icc (0 : ℝ) 1 then s • A else ∅ := by
  first
  | classical
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [if_pos hs]
      ext y
      constructor
      · rintro ⟨⟨r, x⟩, ⟨hr, hx⟩, heq⟩
        have hrs : r = s := congrArg Prod.fst heq
        subst r
        exact ⟨x, hx, congrArg Prod.snd heq⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(s, x), ⟨hs, hx⟩, rfl⟩
    · rw [if_neg hs]
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨⟨r, x⟩, ⟨hr, hx⟩, heq⟩
      have hrs : r = s := congrArg Prod.fst heq
      exact hs (hrs ▸ hr)

/-- The sole scalar integral in the pyramid formula. -/
theorem lintegral_unit_pow (d : ℕ) :
    (∫⁻ s : ℝ in Icc 0 1, ENNReal.ofReal (s ^ d)) =
      ENNReal.ofReal (((d + 1 : ℕ) : ℝ)⁻¹) := by
  first
  | have hi : IntegrableOn (fun s : ℝ => s ^ d) (Icc (0 : ℝ) 1) :=
      (continuous_id.pow d).integrableOn_Icc
    have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] (fun s : ℝ => s ^ d) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact pow_nonneg hs.1 d
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    simp

section Measure

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

theorem unitPyramid_fiber_measure (A : Set E) (s : ℝ) :
    volume (Prod.mk s ⁻¹' unitPyramid A) =
      (Icc (0 : ℝ) 1).indicator
        (fun r => ENNReal.ofReal (r ^ finrank ℝ E) * volume A) s := by
  first
  | classical
    rw [unitPyramid_fiber]
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [if_pos hs, Set.indicator_of_mem hs,
        Measure.addHaar_smul_of_nonneg volume hs.1]
    · simp only [if_neg hs, measure_empty, Set.indicator_of_notMem hs]

/-- Actual product volume of a unit-height pyramid over any compact base. -/
theorem volume_unitPyramid {A : Set E} (hA : IsCompact A) :
    volume (unitPyramid A) =
      ENNReal.ofReal (((finrank ℝ E + 1 : ℕ) : ℝ)⁻¹) * volume A := by
  first
  | calc
      volume (unitPyramid A) = ∫⁻ s : ℝ, volume (Prod.mk s ⁻¹' unitPyramid A) :=
        Measure.prod_apply (unitPyramid_compact hA).measurableSet
      _ = ∫⁻ s : ℝ, (Icc (0 : ℝ) 1).indicator
          (fun r => ENNReal.ofReal (r ^ finrank ℝ E) * volume A) s :=
        lintegral_congr (unitPyramid_fiber_measure A)
      _ = ∫⁻ s : ℝ in Icc 0 1, ENNReal.ofReal (s ^ finrank ℝ E) * volume A :=
        lintegral_indicator measurableSet_Icc _
      _ = (∫⁻ s : ℝ in Icc 0 1, ENNReal.ofReal (s ^ finrank ℝ E)) * volume A :=
        lintegral_mul_const _ (by fun_prop)
      _ = ENNReal.ofReal (((finrank ℝ E + 1 : ℕ) : ℝ)⁻¹) * volume A := by
        rw [lintegral_unit_pow]

theorem realVolume_unitPyramid {A : Set E} (hA : IsCompact A) :
    volume.real (unitPyramid A) =
      (((finrank ℝ E + 1 : ℕ) : ℝ)⁻¹) * volume.real A := by
  first
  | simp only [measureReal_def, volume_unitPyramid hA, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg _))]

/-- Scaling only the first coordinate, with no change to the base coordinates. -/
def axisMap (h : ℝ) : (ℝ × E) →ₗ[ℝ] ℝ × E :=
  (h • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).prodMap (LinearMap.id : E →ₗ[ℝ] E)

@[simp] theorem axisMap_apply (h : ℝ) (p : ℝ × E) :
    axisMap h p = (h * p.1, p.2) := rfl

theorem axisMap_det (h : ℝ) : LinearMap.det (axisMap (E := E) h) = h := by
  first
  | simp [axisMap, LinearMap.det_prodMap]

def pyramid (h : ℝ) (A : Set E) : Set (ℝ × E) := axisMap h '' unitPyramid A

theorem pyramid_eq_parametric (h : ℝ) (A : Set E) :
    pyramid h A =
      (fun p : ℝ × E => (h * p.1, p.1 • p.2)) '' (Icc (0 : ℝ) 1 ×ˢ A) := by
  first
  | rw [pyramid, unitPyramid, Set.image_image]
    rfl

theorem radialHull_singleton_prod (h : ℝ) (A : Set E) :
    radialHull ({h} ×ˢ A) = pyramid h A := by
  first
  | rw [pyramid_eq_parametric]
    ext y
    constructor
    · rintro ⟨⟨r, ⟨s, x⟩⟩, ⟨hr, hs, hx⟩, rfl⟩
      change s = h at hs
      subst s
      exact ⟨(r, x), ⟨hr, hx⟩, Prod.ext (mul_comm h r) rfl⟩
    · rintro ⟨⟨r, x⟩, ⟨hr, hx⟩, rfl⟩
      exact ⟨(r, (h, x)), ⟨hr, rfl, hx⟩, Prod.ext (mul_comm r h) rfl⟩

theorem pyramid_compact {A : Set E} (hA : IsCompact A) (h : ℝ) :
    IsCompact (pyramid h A) :=
  (unitPyramid_compact hA).image (axisMap (E := E) h).continuous_of_finiteDimensional

/-- The height may be positive, negative, or zero. -/
theorem realVolume_pyramid {A : Set E} (hA : IsCompact A) (h : ℝ) :
    volume.real (pyramid h A) =
      (|h| / ((finrank ℝ E + 1 : ℕ) : ℝ)) * volume.real A := by
  first
  | change (volume (axisMap (E := E) h '' unitPyramid A)).toReal = _
    rw [Measure.addHaar_image_linearMap volume (axisMap (E := E) h), axisMap_det,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg h)]
    change |h| * volume.real (unitPyramid A) = _
    rw [realVolume_unitPyramid hA]
    ring

theorem realVolume_pyramid_nonneg {A : Set E} (hA : IsCompact A) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (pyramid h A) =
      (h / ((finrank ℝ E + 1 : ℕ) : ℝ)) * volume.real A := by
  first
  | simpa only [abs_of_nonneg hh] using realVolume_pyramid hA h

/-- A pyramid over an arbitrary compact subset of a coordinate hyperplane,
transported through an actual volume-preserving linear frame. -/
theorem realVolume_radialHull_of_frame
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasureSpace F] [BorelSpace F]
    (T : F ≃L[ℝ] ℝ × E) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) {h : ℝ}
    (hplane : ∀ x ∈ C, (T x).1 = h) :
    volume.real (radialHull C) =
      (|h| / ((finrank ℝ E + 1 : ℕ) : ℝ)) * volume.real (Prod.snd '' (T '' C)) := by
  first
  | have himage : T '' C = {h} ×ˢ (Prod.snd '' (T '' C)) := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hplane x hx, ⟨T x, ⟨x, hx, rfl⟩, rfl⟩⟩
      · rintro ⟨hp, ⟨q, ⟨x, hx, rfl⟩, hq⟩⟩
        change p.1 = h at hp
        refine ⟨x, hx, Prod.ext ?_ hq⟩
        exact (hplane x hx).trans hp.symm
    calc
      volume.real (radialHull C) = volume.real (T '' radialHull C) :=
        (ProductExtrusion.realVolume_image_of_measurePreserving T hT _).symm
      _ = volume.real (radialHull (T '' C)) := by
        exact congrArg volume.real (image_radialHull T.toLinearMap C)
      _ = volume.real (pyramid h (Prod.snd '' (T '' C))) := by
        exact congrArg volume.real ((congrArg radialHull himage).trans
          (radialHull_singleton_prod h (Prod.snd '' (T '' C))))
      _ = _ := realVolume_pyramid ((hC.image T.continuous).image continuous_snd) h

/-- The same formula for an arbitrary continuous linear frame. Its fixed
positive Haar scalar is explicit, so no measure-preservation hypothesis is
needed. -/
theorem realVolume_radialHull_of_equiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
    [IsAddHaarMeasure (volume : Measure F)]
    (T : F ≃L[ℝ] ℝ × E) {C : Set F} (hC : IsCompact C) {h : ℝ}
    (hplane : ∀ x ∈ C, (T x).1 = h) :
    volume.real (radialHull C) =
      ((LinearFrame.volumeFactor T : ℝ) * |h| / ((finrank ℝ E + 1 : ℕ) : ℝ)) *
        volume.real (Prod.snd '' (T '' C)) := by
  first
  | have himage : T '' C = {h} ×ˢ (Prod.snd '' (T '' C)) := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hplane x hx, ⟨T x, ⟨x, hx, rfl⟩, rfl⟩⟩
      · rintro ⟨hp, ⟨q, ⟨x, hx, rfl⟩, hq⟩⟩
        change p.1 = h at hp
        refine ⟨x, hx, Prod.ext ?_ hq⟩
        exact (hplane x hx).trans hp.symm
    rw [LinearFrame.realVolume_eq_factor_mul_image T]
    have himageRadial : T '' radialHull C = radialHull (T '' C) :=
      image_radialHull T.toLinearMap C
    rw [himageRadial]
    have hrad := (congrArg radialHull himage).trans
      (radialHull_singleton_prod h (Prod.snd '' (T '' C)))
    rw [hrad, realVolume_pyramid ((hC.image T.continuous).image continuous_snd) h]
    ring

theorem frame_pyramid_constant_pos
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
    [IsAddHaarMeasure (volume : Measure F)] (T : F ≃L[ℝ] ℝ × E) :
    0 < (LinearFrame.volumeFactor T : ℝ) / ((finrank ℝ E + 1 : ℕ) : ℝ) := by
  first
  | apply div_pos
    · exact_mod_cast LinearFrame.volumeFactor_pos T
    · positivity

end Measure
end VolumePolynomials.PyramidVolume
