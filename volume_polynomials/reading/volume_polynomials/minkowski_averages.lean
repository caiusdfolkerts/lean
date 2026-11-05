module

public import VolumePolynomials.MinkowskiFunctional
public import VolumePolynomials.SharpBerwald
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Minkowski averages of actual convex fibers

Finite-dimensional averaging is applied to finitely many support or other
monotone Minkowski functionals at a time. Blaschke compactness and the finite
intersection property then produce one actual body satisfying every average
identity simultaneously. This avoids assuming a representation theorem for
abstract support functions or continuity of fibers at the boundary.
-/

open Set Metric MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.MinkowskiAverages

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rootVolume (K : ConvexBody E) : ℝ :=
  volume.real (K : Set E) ^ ((finrank ℝ E : ℝ)⁻¹)

theorem rootVolume_nonnegative (K : ConvexBody E) : 0 ≤ rootVolume K :=
  Real.rpow_nonneg measureReal_nonneg _

theorem continuous_rootVolume : Continuous (rootVolume (E := E)) :=
  (continuous_convexBody_realMeasure volume).rpow_const
    (fun _ => Or.inr (inv_nonneg.mpr (Nat.cast_nonneg _)))

theorem rootVolume_mono {K L : ConvexBody E} (h : (K : Set E) ⊆ L) :
    rootVolume K ≤ rootVolume L :=
  Real.rpow_le_rpow measureReal_nonneg (measureReal_mono h L.isCompact.measure_ne_top)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem rootVolume_minkowski_concave (hdim : finrank ℝ E ≠ 0)
    (K L : ConvexBody E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * rootVolume K + b * rootVolume L ≤ rootVolume (a • K + b • L) := by
  first
  | exact TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le hdim
      K.nonempty K.isCompact.measurableSet.nullMeasurableSet
      L.nonempty L.isCompact.measurableSet.nullMeasurableSet ha hb
      (a • K + b • L).isCompact.measure_ne_top

def boundedBodies (R : ℝ) : Set (ConvexBody E) :=
  {K | (K : Set E) ⊆ closedBall 0 R}

theorem boundedBodies_compact (R : ℝ) : IsCompact (boundedBodies (E := E) R) :=
  isCompact_bodies_subset_compact (isCompact_closedBall 0 R)

theorem boundedBodies_combination {R : ℝ} {K L : ConvexBody E}
    (hK : K ∈ boundedBodies R) (hL : L ∈ boundedBodies R)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • K + b • L ∈ boundedBodies R := by
  first
  | rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact convex_closedBall (0 : E) R (hK hx) (hL hy) ha hb hab

def bodyHypograph (R : ℝ) : Set (ConvexBody E × ℝ) :=
  {p | p.1 ∈ boundedBodies R ∧ 0 ≤ p.2 ∧ p.2 ≤ rootVolume p.1}

theorem bodyHypograph_compact (R : ℝ) : IsCompact (bodyHypograph (E := E) R) := by
  first
  | obtain ⟨B, hB⟩ := ((boundedBodies_compact (E := E) R).image continuous_rootVolume).bddAbove
    have heq : bodyHypograph (E := E) R =
        (boundedBodies R ×ˢ Icc 0 B) ∩ {p : ConvexBody E × ℝ | p.2 ≤ rootVolume p.1} := by
      first
      | ext p
        constructor
        · rintro ⟨hp, hz0, hzK⟩
          exact ⟨⟨hp, hz0, hzK.trans (hB ⟨p.1, hp, rfl⟩)⟩, hzK⟩
        · rintro ⟨⟨hp, hz0, _⟩, hzK⟩
          exact ⟨hp, hz0, hzK⟩
    rw [heq]
    exact ((boundedBodies_compact R).prod isCompact_Icc).inter_right
      (isClosed_le continuous_snd (continuous_rootVolume.comp continuous_fst))

def finiteObservation {ι : Type*} (F : ι → MinkowskiFunctional E)
    (p : ConvexBody E × ℝ) : (ι → ℝ) × ℝ := (fun i => F i p.1, p.2)

theorem continuous_finiteObservation {ι : Type*} (F : ι → MinkowskiFunctional E) :
    Continuous (finiteObservation F) :=
  (continuous_pi (fun i => (F i).continuous_toFun.comp continuous_fst)).prodMk continuous_snd

theorem finiteObservation_image_convex {ι : Type*} (hdim : finrank ℝ E ≠ 0)
    (F : ι → MinkowskiFunctional E) (R : ℝ) :
    Convex ℝ (finiteObservation F '' bodyHypograph R) := by
  first
  | rintro _ ⟨⟨K, x⟩, ⟨hK, hx0, hxK⟩, rfl⟩
      _ ⟨⟨L, y⟩, ⟨hL, hy0, hyL⟩, rfl⟩ a b ha hb hab
    refine ⟨(a • K + b • L, a * x + b * y), ?_, ?_⟩
    · refine ⟨boundedBodies_combination hK hL ha hb hab,
        add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0), ?_⟩
      exact (add_le_add (mul_le_mul_of_nonneg_left hxK ha)
        (mul_le_mul_of_nonneg_left hyL hb)).trans
        (rootVolume_minkowski_concave hdim K L ha hb)
    · ext i
      · exact (F i).map_convex_combination K L ha hb
      · rfl

section Fibers

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  {Z : Set U} {K : U → ConvexBody E}

theorem rootVolume_fiber_concave (hdim : finrank ℝ E ≠ 0)
    (hK : FiberConcave Z K) : ConcaveOn ℝ Z (fun y => rootVolume (K y)) := by
  first
  | refine ⟨hK.1, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (rootVolume_minkowski_concave hdim (K x) (K y) ha hb).trans
      (rootVolume_mono (hK.2 x hx y hy a b ha hb hab))

theorem functional_fiber_integrable (hZ : IsCompact Z) (hK : FiberConcave Z K)
    {R : ℝ} (hR : ∀ y ∈ Z, K y ∈ boundedBodies R) (φ : MinkowskiFunctional E) :
    IntegrableOn (fun y => φ (K y)) Z := by
  first
  | obtain ⟨B, hB⟩ := ((boundedBodies_compact (E := E) R).image
      φ.continuous_toFun).isBounded.exists_norm_le
    exact BerwaldMoments.bounded_concave_integrable_signed hZ
      (hK.functional_concave φ) (fun y hy => hB _ ⟨K y, hR y hy, rfl⟩)

theorem rootVolume_fiber_integrable (hdim : finrank ℝ E ≠ 0)
    (hZ : IsCompact Z) (hK : FiberConcave Z K)
    {R : ℝ} (hR : ∀ y ∈ Z, K y ∈ boundedBodies R) :
    IntegrableOn (fun y => rootVolume (K y)) Z := by
  first
  | obtain ⟨B, hB⟩ := ((boundedBodies_compact (E := E) R).image
      continuous_rootVolume).isBounded.exists_norm_le
    exact BerwaldMoments.bounded_concave_integrable_signed hZ
      (rootVolume_fiber_concave hdim hK) (fun y hy => hB _ ⟨K y, hR y hy, rfl⟩)

theorem finite_average_body {ι : Type*} [Fintype ι]
    (hdim : finrank ℝ E ≠ 0) (hZ : IsCompact Z) (hvol : 0 < volume.real Z)
    (hK : FiberConcave Z K) {R : ℝ} (hR : ∀ y ∈ Z, K y ∈ boundedBodies R)
    (F : ι → MinkowskiFunctional E) :
    ∃ A ∈ boundedBodies R,
      (∀ i, F i A = ⨍ y in Z, F i (K y)) ∧
      (⨍ y in Z, rootVolume (K y)) ≤ rootVolume A := by
  first
  | have hF (i : ι) := functional_fiber_integrable hZ hK hR (F i)
    have hFi : IntegrableOn (fun y => fun i => F i (K y)) Z := Integrable.of_eval hF
    have hroot := rootVolume_fiber_integrable hdim hZ hK hR
    have hs := finiteObservation_image_convex hdim F R
    have hsc := ((bodyHypograph_compact R).image (continuous_finiteObservation F)).isClosed
    have hvol0 : volume Z ≠ 0 := by
      first
      | intro hz
        simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hvol
    have hp := hs.set_average_mem hsc hvol0 hZ.measure_ne_top
      (show ∀ᵐ y ∂volume.restrict Z,
        (fun i => F i (K y), rootVolume (K y)) ∈ finiteObservation F '' bodyHypograph R from by
        filter_upwards [ae_restrict_mem hZ.measurableSet] with y hy
        exact ⟨(K y, rootVolume (K y)), ⟨hR y hy, rootVolume_nonnegative _, le_rfl⟩, rfl⟩)
      (hFi.prodMk hroot)
    rw [average_pair hFi hroot] at hp
    obtain ⟨⟨A, z⟩, ⟨hA, hz0, hzA⟩, hobs⟩ := hp
    have hz : z = ⨍ y in Z, rootVolume (K y) := congrArg Prod.snd hobs
    refine ⟨A, hA, ?_, hz ▸ hzA⟩
    intro i
    have hi := congrArg (fun p : (ι → ℝ) × ℝ => p.1 i) hobs
    simpa only [finiteObservation, setAverage_eq, Pi.smul_apply, smul_eq_mul,
      eval_integral hF i] using hi

/-- Existence of a single actual Minkowski average, with the Brunn--Minkowski
lower bound and all continuous monotone Minkowski functionals preserved. -/
theorem exists_average_body (hdim : finrank ℝ E ≠ 0)
    (hZ : IsCompact Z) (hvol : 0 < volume.real Z) (hK : FiberConcave Z K)
    {R : ℝ} (hR : ∀ y ∈ Z, K y ∈ boundedBodies R) :
    ∃ A ∈ boundedBodies R,
      (∀ φ : MinkowskiFunctional E, φ A = ⨍ y in Z, φ (K y)) ∧
      (⨍ y in Z, rootVolume (K y)) ≤ rootVolume A := by
  first
  | classical
    let q : ℝ := ⨍ y in Z, rootVolume (K y)
    let C : Set (ConvexBody E) := boundedBodies R ∩ {A | q ≤ rootVolume A}
    have hC : IsCompact C := (boundedBodies_compact R).inter_right
      (isClosed_le continuous_const continuous_rootVolume)
    let T : MinkowskiFunctional E → Set (ConvexBody E) :=
      fun φ => {A | φ A = ⨍ y in Z, φ (K y)}
    have hT (φ : MinkowskiFunctional E) : IsClosed (T φ) :=
      isClosed_eq φ.continuous_toFun continuous_const
    have hfinite (s : Finset (MinkowskiFunctional E)) : (C ∩ ⋂ φ ∈ s, T φ).Nonempty := by
      first
      | obtain ⟨A, hA, heq, hq⟩ := finite_average_body hdim hZ hvol hK hR
          (fun φ : s => φ.1)
        refine ⟨A, ⟨hA, hq⟩, ?_⟩
        simp only [mem_iInter]
        intro φ hφ
        exact heq ⟨φ, hφ⟩
    obtain ⟨A, hA, hAT⟩ := hC.inter_iInter_nonempty T hT hfinite
    exact ⟨A, hA.1, fun φ => mem_iInter.mp hAT φ, hA.2⟩

theorem average_body_unique {A B : ConvexBody E}
    (hA : ∀ φ : MinkowskiFunctional E, φ A = ⨍ y in Z, φ (K y))
    (hB : ∀ φ : MinkowskiFunctional E, φ B = ⨍ y in Z, φ (K y)) : A = B :=
  MinkowskiFunctional.separating (fun φ => (hA φ).trans (hB φ).symm)

end Fibers

end VolumePolynomials.MinkowskiAverages
