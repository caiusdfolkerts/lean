module

public import volume_polynomials.mixed_volume_basis
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Analysis.SpecificLimits.Normed

set_option Elab.async false

/- BEGIN SOURCE: MixedVolume/ScalarPolynomial.lean -/
section


/-!
An explicit rational twelve-label cubic for the scalar section.

This file contains the algebraic specification; the full geometric
equivalence is developed in MixedVolume.DeficitConstruction and the
rational quadratic section in MixedVolume.ScalarSection. Verification status
is recorded in the build and axiom-audit manifests.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ScalarPolynomial

open scoped BigOperators

abbrev Label := Fin 12
abbrev Parameter := Fin 3

def stateLabel (i : Parameter) : Label := ⟨5 + i.val, by omega⟩
def imageLabel (i : Parameter) : Label := ⟨8 + i.val, by omega⟩
def deficitLabel : Label := 11

def rate (i : Parameter) : ℚ :=
  if i = 0 then 1 else if i = 1 then 1 / 2 else 1 / 4

def heightRat (i : Parameter) : ℚ := 1 / (1 - rate i / 4)
def widthRat (i : Parameter) : ℚ :=
  heightRat i - 1 / (1 - rate i / 8)
def areaRat (i : Parameter) : ℚ :=
  widthRat i / (1 - rate i ^ 2 / 32)
def mixedRat (i j : Parameter) : ℚ :=
  (widthRat i + widthRat j) / (1 - rate i * rate j / 32)

theorem mixedRat_comm (i j : Parameter) : mixedRat i j = mixedRat j i := by
  unfold mixedRat
  rw [add_comm, mul_comm]

section Algebra

variable {R : Type*} [CommRing R] [Algebra ℚ R]

def rat (q : ℚ) : R := algebraMap ℚ R q

def height (b : Parameter → R) : R :=
  rat (heightRat 0) * b 0 +
  rat (heightRat 1) * b 1 +
  rat (heightRat 2) * b 2

def width (b : Parameter → R) : R :=
  rat (widthRat 0) * b 0 +
  rat (widthRat 1) * b 1 +
  rat (widthRat 2) * b 2

def quadratic (b : Parameter → R) : R :=
  rat (areaRat 0) * b 0 ^ 2 +
  rat (areaRat 1) * b 1 ^ 2 +
  rat (areaRat 2) * b 2 ^ 2 +
  rat (mixedRat 0 1) * b 0 * b 1 +
  rat (mixedRat 0 2) * b 0 * b 2 +
  rat (mixedRat 1 2) * b 1 * b 2

def bilinear (b c : Parameter → R) : R :=
  2 * rat (areaRat 0) * b 0 * c 0 +
  2 * rat (areaRat 1) * b 1 * c 1 +
  2 * rat (areaRat 2) * b 2 * c 2 +
  rat (mixedRat 0 1) * (b 0 * c 1 + b 1 * c 0) +
  rat (mixedRat 0 2) * (b 0 * c 2 + b 2 * c 0) +
  rat (mixedRat 1 2) * (b 1 * c 2 + b 2 * c 1)

def divideRates (c : Parameter → R) : Parameter → R :=
  fun i => rat (1 / rate i) * c i

def componentSum (b : Parameter → R) : R := b 0 + b 1 + b 2

theorem height_add (b c : Parameter → R) :
    height (fun i => b i + c i) = height b + height c := by
  unfold height
  ring

theorem width_add (b c : Parameter → R) :
    width (fun i => b i + c i) = width b + width c := by
  unfold width
  ring

theorem quadratic_add (b c : Parameter → R) :
    quadratic (fun i => b i + c i) =
      quadratic b + bilinear b c + quadratic c := by
  unfold quadratic bilinear
  ring

theorem quadratic_shift (b a : Parameter → R) (z : R) :
    quadratic (fun i => b i - a i * z) =
      quadratic b - z * bilinear b a + z ^ 2 * quadratic a := by
  unfold quadratic bilinear
  ring

/-- The complete reference-only cubic; the omitted e2 e3 sI coefficient is zero. -/
def referenceCubic (e₁ e₂ e₃ s ι : R) : R :=
  e₁ * e₂ * e₃ + e₁ * e₂ * s + e₁ * e₂ * ι +
  2 * e₁ * e₃ * s + e₁ * e₃ * ι + e₁ * s * ι +
  e₂ * e₃ * s + e₂ * s * ι + e₃ * s * ι

/--
The complete canonical cubic.

The five scalar arguments are the weights of S(e1), S(e2), S(e3),
S((-1,-2,1)), and S((0,-1,1)). The b arguments are the three
W_r in the XZ plane; the c arguments are T W_r in the XY plane.
Every term is an ordinary monomial coefficient contribution.
-/
def canonicalFormula (e₁ e₂ e₃ s ι : R)
    (b c : Parameter → R) : R :=
  quadratic b * (rat (1 / 4) * height c) +
  rat (1 / 32) * quadratic c * height b +
  e₁ * height b * (rat (1 / 4) * height c) +
  e₂ * (quadratic b + width (divideRates c) * height b) +
  e₃ * (rat (1 / 32) * quadratic c +
    width b * (rat (1 / 4) * height c)) +
  s * rat (1 / 32) * quadratic (fun i => 8 * b i + c i) +
  ι * (quadratic (fun i => b i + divideRates c i) -
    componentSum (divideRates c) * width (fun i => b i + divideRates c i)) +
  e₁ * e₂ * height b +
  e₁ * e₃ * (rat (1 / 4) * height c) +
  e₁ * s * (2 * height b + rat (1 / 4) * height c) +
  e₁ * ι * (height b + rat (1 / 4) * height c) +
  e₂ * e₃ * (width b + width (divideRates c)) +
  e₂ * s * (width b + height b + width (divideRates c)) +
  e₂ * ι * (width b + width (divideRates c)) +
  e₃ * s * (2 * width b + rat (1 / 4) * width c) +
  e₃ * ι * (width b + width (divideRates c)) +
  s * ι * (height b - width b +
    rat (1 / 4) * height c - width (divideRates c)) +
  referenceCubic e₁ e₂ e₃ s ι

/-- Coefficient of the quadratic dependence on the state weights. -/
def kappa (e₂ s ι : R) (c : Parameter → R) : R :=
  rat (1 / 4) * height c + e₂ + 64 * rat (1 / 32) * s + ι

def linearHeight (e₁ e₂ s ι : R) (c : Parameter → R) : R :=
  rat (1 / 32) * quadratic c +
  rat (1 / 4) * e₁ * height c +
  e₂ * width (divideRates c) +
  e₁ * e₂ + 2 * e₁ * s + e₁ * ι + e₂ * s + s * ι

def linearWidth (e₂ e₃ s ι : R) (c : Parameter → R) : R :=
  rat (1 / 4) * e₃ * height c -
  ι * componentSum (divideRates c) +
  e₂ * e₃ + e₂ * s + e₂ * ι +
  2 * e₃ * s + e₃ * ι - s * ι

def linearStatePart (e₁ e₂ e₃ s ι : R)
    (a c : Parameter → R) : R :=
  linearHeight e₁ e₂ s ι c * height a +
  linearWidth e₂ e₃ s ι c * width a +
  8 * rat (1 / 32) * s * bilinear a c +
  ι * bilinear a (divideRates c)

/--
An exact full-polynomial identity. It exhibits parameter degree at most two
without discarding any body-variable coefficient.
-/
theorem canonicalFormula_shift (e₁ e₂ e₃ s ι z : R)
    (b c a : Parameter → R) :
    canonicalFormula e₁ e₂ e₃ s ι (fun i => b i - a i * z) c =
      canonicalFormula e₁ e₂ e₃ s ι b c -
        z * (kappa e₂ s ι c * bilinear b a +
          linearStatePart e₁ e₂ e₃ s ι a c) +
        z ^ 2 * kappa e₂ s ι c * quadratic a := by
  unfold canonicalFormula kappa linearStatePart linearHeight linearWidth
    quadratic bilinear height width componentSum
  ring

end Algebra

def canonicalRationalPolynomial : MvPolynomial Label ℚ :=
  canonicalFormula (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.X 3) (MvPolynomial.X 4)
    (fun i => MvPolynomial.X (stateLabel i))
    (fun i => MvPolynomial.X (imageLabel i))

noncomputable def targetPolynomial (a : Parameter → ℝ) : MvPolynomial Label ℝ :=
  canonicalFormula (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.X 3) (MvPolynomial.X 4)
    (fun i => MvPolynomial.X (stateLabel i) -
      MvPolynomial.C (a i) * MvPolynomial.X deficitLabel)
    (fun i => MvPolynomial.X (imageLabel i))

def targetValue (a : Parameter → ℝ) (w : Label → ℝ) : ℝ :=
  canonicalFormula (w 0) (w 1) (w 2) (w 3) (w 4)
    (fun i => w (stateLabel i) - a i * w deficitLabel)
    (fun i => w (imageLabel i))

theorem eval_targetPolynomial (a : Parameter → ℝ) (w : Label → ℝ) :
    MvPolynomial.eval w (targetPolynomial a) = targetValue a w := by
  simp [targetPolynomial, targetValue, canonicalFormula, referenceCubic,
    quadratic, height, width, componentSum, divideRates, rat,
    MvPolynomial.algebraMap_apply]

/--
The proposition quantifies over genuine nonempty compact convex bodies
and demands equality of the entire volume polynomial on all nonnegative
weights. It does not postulate calibrated shapes or recurrence equations.
-/
def TargetRealizable (a : Parameter → ℝ) : Prop :=
  ∃ K : Label → VolumePolynomials.Body 3,
    ∀ t : Label → ℝ, (∀ i, 0 ≤ t i) →
      MvPolynomial.eval t (targetPolynomial a) =
        VolumePolynomials.volumeFunction K t

def cone (a : Parameter → ℝ) : Prop :=
  ∀ n : ℕ, a 0 + (1 / 2 : ℝ) ^ n * a 1 + (1 / 4 : ℝ) ^ n * a 2 ≤ 0

end MixedVolume.ScalarPolynomial

end

end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ScalarPolynomial.lean -/

/- BEGIN SOURCE: MixedVolume/ReferenceCalibration.lean -/
section


/-! Exhaustive sign calibration for the five references of the scalar section.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ReferenceCalibration

open VolumePolynomials VolumePolynomials.Holonomy
open scoped Pointwise

def sDirection : Space 3 := ![-1, -2, 1]
def iDirection : Space 3 := ![0, -1, 1]

theorem scalar_signs (vx vy vz wy wz : ℝ)
    (hx : |vx| = 1) (hy : |vy| = 2) (hz : |vz| = 1)
    (hwy : |wy| = 1) (hwz : |wz| = 1)
    (hpair : |vy * wz - vz * wy| = 1) :
    vz * (-vz * vx) * vx = -1 ∧
    vz * (-wz * wy) * vy = -2 ∧ vz * vz = 1 ∧
    wz * (-wz * wy) * wy = -1 ∧ wz * wz = 1 := by
  rcases eq_or_eq_neg_of_abs_eq hx with rfl | rfl <;>
    rcases eq_or_eq_neg_of_abs_eq hy with rfl | rfl <;>
    rcases eq_or_eq_neg_of_abs_eq hz with rfl | rfl <;>
    rcases eq_or_eq_neg_of_abs_eq hwy with rfl | rfl <;>
    rcases eq_or_eq_neg_of_abs_eq hwz with rfl | rfl <;>
    norm_num at *

/-- A single coordinate reflection fixes the coordinate segments and calibrates
both oblique segments, with only independent segment orientations remaining. -/
theorem calibrate_vectors (v w : Space 3)
    (hx : |v 0| = 1) (hy : |v 1| = 2) (hz : |v 2| = 1)
    (hwx : w 0 = 0) (hwy : |w 1| = 1) (hwz : |w 2| = 1)
    (hpair : |v 1 * w 2 - v 2 * w 1| = 1) :
    ∃ g : Space 3 ≃L[ℝ] Space 3,
      |LinearMap.det g.toLinearMap| = 1 ∧
      (∀ k : Fin 3, ∃ s : ℝ, g (axis k) = s • axis k) ∧
      (∀ k : Fin 3, mapBody g.toContinuousLinearMap (centeredBody (axis k)) = centeredBody (axis k)) ∧
      mapBody g.toContinuousLinearMap (centeredBody v) = centeredBody sDirection ∧
      mapBody g.toContinuousLinearMap (centeredBody w) = centeredBody iDirection := by
  let σ : Space 3 := ![-v 2 * v 0, -w 2 * w 1, 1]
  have hσ : ∀ k, |σ k| = 1 := by
    intro k
    fin_cases k <;> simp [σ, abs_mul, hz, hx, hwy, hwz]
  let g := coordinateReflection σ hσ
  have hs := scalar_signs (v 0) (v 1) (v 2) (w 1) (w 2) hx hy hz hwy hwz hpair
  have hv : (v 2) • g v = sDirection := by
    ext k
    fin_cases k
    · simpa [g, coordinateReflection, σ, sDirection, mul_assoc] using hs.1
    · simpa [g, coordinateReflection, σ, sDirection, mul_assoc] using hs.2.1
    · simpa [g, coordinateReflection, σ, sDirection] using hs.2.2.1
  have hw : (w 2) • g w = iDirection := by
    ext k
    fin_cases k
    · simp [g, coordinateReflection, σ, iDirection, hwx]
    · simpa [g, coordinateReflection, σ, iDirection, mul_assoc] using hs.2.2.2.1
    · simpa [g, coordinateReflection, σ, iDirection] using hs.2.2.2.2
  refine ⟨g, coordinateReflection_abs_det σ hσ, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨σ k, coordinateReflection_basis σ hσ k⟩
  · intro k
    rw [map_centeredBody]
    change centeredBody (g (axis k)) = centeredBody (axis k)
    have hk : g (axis k) = σ k • axis k := coordinateReflection_basis σ hσ k
    rw [hk]
    exact centeredBody_smul_sign (σ k) (hσ k) (axis k)
  · rw [map_centeredBody]
    change centeredBody (g v) = centeredBody sDirection
    exact (centeredBody_smul_sign (v 2) hz (g v)).symm.trans (congrArg centeredBody hv)
  · rw [map_centeredBody]
    change centeredBody (g w) = centeredBody iDirection
    exact (centeredBody_smul_sign (w 2) hwz (g w)).symm.trans (congrArg centeredBody hw)

end MixedVolume.ReferenceCalibration

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ReferenceCalibration.lean -/

/- BEGIN SOURCE: MixedVolume/ReferenceNormalization.lean -/
section


/-! Five-reference calibration extracted from the literal full target polynomial.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ReferenceNormalization

open VolumePolynomials VolumePolynomials.Holonomy ScalarPolynomial Set
open scoped BigOperators Pointwise

def referenceLabel (i : Fin 5) : Label := ⟨i.val, by omega⟩
def frameLabel (i : Fin 3) : Label := ⟨i.val, by omega⟩
def unitWeight (i : Label) : Label → ℝ := Pi.single i 1

theorem unitWeight_nonneg (i j : Label) : 0 ≤ unitWeight i j := by
  simp only [unitWeight, Pi.single_apply]
  split <;> norm_num

theorem weightedSum_unit (K : Label → Body 3) (i : Label) : weightedSum K (unitWeight i) = K i := by
  rw [unitWeight, weightedSum_single, one_smul]

theorem volume_pair (K : Label → Body 3) (i j : Label) :
    volumeFunction K (unitWeight i + unitWeight j) = bodyVolume (K i + K j) := by
  rw [volumeFunction, weightedSum_add K _ _ (unitWeight_nonneg i) (unitWeight_nonneg j),
    weightedSum_unit, weightedSum_unit]

theorem volume_triple (K : Label → Body 3) (i j k : Label) :
    volumeFunction K (unitWeight i + unitWeight j + unitWeight k) = bodyVolume (K i + K j + K k) := by
  rw [volumeFunction, weightedSum_add K (unitWeight i + unitWeight j) (unitWeight k)
    (fun h => add_nonneg (unitWeight_nonneg i h) (unitWeight_nonneg j h)) (unitWeight_nonneg k),
    weightedSum_add K _ _ (unitWeight_nonneg i) (unitWeight_nonneg j),
    weightedSum_unit, weightedSum_unit, weightedSum_unit]

def IsTarget (a : Parameter → ℝ) (K : Label → Body 3) : Prop :=
  ∀ w, (∀ i, 0 ≤ w i) → targetValue a w = volumeFunction K w

theorem targetRealizable_iff (a : Parameter → ℝ) :
    TargetRealizable a ↔ ∃ K, IsTarget a K := by
  simp only [TargetRealizable, IsTarget, eval_targetPolynomial]

structure Tests (K : Label → Body 3) : Prop where
  segmentZero : ∀ i : Fin 5, ∀ j : Fin 3,
    bodyVolume (K (referenceLabel i) + K (frameLabel j)) = 0
  frameVolume : bodyVolume (K 0 + K 1 + K 2) = 1
  sx : bodyVolume (K 3 + K 1 + K 2) = 1
  sy : bodyVolume (K 3 + K 0 + K 2) = 2
  sz : bodyVolume (K 3 + K 0 + K 1) = 1
  ix : bodyVolume (K 4 + K 1 + K 2) = 0
  iy : bodyVolume (K 4 + K 0 + K 2) = 1
  iz : bodyVolume (K 4 + K 0 + K 1) = 1
  obliquePair : bodyVolume (K 0 + K 3 + K 4) = 1
  statePlane : ∀ i, bodyVolume (K (stateLabel i) + K 0 + K 2) = 0
  imagePlane : ∀ i, bodyVolume (K (imageLabel i) + K 0 + K 1) = 0
  deficitPlane : bodyVolume (K deficitLabel + K 0 + K 2) = 0

theorem isTarget_tests {a : Parameter → ℝ} {K : Label → Body 3} (hK : IsTarget a K) : Tests K := by
  have hp (i j : Label) : bodyVolume (K i + K j) = targetValue a (unitWeight i + unitWeight j) := by
    rw [← volume_pair]
    exact (hK _ (fun h => add_nonneg (unitWeight_nonneg i h) (unitWeight_nonneg j h))).symm
  have ht (i j k : Label) : bodyVolume (K i + K j + K k) =
      targetValue a (unitWeight i + unitWeight j + unitWeight k) := by
    rw [← volume_triple]
    exact (hK _ (fun h => add_nonneg
      (add_nonneg (unitWeight_nonneg i h) (unitWeight_nonneg j h)) (unitWeight_nonneg k h))).symm
  constructor
  · intro i j
    rw [hp]
    fin_cases i <;> fin_cases j <;>
      norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
        componentSum, divideRates, unitWeight, referenceLabel, frameLabel,
        stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · rw [ht]
    norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · rw [ht]
    norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · rw [ht]
    norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · rw [ht]
    norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · rw [ht]
    norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · rw [ht]
    norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · rw [ht]
    norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · rw [ht]
    norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · intro i
    rw [ht]
    fin_cases i <;>
      norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
        componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · intro i
    rw [ht]
    fin_cases i <;>
      norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
        componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]
  · rw [ht]
    norm_num [targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, Pi.single_apply]

theorem IsTarget.of_same_volume {a : Parameter → ℝ} {K L : Label → Body 3}
    (hK : IsTarget a K) (heq : volumeFunction L = volumeFunction K) : IsTarget a L := by
  intro w hw
  rw [heq]
  exact hK w hw

theorem IsTarget.translate {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (p : Label → Space 3) :
    IsTarget a (fun i => translateBody (p i) (K i)) := by
  apply hK.of_same_volume
  funext w
  exact volumeFunction_translate K p w

theorem IsTarget.map {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (g : Space 3 ≃L[ℝ] Space 3)
    (hg : |LinearMap.det g.toLinearMap| = 1) :
    IsTarget a (fun i => mapBody g.toContinuousLinearMap (K i)) := by
  apply hK.of_same_volume
  funext w
  rw [volumeFunction_map]
  change |LinearMap.det g.toLinearMap| * volumeFunction K w = volumeFunction K w
  rw [hg, one_mul]

theorem Tests.segments {K : Label → Body 3} (h : Tests K)
    (hz : ∀ i, (0 : Space 3) ∈ K i) :
    ∀ i : Fin 5, ∃ x y : Space 3,
      x ∈ K (referenceLabel i) ∧ y ∈ K (referenceLabel i) ∧
        K (referenceLabel i) = segmentBody x y := by
  intro i
  obtain ⟨x, y, hx, hy, hxy⟩ := body_is_segment_of_three_zero_volumes
    (K (referenceLabel i)) (K 0) (K 1) (K 2)
    (hz _) (hz _) (hz _) (hz _)
    (h.segmentZero i 0) (h.segmentZero i 1) (h.segmentZero i 2)
    (by rw [h.frameVolume]; norm_num)
  exact ⟨x, y, hx, hy, body_eq_segmentBody hxy⟩

theorem normalize_origins {a : Parameter → ℝ} (K : Label → Body 3) (hK : IsTarget a K) :
    ∃ L : Label → Body 3, ∃ u : Fin 5 → Space 3,
      IsTarget a L ∧ (∀ i, (0 : Space 3) ∈ L i) ∧
        ∀ i, L (referenceLabel i) = segmentBody 0 (u i) := by
  classical
  choose p hp using fun i => (K i).nonempty
  let K₀ : Label → Body 3 := fun i => translateBody (-p i) (K i)
  have hK₀ : IsTarget a K₀ := hK.translate (fun i => -p i)
  have hz₀ : ∀ i, (0 : Space 3) ∈ K₀ i := fun i => zero_mem_translateBody_neg (hp i)
  choose x y hx hy hxy using (isTarget_tests hK₀).segments hz₀
  let v : Label → Space 3 := fun i => if h : i.val < 5 then -x ⟨i.val, h⟩ else 0
  let L : Label → Body 3 := fun i => translateBody (v i) (K₀ i)
  refine ⟨L, fun i => y i - x i, hK₀.translate v, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < 5
    · let j : Fin 5 := ⟨i.val, hi⟩
      have hji : referenceLabel j = i := Fin.ext rfl
      have hx' : x j ∈ K₀ i := by rw [← hji]; exact hx j
      simpa only [L, v, dif_pos hi] using zero_mem_translateBody_neg hx'
    · simpa only [L, v, dif_neg hi, translateBody_zero] using hz₀ i
  · intro i
    have hv : v (referenceLabel i) = -x i := by simp [v, referenceLabel, i.isLt]
    change translateBody (v (referenceLabel i)) (K₀ (referenceLabel i)) = _
    rw [hv, hxy i, translate_segmentBody, neg_add_cancel, neg_add_eq_sub]

theorem normalize_frame {a : Parameter → ℝ} (K : Label → Body 3) (hK : IsTarget a K) :
    ∃ L : Label → Body 3, ∃ u : Fin 5 → Space 3,
      IsTarget a L ∧ (∀ i, (0 : Space 3) ∈ L i) ∧
      (∀ i, L (referenceLabel i) = segmentBody 0 (u i)) ∧
      ∀ i : Fin 3, u ⟨i.val, by omega⟩ = axis i := by
  obtain ⟨P, v, hP, hz, hseg⟩ := normalize_origins K hK
  let vf : Fin 3 → Space 3 := fun i => v ⟨i.val, by omega⟩
  have hv : bodyVolume (∑ i, segmentBody 0 (vf i)) = 1 := by
    simp only [Fin.sum_univ_three, vf]
    change bodyVolume (segmentBody 0 (v 0) + segmentBody 0 (v 1) + segmentBody 0 (v 2)) = 1
    rw [← hseg 0, ← hseg 1, ← hseg 2]
    exact (isTarget_tests hP).frameVolume
  obtain ⟨g, hg, hgv⟩ := normalize_origin_segment_frame vf hv
  refine ⟨fun i => mapBody g.toContinuousLinearMap (P i), fun i => g (v i),
    hP.map g hg, ?_, ?_, hgv⟩
  · intro i
    exact ⟨0, hz i, map_zero g⟩
  · intro i
    change mapBody g.toContinuousLinearMap (P (referenceLabel i)) = segmentBody 0 (g (v i))
    rw [hseg, map_segmentBody, map_zero, ContinuousLinearEquiv.coe_coe]

structure Calibrated (K : Label → Body 3) : Prop where
  axes : ∀ i : Fin 3, K (frameLabel i) = centeredBody (axis i)
  oblique : K 3 = centeredBody ReferenceCalibration.sDirection
  identity : K 4 = centeredBody ReferenceCalibration.iDirection
  stateZero : ∀ i, (0 : Space 3) ∈ K (stateLabel i)
  imageZero : ∀ i, (0 : Space 3) ∈ K (imageLabel i)
  deficitZero : (0 : Space 3) ∈ K deficitLabel
  statePlane : ∀ i, ∀ x ∈ K (stateLabel i), x 1 = 0
  imagePlane : ∀ i, ∀ x ∈ K (imageLabel i), x 2 = 0
  deficitPlane : ∀ x ∈ K deficitLabel, x 1 = 0

/-- The reference directions and all planar supports are forced by the complete
ordinary coefficient array.  No geometric calibration is an input hypothesis. -/
theorem normalize_references {a : Parameter → ℝ} (K : Label → Body 3)
    (hK : IsTarget a K) : ∃ L, IsTarget a L ∧ Calibrated L := by
  classical
  obtain ⟨P, u, hP, hz, hseg, haxis⟩ := normalize_frame K hK
  have ht := isTarget_tests hP
  have he₀ : P 0 = segmentBody 0 (axis 0) := by
    exact (hseg 0).trans (congrArg (segmentBody 0) (haxis 0))
  have he₁ : P 1 = segmentBody 0 (axis 1) := by
    exact (hseg 1).trans (congrArg (segmentBody 0) (haxis 1))
  have he₂ : P 2 = segmentBody 0 (axis 2) := by
    exact (hseg 2).trans (congrArg (segmentBody 0) (haxis 2))
  have hs : P 3 = segmentBody 0 (u 3) := hseg 3
  have hi : P 4 = segmentBody 0 (u 4) := hseg 4
  have hs₀ : |u 3 0| = 1 := by
    simpa only [hs, he₁, he₂, axis, volume_coordinate_test₁] using ht.sx
  have hs₁ : |u 3 1| = 2 := by
    simpa only [hs, he₀, he₂, axis, volume_coordinate_test₂] using ht.sy
  have hs₂ : |u 3 2| = 1 := by
    simpa only [hs, he₀, he₁, axis, volume_coordinate_test₃] using ht.sz
  have hi₀ : u 4 0 = 0 := by
    have h := ht.ix
    simp only [hi, he₁, he₂, axis, volume_coordinate_test₁] at h
    exact abs_eq_zero.mp h
  have hi₁ : |u 4 1| = 1 := by
    simpa only [hi, he₀, he₂, axis, volume_coordinate_test₂] using ht.iy
  have hi₂ : |u 4 2| = 1 := by
    simpa only [hi, he₀, he₁, axis, volume_coordinate_test₃] using ht.iz
  have hsi : |u 3 1 * u 4 2 - u 3 2 * u 4 1| = 1 := by
    have h := ht.obliquePair
    simpa [he₀, hs, hi, volume_three_origin_segments, determinant3, axis] using h
  obtain ⟨g, hg, hga, hgaBody, hgs, hgi⟩ :=
    ReferenceCalibration.calibrate_vectors (u 3) (u 4)
      hs₀ hs₁ hs₂ hi₀ hi₁ hi₂ hsi
  have hstate : ∀ i, ∀ x ∈ P (stateLabel i), x 1 = 0 := by
    intro i
    apply coordinate_eq_zero_of_volume_zero (P (stateLabel i)) 0 2 1
      (by decide) (by decide) (by decide) (hz _)
    simpa only [he₀, he₂, coordinateSegment, axis] using ht.statePlane i
  have himage : ∀ i, ∀ x ∈ P (imageLabel i), x 2 = 0 := by
    intro i
    apply coordinate_eq_zero_of_volume_zero (P (imageLabel i)) 0 1 2
      (by decide) (by decide) (by decide) (hz _)
    simpa only [he₀, he₁, coordinateSegment, axis] using ht.imagePlane i
  have hdeficit : ∀ x ∈ P deficitLabel, x 1 = 0 := by
    apply coordinate_eq_zero_of_volume_zero (P deficitLabel) 0 2 1
      (by decide) (by decide) (by decide) (hz _)
    simpa only [he₀, he₂, coordinateSegment, axis] using ht.deficitPlane
  let R : Label → Body 3 := fun i => mapBody g.toContinuousLinearMap (P i)
  let t : Label → Space 3 := fun i => if h : i.val < 5 then
    -(1 / 2 : ℝ) • g (u ⟨i.val, h⟩) else 0
  let L : Label → Body 3 := fun i => translateBody (t i) (R i)
  have hL : IsTarget a L := (hP.map g hg).translate t
  have hLseg : ∀ i : Fin 5,
      L (referenceLabel i) = mapBody g.toContinuousLinearMap (centeredBody (u i)) := by
    intro i
    have ht' : t (referenceLabel i) = -(1 / 2 : ℝ) • g (u i) := by
      simp [t, referenceLabel, i.isLt]
    change translateBody (t (referenceLabel i))
      (mapBody g.toContinuousLinearMap (P (referenceLabel i))) = _
    rw [ht', hseg, map_segmentBody, map_zero, map_centeredBody]
    exact (centeredBody_eq_translate (g (u i))).symm
  have hLstate (i) : L (stateLabel i) = R (stateLabel i) := by
    simp [L, t, stateLabel]
  have hLimage (i) : L (imageLabel i) = R (imageLabel i) := by
    have hi : ¬ 8 + i.val < 5 := by omega
    simp [L, t, imageLabel, hi]
  have hLdeficit : L deficitLabel = R deficitLabel := by simp [L, t, deficitLabel]
  refine ⟨L, hL, ?_⟩
  constructor
  · intro i
    change L (referenceLabel ⟨i.val, by omega⟩) = _
    rw [hLseg, haxis, hgaBody]
  · exact (hLseg 3).trans hgs
  · exact (hLseg 4).trans hgi
  · intro i
    rw [hLstate]
    exact mapBody_zero_mem g.toContinuousLinearMap (hz _)
  · intro i
    rw [hLimage]
    exact mapBody_zero_mem g.toContinuousLinearMap (hz _)
  · rw [hLdeficit]
    exact mapBody_zero_mem g.toContinuousLinearMap (hz _)
  · intro i
    rw [hLstate]
    exact mapBody_coordinate_zero g.toContinuousLinearMap hga (hstate i)
  · intro i
    rw [hLimage]
    exact mapBody_coordinate_zero g.toContinuousLinearMap hga (himage i)
  · rw [hLdeficit]
    exact mapBody_coordinate_zero g.toContinuousLinearMap hga hdeficit

end MixedVolume.ReferenceNormalization

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ReferenceNormalization.lean -/

/- BEGIN SOURCE: MixedVolume/ScalarGeometry.lean -/
section


/-! Exact scalar geometric family for the twelve-body section.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ScalarGeometry

open VolumePolynomials Set Filter MeasureTheory
open scoped Topology Pointwise

abbrev Plane := ℝ × ℝ

def transition : Plane →L[ℝ] Plane where
  toFun p := ((p.1 + p.2) / 8, p.2 / 4)
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' r p := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring
  cont := by fun_prop

@[simp] theorem transition_apply (p : Plane) :
    transition p = ((p.1 + p.2) / 8, p.2 / 4) := rfl

def scaledTransition (r : ℝ) : Plane →L[ℝ] Plane := r • transition

/-- The n-th generator of W_r, expressed as two geometric sequences. -/
def generator (r : ℝ) (n : ℕ) : Plane :=
  ((r / 4) ^ n - (r / 8) ^ n, (r / 4) ^ n)

@[simp] theorem generator_zero (r : ℝ) : generator r 0 = (0, 1) := by
  simp [generator]

theorem generator_recurrence (r : ℝ) (n : ℕ) :
    generator r (n + 1) = scaledTransition r (generator r n) := by
  ext <;> simp only [generator, scaledTransition, ContinuousLinearMap.smul_apply,
    transition_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, pow_succ] <;> ring

theorem generator_norm (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    ‖generator r n‖ = (r / 4) ^ n := by
  have h₄ : 0 ≤ (r / 4) ^ n := pow_nonneg (by positivity) n
  have h₈ : 0 ≤ (r / 8) ^ n := pow_nonneg (by positivity) n
  have hle : (r / 8) ^ n ≤ (r / 4) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  change max ‖(r / 4) ^ n - (r / 8) ^ n‖ ‖(r / 4) ^ n‖ = _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle),
    abs_of_nonneg h₄, max_eq_right (by linarith)]

theorem generator_summable (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    Summable fun n => ‖generator r n‖ := by
  simp only [generator_norm r hr₀]
  exact summable_geometric_of_lt_one (by positivity) (by linarith)

def body (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) : ConvexBody Plane :=
  segmentSeriesBody (generator r) (generator_summable r hr₀ hr₁)

@[simp] theorem body_carrier (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (body r hr₀ hr₁ : Set Plane) = segmentSeries (generator r) := rfl

theorem body_fixed (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (body r hr₀ hr₁ : Set Plane) = centeredSegment (0, 1) +
      scaledTransition r '' (body r hr₀ hr₁ : Set Plane) := by
  simpa only [body_carrier, generator_zero] using
    segmentSeries_fixed (scaledTransition r) (generator r)
      (generator_summable r hr₀ hr₁) (generator_recurrence r)

theorem transition_norm_le : ‖transition‖ ≤ (1 / 4 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  have hx : ‖p.1‖ ≤ ‖p‖ := le_max_left _ _
  have hy : ‖p.2‖ ≤ ‖p‖ := le_max_right _ _
  change max ‖(p.1 + p.2) / 8‖ ‖p.2 / 4‖ ≤ _
  apply max_le
  · rw [norm_div, Real.norm_ofNat]
    have hs := norm_add_le p.1 p.2
    nlinarith
  · rw [norm_div, Real.norm_ofNat]
    nlinarith

theorem scaledTransition_norm_le (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    ‖scaledTransition r‖ ≤ (1 / 4 : ℝ) := by
  rw [scaledTransition, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr₀]
  have h := mul_le_mul_of_nonneg_left transition_norm_le hr₀
  nlinarith

theorem scaledTransition_powers_tendsto_zero (r : ℝ)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    Tendsto (fun n : ℕ => ‖scaledTransition r ^ n‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => (norm_pow_le _ n).trans
      (pow_le_pow_left₀ (norm_nonneg _) (scaledTransition_norm_le r hr₀ hr₁) n))
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem body_unique (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (K : Set Plane) (hKc : IsCompact K) (hKn : K.Nonempty)
    (hK : K = centeredSegment (0, 1) + scaledTransition r '' K) :
    K = (body r hr₀ hr₁ : Set Plane) :=
  compact_affine_fixed_unique (scaledTransition r)
    (scaledTransition_powers_tendsto_zero r hr₀ hr₁)
    (centeredSegment (0, 1)) K (body r hr₀ hr₁)
    hKc (body r hr₀ hr₁).isCompact hKn (body r hr₀ hr₁).nonempty
    hK (body_fixed r hr₀ hr₁)

/-- Exact centre absorbing the affine translation in K = q + E + r T K. -/
def translationCenter (r : ℝ) (q : Plane) : Plane :=
  ((q.1 + r * q.2 / (8 * (1 - r / 4))) / (1 - r / 8),
    q.2 / (1 - r / 4))

theorem translationCenter_fixed (r : ℝ) (hr : r ≤ 1) (q : Plane) :
    translationCenter r q = q + scaledTransition r (translationCenter r q) := by
  have h₄ : 1 - r / 4 ≠ 0 := by linarith
  have h₈ : 1 - r / 8 ≠ 0 := by linarith
  have h₄' : 4 - r ≠ 0 := by linarith
  have h₈' : 8 - r ≠ 0 := by linarith
  ext <;> simp only [translationCenter, scaledTransition, ContinuousLinearMap.smul_apply,
    transition_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp [h₄, h₈, h₄', h₈'] <;> ring

theorem body_unique_up_to_translation (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (K : Set Plane) (hKc : IsCompact K) (hKn : K.Nonempty) (q : Plane)
    (hK : K = q +ᵥ (centeredSegment (0, 1) + scaledTransition r '' K)) :
    K = translationCenter r q +ᵥ (body r hr₀ hr₁ : Set Plane) := by
  let p := translationCenter r q
  have hp : p = q + scaledTransition r p := translationCenter_fixed r hr₁ q
  have hc : -p + q = scaledTransition r (-p) := by
    calc
      -p + q = -(q + scaledTransition r p) + q := congrArg (fun x => -x + q) hp
      _ = -(scaledTransition r p) := by abel
      _ = scaledTransition r (-p) := (map_neg (scaledTransition r) p).symm
  have hL : -p +ᵥ K = centeredSegment (0, 1) + scaledTransition r '' (-p +ᵥ K) := by
    calc
      -p +ᵥ K = -p +ᵥ (q +ᵥ (centeredSegment (0, 1) + scaledTransition r '' K)) :=
        congrArg (-p +ᵥ ·) hK
      _ = (-p + q) +ᵥ (centeredSegment (0, 1) + scaledTransition r '' K) := by
        simp only [vadd_vadd, vadd_eq_add]
      _ = scaledTransition r (-p) +ᵥ (centeredSegment (0, 1) + scaledTransition r '' K) := by
        rw [hc]
      _ = centeredSegment (0, 1) + (scaledTransition r (-p) +ᵥ scaledTransition r '' K) := by
        rw [add_vadd_comm]
      _ = centeredSegment (0, 1) + scaledTransition r '' (-p +ᵥ K) := by
        rw [Holonomy.linear_image_vadd]

  have heq := body_unique r hr₀ hr₁ (-p +ᵥ K)
    (hKc.vadd (-p)) hKn.vadd_set hL
  have := congrArg (fun S : Set Plane => p +ᵥ S) heq
  simpa only [vadd_vadd, vadd_eq_add, add_neg_cancel, zero_vadd] using this

def dyadicTag (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ n

theorem generator_factored (r : ℝ) (n : ℕ) :
    generator r n = r ^ n • ((1 / 4 : ℝ) ^ n • (dyadicTag n, 1)) := by
  have h₄ : r / 4 = r * (1 / 4) := by ring
  have h₈ : r / 8 = r * ((1 / 4) * (1 / 2)) := by ring
  ext <;> simp only [generator, dyadicTag, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, h₄, h₈, mul_pow] <;> ring

theorem dyadicTag_strictMono : StrictMono dyadicTag := by
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp [dyadicTag]
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

def tagNormal (k : ℕ) : Plane →L[ℝ] ℝ where
  toFun p := p.1 - dyadicTag k * p.2
  map_add' p q := by dsimp; ring
  map_smul' r p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring
  cont := by fun_prop

theorem tagNormal_generator (k n : ℕ) (r : ℝ) :
    tagNormal k (generator r n) =
      r ^ n * (1 / 4 : ℝ) ^ n * (dyadicTag n - dyadicTag k) := by
  rw [generator_factored]
  simp only [map_smul, smul_eq_mul]
  dsimp [tagNormal]
  ring

theorem tagNormal_generator_ne (k n : ℕ) (r : ℝ)
    (hr : 0 < r) (hn : n ≠ k) : tagNormal k (generator r n) ≠ 0 := by
  rw [tagNormal_generator]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero n hr.ne') (by positivity))
    (sub_ne_zero.mpr (dyadicTag_strictMono.injective.ne hn))

theorem body_exposed_face (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1) (k : ℕ) :
    ∃ p : Plane, (tagNormal k).toExposed (body r hr₀.le hr₁ : Set Plane) =
      {x | ∃ t : Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        x = p + (t : ℝ) • generator r k} := by
  exact exposed_face_eq_centered_segment (tagNormal k) (generator r)
    (generator_summable r hr₀.le hr₁) k
    (by rw [tagNormal_generator]; simp) (fun n hn => tagNormal_generator_ne k n r hr₀ hn)

end MixedVolume.ScalarGeometry

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ScalarGeometry.lean -/

/- BEGIN SOURCE: MixedVolume/SeriesProjection.lean -/
section


/-! Exact one-dimensional projections of actual compact segment series.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.SeriesProjection

open VolumePolynomials Set MeasureTheory
open scoped Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem summable_abs_image (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) : Summable fun n => |l (u n)| := by
  apply (hu.mul_left ‖l‖).of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs, abs_abs] using l.le_opNorm (u n)

theorem maximizing_value (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) :
    l (seriesPoint u (maximizingChoice l u)) = (1 / 2 : ℝ) * ∑' n, |l (u n)| := by
  classical
  rw [seriesPoint, l.map_tsum (series_summable u hu (maximizingChoice l u))]
  have hterm (n : ℕ) :
      l ((maximizingChoice l u n : ℝ) • u n) = (1 / 2 : ℝ) * |l (u n)| := by
    simp only [map_smul, smul_eq_mul]
    by_cases h : 0 ≤ l (u n)
    · simp only [maximizingChoice, if_pos h, abs_of_nonneg h]
    · simp only [maximizingChoice, if_neg h, abs_of_neg (lt_of_not_ge h)]
      ring
  simp_rw [hterm]
  exact tsum_mul_left

theorem image_segmentSeries (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) :
    l '' segmentSeries u =
      Icc (-(1 / 2 : ℝ) * ∑' n, |l (u n)|) ((1 / 2 : ℝ) * ∑' n, |l (u n)|) := by
  let M : ℝ := (1 / 2 : ℝ) * ∑' n, |l (u n)|
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (tsum_nonneg fun n => abs_nonneg _)
  have hmax : l (seriesPoint u (maximizingChoice l u)) = M := maximizing_value l u hu
  have hmin : l (seriesPoint u (maximizingChoice (-l) u)) = -M := by
    have h := maximizing_value (-l) u hu
    simp only [ContinuousLinearMap.neg_apply, abs_neg] at h
    change -l (seriesPoint u (maximizingChoice (-l) u)) = M at h
    linarith
  have hlo_eq : -(1 / 2 : ℝ) * (∑' n, |l (u n)|) = -M := by
    dsimp [M]
    ring
  rw [hlo_eq]
  change l '' segmentSeries u = Icc (-M) M
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hupper := maximizingChoice_maximal l u hu hy
    have hlower := maximizingChoice_maximal (-l) u hu hy
    rw [hmax] at hupper
    simp only [ContinuousLinearMap.neg_apply, hmin] at hlower
    constructor <;> linarith
  · have hlo : -M ∈ l '' segmentSeries u :=
      ⟨seriesPoint u (maximizingChoice (-l) u), ⟨_, rfl⟩, hmin⟩
    have hhi : M ∈ l '' segmentSeries u :=
      ⟨seriesPoint u (maximizingChoice l u), ⟨_, rfl⟩, hmax⟩
    have hseg := ((segmentSeries_convex u hu).linear_image l.toLinearMap).segment_subset hlo hhi
    simpa only [segment_eq_Icc (by linarith : -M ≤ M), ContinuousLinearMap.coe_coe] using hseg

theorem length_image_segmentSeries (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) :
    volume.real (l '' segmentSeries u) = ∑' n, |l (u n)| := by
  have hs : 0 ≤ ∑' n, |l (u n)| := tsum_nonneg fun n => abs_nonneg _
  rw [image_segmentSeries l u hu, Real.volume_real_Icc_of_le (by nlinarith)]
  ring

end MixedVolume.SeriesProjection

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/SeriesProjection.lean -/

/- BEGIN SOURCE: MixedVolume/ScalarMoments.lean -/
section


/-! Rational widths and areas from the exact contraction equations.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ScalarGeometry

open VolumePolynomials Set MeasureTheory
open scoped Pointwise

theorem body_height (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    PlanarCorner.height (body r hr₀ hr₁) = 1 / (1 - r / 4) := by
  change volume.real ((ContinuousLinearMap.snd ℝ ℝ ℝ) ''
    segmentSeries (generator r)) = _
  rw [SeriesProjection.length_image_segmentSeries _ _ (generator_summable r hr₀ hr₁)]
  have hterm (n : ℕ) : |(ContinuousLinearMap.snd ℝ ℝ ℝ) (generator r n)| = (r / 4) ^ n := by
    exact abs_of_nonneg (pow_nonneg (by positivity) n)
  simp_rw [hterm]
  rw [tsum_geometric_of_lt_one (by positivity) (by linarith), one_div]

theorem body_width (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    PlanarCorner.width (body r hr₀ hr₁) =
      1 / (1 - r / 4) - 1 / (1 - r / 8) := by
  change volume.real ((ContinuousLinearMap.fst ℝ ℝ ℝ) ''
    segmentSeries (generator r)) = _
  rw [SeriesProjection.length_image_segmentSeries _ _ (generator_summable r hr₀ hr₁)]
  have hterm (n : ℕ) :
      |(ContinuousLinearMap.fst ℝ ℝ ℝ) (generator r n)| = (r / 4) ^ n - (r / 8) ^ n := by
    apply abs_of_nonneg
    exact sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) (by linarith) n)
  simp_rw [hterm]
  rw [Summable.tsum_sub
    (summable_geometric_of_lt_one (by positivity : 0 ≤ r / 4) (by linarith))
    (summable_geometric_of_lt_one (by positivity : 0 ≤ r / 8) (by linarith)),
    tsum_geometric_of_lt_one (by positivity) (by linarith),
    tsum_geometric_of_lt_one (by positivity) (by linarith), one_div, one_div]

theorem transition_det : LinearMap.det transition.toLinearMap = (1 / 32 : ℝ) := by
  have heq : transition.toLinearMap =
      PlanarExtrusion.frameMap ((1 / 8 : ℝ), 0) ((1 / 8 : ℝ), (1 / 4 : ℝ)) := by
    ext p <;> dsimp [transition, PlanarExtrusion.frameMap] <;> ring
  rw [heq, PlanarExtrusion.frameMap_det]
  norm_num [PlanarExtrusion.determinant]

theorem area_transition (K : ConvexBody Plane) :
    volume.real (mapBody transition K : Set Plane) =
      (1 / 32 : ℝ) * volume.real (K : Set Plane) := by
  rw [PlanarEdges.area_mapBody, transition_det]
  norm_num

theorem mapBody_scaledTransition (r : ℝ) (K : ConvexBody Plane) :
    mapBody (scaledTransition r) K = r • mapBody transition K := by
  apply ConvexBody.ext
  simp only [coe_mapBody, ConvexBody.coe_smul, ← Set.image_smul, Set.image_image,
    scaledTransition, ContinuousLinearMap.smul_apply]

theorem body_recurrence (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    body r hr₀ hr₁ = PlanarCorner.unitY + r • mapBody transition (body r hr₀ hr₁) := by
  rw [← mapBody_scaledTransition]
  apply ConvexBody.ext
  change (body r hr₀ hr₁ : Set Plane) =
    PlanarExtrusion.centeredSegment (0, 1) + scaledTransition r '' (body r hr₀ hr₁ : Set Plane)
  rw [← centeredSegment_eq_planar]
  exact body_fixed r hr₀ hr₁

theorem scaled_transition_width (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    PlanarCorner.width (r • mapBody transition (body r hr₀ hr₁)) =
      PlanarCorner.width (body r hr₀ hr₁) := by
  have h := congrArg PlanarCorner.width (body_recurrence r hr₀ hr₁)
  rw [PlanarCorner.width_add, PlanarCorner.width_unitY, zero_add] at h
  exact h.symm

theorem body_area_equation (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    volume.real (body r hr₀ hr₁ : Set Plane) =
      r ^ 2 / 32 * volume.real (body r hr₀ hr₁ : Set Plane) +
        PlanarCorner.width (body r hr₀ hr₁) := by
  have h := PlanarCorner.area_add_scaled_unitY
    (r • mapBody transition (body r hr₀ hr₁)) (by norm_num : (0 : ℝ) ≤ 1)
  rw [one_smul, one_mul, PlanarCorner.area_smul _ hr₀,
    area_transition, scaled_transition_width r hr₀ hr₁] at h
  have heq : r • mapBody transition (body r hr₀ hr₁) + PlanarCorner.unitY = body r hr₀ hr₁ := by
    rw [add_comm]
    exact (body_recurrence r hr₀ hr₁).symm
  rw [heq] at h
  nlinarith

theorem body_area (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    volume.real (body r hr₀ hr₁ : Set Plane) =
      (1 / (1 - r / 4) - 1 / (1 - r / 8)) / (1 - r ^ 2 / 32) := by
  have hsquare : r ^ 2 ≤ 1 := pow_le_one₀ hr₀ hr₁
  have hd : 0 < 1 - r ^ 2 / 32 := by nlinarith
  apply (eq_div_iff hd.ne').mpr
  have h := body_area_equation r hr₀ hr₁
  rw [body_width r hr₀ hr₁] at h
  nlinarith

theorem body_area_pos (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    0 < volume.real (body r hr₀.le hr₁ : Set Plane) := by
  have hsquare : r ^ 2 ≤ 1 := pow_le_one₀ hr₀.le hr₁
  rw [body_area]
  apply div_pos
  · have h₄ : 0 < 1 - r / 4 := by linarith
    have h₈ : 1 - r / 4 < 1 - r / 8 := by linarith
    exact sub_pos.mpr (one_div_lt_one_div_of_lt h₄ h₈)
  · nlinarith

theorem mixed_body_equation (r s : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    2 * PlanarMixedForm.mixedArea volume (body r hr₀ hr₁) (body s hs₀ hs₁) =
      PlanarCorner.width (body r hr₀ hr₁) + PlanarCorner.width (body s hs₀ hs₁) +
        (r * s / 32) *
          (2 * PlanarMixedForm.mixedArea volume (body r hr₀ hr₁) (body s hs₀ hs₁)) := by
  let U := body r hr₀ hr₁
  let V := body s hs₀ hs₁
  let U' := r • mapBody transition U
  let V' := s • mapBody transition V
  have hU : U = PlanarCorner.unitY + U' := body_recurrence r hr₀ hr₁
  have hV : V = PlanarCorner.unitY + V' := body_recurrence s hs₀ hs₁
  have hee : PlanarMixedForm.mixedArea volume PlanarCorner.unitY PlanarCorner.unitY = 0 := by
    rw [PlanarMixedForm.mixedArea_diagonal volume PlanarCorner.plane_finrank,
      PlanarCorner.unitY, PlanarCorner.area_segmentBody]
  have hcross : PlanarMixedForm.mixedArea volume U' V' =
      (r * s / 32) * PlanarMixedForm.mixedArea volume U V := by
    dsimp [U', V']
    rw [PlanarMixedForm.mixedArea_smul_left volume _ _ hr₀,
      PlanarMixedForm.mixedArea_smul_right volume _ _ hs₀,
      PlanarEdges.mixedArea_mapBody, transition_det]
    norm_num
    ring
  have huwidth : 2 * PlanarMixedForm.mixedArea volume U' PlanarCorner.unitY = PlanarCorner.width U := by
    rw [PlanarCorner.twice_mixedArea_unitY]
    exact scaled_transition_width r hr₀ hr₁
  have hvwidth : 2 * PlanarMixedForm.mixedArea volume PlanarCorner.unitY V' = PlanarCorner.width V := by
    rw [PlanarMixedForm.mixedArea_symm, PlanarCorner.twice_mixedArea_unitY]
    exact scaled_transition_width s hs₀ hs₁
  have hexpand : PlanarMixedForm.mixedArea volume U V =
      PlanarMixedForm.mixedArea volume PlanarCorner.unitY PlanarCorner.unitY +
      PlanarMixedForm.mixedArea volume PlanarCorner.unitY V' +
      PlanarMixedForm.mixedArea volume U' PlanarCorner.unitY +
      PlanarMixedForm.mixedArea volume U' V' := by
    conv_lhs => rw [hU, hV]
    rw [PlanarMixedForm.mixedArea_add_left,
      PlanarMixedForm.mixedArea_add_right, PlanarMixedForm.mixedArea_add_right]
    ring
  change 2 * PlanarMixedForm.mixedArea volume U V = _
  rw [hee, hcross] at hexpand
  nlinarith

theorem mixed_body (r s : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    2 * PlanarMixedForm.mixedArea volume (body r hr₀ hr₁) (body s hs₀ hs₁) =
      ((1 / (1 - r / 4) - 1 / (1 - r / 8)) +
        (1 / (1 - s / 4) - 1 / (1 - s / 8))) / (1 - r * s / 32) := by
  have hprod : r * s ≤ 1 := (mul_le_mul hr₁ hs₁ hs₀ (by norm_num)).trans_eq (by norm_num)
  have hd : 0 < 1 - r * s / 32 := by linarith
  apply (eq_div_iff hd.ne').mpr
  have h := mixed_body_equation r s hr₀ hr₁ hs₀ hs₁
  rw [body_width r hr₀ hr₁, body_width s hs₀ hs₁] at h
  nlinarith

end MixedVolume.ScalarGeometry

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ScalarMoments.lean -/

/- BEGIN SOURCE: MixedVolume/ProjectedForcing.lean -/
section


/-! Recovering the scalar recurrences from literal projected areas.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ProjectedForcing

open VolumePolynomials VolumePolynomials.Holonomy ScalarPolynomial ReferenceNormalization
open Set MeasureTheory
open scoped Pointwise BigOperators

def state (K : Label → Body 3) (i : Parameter) : ConvexBody Plane :=
  mapBody (coordinateProjection 1) (K (stateLabel i))

def imageState (K : Label → Body 3) (i : Parameter) : ConvexBody Plane :=
  mapBody (coordinateProjection 2) (K (imageLabel i))

def deficit (K : Label → Body 3) : ConvexBody Plane :=
  mapBody (coordinateProjection 1) (K deficitLabel)

def projectionS : Space 3 →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp (projectionFrame 2 (-1, -2)).toContinuousLinearMap

def projectionI : Space 3 →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp (projectionFrame 2 (0, -1)).toContinuousLinearMap

@[simp] theorem projectionS_apply (x : Space 3) :
    projectionS x = (x 0 + x 2, x 1 + 2 * x 2) := by
  simp [projectionS, projectionFrame_apply, mul_comm]

@[simp] theorem projectionI_apply (x : Space 3) :
    projectionI x = (x 0, x 1 + x 2) := by
  simp [projectionI, projectionFrame_apply]

theorem extrusionS (L : Body 3) :
    bodyVolume (L + centeredBody ReferenceCalibration.sDirection) - bodyVolume L =
      volume.real (mapBody projectionS L : Set Plane) := by
  apply bodyExtrusion_eq_frame_projection L (projectionFrame 2 (-1, -2))
    (projectionFrame_measurePreserving 2 (-1, -2)) ReferenceCalibration.sDirection
  norm_num [projectionFrame_apply, ReferenceCalibration.sDirection]

theorem extrusionI (L : Body 3) :
    bodyVolume (L + centeredBody ReferenceCalibration.iDirection) - bodyVolume L =
      volume.real (mapBody projectionI L : Set Plane) := by
  apply bodyExtrusion_eq_frame_projection L (projectionFrame 2 (0, -1))
    (projectionFrame_measurePreserving 2 (0, -1)) ReferenceCalibration.iDirection
  norm_num [projectionFrame_apply, ReferenceCalibration.iDirection]

theorem _root_.MixedVolume.ReferenceNormalization.Calibrated.place_state {K : Label → Body 3} (hK : Calibrated K) (i) :
    K (stateLabel i) = mapBody embedXZ (state K i) := by
  apply ConvexBody.ext
  change _ = embedXZ '' (coordinateProjection 1 '' (K (stateLabel i) : Set (Space 3)))
  rw [Set.image_image]
  symm
  calc
    _ = id '' (K (stateLabel i) : Set (Space 3)) :=
      Set.image_congr (fun x hx => embedXZ_coordinateProjection (hK.statePlane i x hx))
    _ = _ := Set.image_id' _

theorem _root_.MixedVolume.ReferenceNormalization.Calibrated.place_image {K : Label → Body 3} (hK : Calibrated K) (i) :
    K (imageLabel i) = mapBody embedXY (imageState K i) := by
  apply ConvexBody.ext
  change _ = embedXY '' (coordinateProjection 2 '' (K (imageLabel i) : Set (Space 3)))
  rw [Set.image_image]
  symm
  calc
    _ = id '' (K (imageLabel i) : Set (Space 3)) :=
      Set.image_congr (fun x hx => embedXY_coordinateProjection (hK.imagePlane i x hx))
    _ = _ := Set.image_id' _

theorem _root_.MixedVolume.ReferenceNormalization.Calibrated.place_deficit {K : Label → Body 3} (hK : Calibrated K) :
    K deficitLabel = mapBody embedXZ (deficit K) := by
  apply ConvexBody.ext
  change _ = embedXZ '' (coordinateProjection 1 '' (K deficitLabel : Set (Space 3)))
  rw [Set.image_image]
  symm
  calc
    _ = id '' (K deficitLabel : Set (Space 3)) :=
      Set.image_congr (fun x hx => embedXZ_coordinateProjection (hK.deficitPlane x hx))
    _ = _ := Set.image_id' _

theorem projectionS_embedXZ : projectionS.comp embedXZ = (8 : ℝ) • ScalarGeometry.transition := by
  ext p <;> simp [projectionS_apply, embedXZ, ScalarGeometry.transition] <;> ring

theorem projectionS_embedXY : projectionS.comp embedXY = ContinuousLinearMap.id ℝ Plane := by
  ext p <;> simp [projectionS_apply, embedXY]

theorem projectionI_embedXZ : projectionI.comp embedXZ = ContinuousLinearMap.id ℝ Plane := by
  ext p <;> simp [projectionI_apply, embedXZ]

theorem projectionI_embedXY : projectionI.comp embedXY = ContinuousLinearMap.id ℝ Plane := by
  ext p <;> simp [projectionI_apply, embedXY]

theorem mapBody_id (B : ConvexBody Plane) : mapBody (ContinuousLinearMap.id ℝ Plane) B = B := by
  apply ConvexBody.ext
  exact Set.image_id' _

theorem mapBody_smul_map (r : ℝ) (f : Plane →L[ℝ] Plane) (B : ConvexBody Plane) :
    mapBody (r • f) B = r • mapBody f B := by
  apply ConvexBody.ext
  change (fun x => r • f x) '' (B : Set Plane) = r • (f '' (B : Set Plane))
  rw [← Set.image_smul, Set.image_image]

theorem _root_.MixedVolume.ReferenceNormalization.Calibrated.projectionS_state {K : Label → Body 3} (hK : Calibrated K) (i) :
    mapBody projectionS (K (stateLabel i)) =
      (8 : ℝ) • mapBody ScalarGeometry.transition (state K i) := by
  rw [hK.place_state, mapBody_comp, projectionS_embedXZ, mapBody_smul_map]

theorem _root_.MixedVolume.ReferenceNormalization.Calibrated.projectionS_image {K : Label → Body 3} (hK : Calibrated K) (i) :
    mapBody projectionS (K (imageLabel i)) = imageState K i := by
  rw [hK.place_image, mapBody_comp, projectionS_embedXY, mapBody_id]

theorem _root_.MixedVolume.ReferenceNormalization.Calibrated.projectionI_state {K : Label → Body 3} (hK : Calibrated K) (i) :
    mapBody projectionI (K (stateLabel i)) = state K i := by
  rw [hK.place_state, mapBody_comp, projectionI_embedXZ, mapBody_id]

theorem _root_.MixedVolume.ReferenceNormalization.Calibrated.projectionI_image {K : Label → Body 3} (hK : Calibrated K) (i) :
    mapBody projectionI (K (imageLabel i)) = imageState K i := by
  rw [hK.place_image, mapBody_comp, projectionI_embedXY, mapBody_id]

theorem _root_.MixedVolume.ReferenceNormalization.Calibrated.projectionI_vertical {K : Label → Body 3} (hK : Calibrated K) :
    mapBody projectionI (K 1) = PlanarCorner.unitY := by
  have haxis := hK.axes 1
  change K 1 = centeredBody (axis 1) at haxis
  rw [haxis]
  apply ConvexBody.ext
  change projectionI '' (centeredBody (axis 1) : Set (Space 3)) =
    PlanarExtrusion.centeredSegment (0, 1)
  rw [centeredBody_carrier, PlanarExtrusion.centeredSegment, Set.image_image]
  congr 1
  funext t
  simp [Function.comp_apply, map_smul, axis]

def delta (a : Parameter → ℝ) (j : Label) (w : Label → ℝ) : ℝ :=
  targetValue a (w + unitWeight j) - targetValue a w

theorem extrusion_eq_delta {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (j : Label) (v : Space 3) (π : Space 3 →L[ℝ] Plane)
    (hj : K j = centeredBody v)
    (hπ : ∀ L : Body 3, bodyVolume (L + centeredBody v) - bodyVolume L =
      volume.real (mapBody π L : Set Plane))
    (w : Label → ℝ) (hw : ∀ i, 0 ≤ w i) :
    volume.real (mapBody π (weightedSum K w) : Set Plane) = delta a j w := by
  rw [← hπ]
  have hsum : weightedSum K (w + unitWeight j) = weightedSum K w + centeredBody v := by
    rw [weightedSum_add K _ _ hw (unitWeight_nonneg j), weightedSum_unit, hj]
  rw [delta, hK (w + unitWeight j) (fun i => add_nonneg (hw i) (unitWeight_nonneg j i)), hK w hw]
  rw [volumeFunction, hsum]
  rfl

theorem extrusionS_eq_delta {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (w : Label → ℝ) (hw : ∀ i, 0 ≤ w i) :
    volume.real (mapBody projectionS (weightedSum K w) : Set Plane) = delta a 3 w :=
  extrusion_eq_delta hK 3 _ _ hcal.oblique extrusionS w hw

theorem extrusionI_eq_delta {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (w : Label → ℝ) (hw : ∀ i, 0 ≤ w i) :
    volume.real (mapBody projectionI (weightedSum K w) : Set Plane) = delta a 4 w :=
  extrusion_eq_delta hK 4 _ _ hcal.identity extrusionI w hw

theorem extrusionAxis_eq_delta {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (j : Fin 3)
    (w : Label → ℝ) (hw : ∀ i, 0 ≤ w i) :
    volume.real (mapBody (coordinateProjection j) (weightedSum K w) : Set Plane) =
      delta a (frameLabel j) w :=
  extrusion_eq_delta hK (frameLabel j) _ _ (hcal.axes j) (fun L => bodyExtrusion_axis L j) w hw

def weight (i : Label) (r : ℝ) : Label → ℝ := Pi.single i r

theorem weight_nonneg (i : Label) {r : ℝ} (hr : 0 ≤ r) : ∀ j, 0 ≤ weight i r j := by
  intro j
  simp only [weight, Pi.single_apply]
  split <;> positivity

theorem weightedSum_weight (K : Label → Body 3) (i : Label) (r : ℝ) :
    weightedSum K (weight i r) = r • K i := weightedSum_single K i r

theorem rate_pos (i : Parameter) : 0 < (rate i : ℝ) := by
  fin_cases i <;> norm_num [rate]

theorem areaRat_pos (i : Parameter) : 0 < (areaRat i : ℝ) := by
  fin_cases i <;> norm_num [areaRat, widthRat, heightRat, rate]

theorem state_area {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (i : Parameter) :
    volume.real (state K i : Set Plane) = (areaRat i : ℝ) := by
  have h := extrusionAxis_eq_delta hK hcal 1 (unitWeight (stateLabel i))
    (unitWeight_nonneg _)
  rw [weightedSum_unit] at h
  change volume.real (state K i : Set Plane) = _ at h
  rw [h]
  fin_cases i <;>
    norm_num [delta, targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, frameLabel,
      Pi.single_apply, areaRat, widthRat, heightRat, rate, rat]

theorem image_area {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (i : Parameter) :
    volume.real (imageState K i : Set Plane) = (areaRat i : ℝ) / 32 := by
  have h := extrusionAxis_eq_delta hK hcal 2 (unitWeight (imageLabel i))
    (unitWeight_nonneg _)
  rw [weightedSum_unit] at h
  change volume.real (imageState K i : Set Plane) = _ at h
  rw [h]
  fin_cases i <;>
    norm_num [delta, targetValue, canonicalFormula, referenceCubic, quadratic, height, width,
      componentSum, divideRates, unitWeight, stateLabel, imageLabel, deficitLabel, frameLabel,
      Pi.single_apply, areaRat, widthRat, heightRat, rate, rat]

theorem projected_sum_area {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (i : Parameter) :
    volume.real (↑(mapBody ScalarGeometry.transition (state K i) + imageState K i) : Set Plane) =
      (areaRat i : ℝ) / 8 := by
  let w := weight (stateLabel i) (1 / 8) + unitWeight (imageLabel i)
  have hn : ∀ j, 0 ≤ w j := fun j =>
    add_nonneg (weight_nonneg _ (by norm_num) j) (unitWeight_nonneg _ j)
  have h := extrusionS_eq_delta hK hcal w hn
  have hw : mapBody projectionS (weightedSum K w) =
      mapBody ScalarGeometry.transition (state K i) + imageState K i := by
    rw [show w = weight (stateLabel i) (1 / 8) + unitWeight (imageLabel i) from rfl,
      weightedSum_add K _ _ (weight_nonneg _ (by norm_num)) (unitWeight_nonneg _),
      weightedSum_weight, weightedSum_unit, mapBody_add, mapBody_smul,
      hcal.projectionS_state, hcal.projectionS_image, smul_smul]
    norm_num
  rw [hw] at h
  rw [h]
  fin_cases i <;>
    norm_num [delta, w, weight, targetValue, canonicalFormula, referenceCubic, quadratic,
      height, width, componentSum, divideRates, unitWeight, stateLabel, imageLabel,
      deficitLabel, Pi.single_apply, areaRat, widthRat, heightRat, rate, rat]

theorem images_forced {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (i : Parameter) :
    ∃ q : Plane, imageState K i =
      translateBody q (mapBody ScalarGeometry.transition (state K i)) := by
  let B := mapBody ScalarGeometry.transition (state K i)
  have hb : volume.real (B : Set Plane) = (areaRat i : ℝ) / 32 := by
    rw [ScalarGeometry.area_transition, state_area hK hcal]
    ring
  obtain ⟨q, hq⟩ := equal_area_translates B.convex B.isCompact
    (imageState K i).convex (imageState K i).isCompact
    (by rw [hb]; exact div_pos (areaRat_pos i) (by norm_num))
    (by rw [image_area hK hcal, hb])
    (by
      rw [← ConvexBody.coe_add]
      change volume.real (↑(mapBody ScalarGeometry.transition (state K i) + imageState K i) : Set Plane) = _
      rw [projected_sum_area hK hcal, hb]
      ring)
  exact ⟨q, ConvexBody.ext (by simpa only [coe_translateBody] using hq)⟩

theorem recurrence_area {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (i : Parameter) :
    volume.real (↑(PlanarCorner.unitY + (rate i : ℝ) • imageState K i) : Set Plane) =
      (areaRat i : ℝ) := by
  let w := unitWeight 1 + weight (imageLabel i) (rate i : ℝ)
  have hn : ∀ j, 0 ≤ w j := fun j =>
    add_nonneg (unitWeight_nonneg _ j) (weight_nonneg _ (rate_pos i).le j)
  have h := extrusionI_eq_delta hK hcal w hn
  have hw : mapBody projectionI (weightedSum K w) =
      PlanarCorner.unitY + (rate i : ℝ) • imageState K i := by
    rw [show w = unitWeight 1 + weight (imageLabel i) (rate i : ℝ) from rfl,
      weightedSum_add K _ _ (unitWeight_nonneg _) (weight_nonneg _ (rate_pos i).le),
      weightedSum_unit, weightedSum_weight, mapBody_add, mapBody_smul,
      hcal.projectionI_vertical, hcal.projectionI_image]
  rw [hw] at h
  rw [h]
  fin_cases i <;>
    norm_num [delta, w, weight, targetValue, canonicalFormula, referenceCubic, quadratic,
      height, width, componentSum, divideRates, unitWeight, stateLabel, imageLabel,
      deficitLabel, Pi.single_apply, areaRat, widthRat, heightRat, rate, rat]

theorem recurrence_sum_area {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (i : Parameter) :
    volume.real (↑(state K i + (PlanarCorner.unitY + (rate i : ℝ) • imageState K i)) : Set Plane) =
      4 * (areaRat i : ℝ) := by
  let w := unitWeight (stateLabel i) + (unitWeight 1 + weight (imageLabel i) (rate i : ℝ))
  have hn' : ∀ j, 0 ≤ (unitWeight 1 + weight (imageLabel i) (rate i : ℝ)) j := fun j =>
    add_nonneg (unitWeight_nonneg _ j) (weight_nonneg _ (rate_pos i).le j)
  have hn : ∀ j, 0 ≤ w j := fun j => add_nonneg (unitWeight_nonneg _ j) (hn' j)
  have h := extrusionI_eq_delta hK hcal w hn
  have hw : mapBody projectionI (weightedSum K w) =
      state K i + (PlanarCorner.unitY + (rate i : ℝ) • imageState K i) := by
    rw [show w = unitWeight (stateLabel i) +
        (unitWeight 1 + weight (imageLabel i) (rate i : ℝ)) from rfl,
      weightedSum_add K _ _ (unitWeight_nonneg _) hn',
      weightedSum_add K _ _ (unitWeight_nonneg _) (weight_nonneg _ (rate_pos i).le),
      weightedSum_unit, weightedSum_unit, weightedSum_weight,
      mapBody_add, mapBody_add, mapBody_smul, hcal.projectionI_state,
      hcal.projectionI_vertical, hcal.projectionI_image]
  rw [hw] at h
  rw [h]
  fin_cases i <;>
    norm_num [delta, w, weight, targetValue, canonicalFormula, referenceCubic, quadratic,
      height, width, componentSum, divideRates, unitWeight, stateLabel, imageLabel,
      deficitLabel, Pi.single_apply, areaRat, widthRat, heightRat, rate, rat]

theorem smul_translateBody (r : ℝ) (q : Plane) (B : ConvexBody Plane) :
    r • translateBody q B = translateBody (r • q) (r • B) := by
  simp only [translateBody, smul_add, ← pointBody_smul]

theorem recurrence_forced {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (i : Parameter) :
    ∃ q : Plane, state K i = translateBody q
      (PlanarCorner.unitY + (rate i : ℝ) • mapBody ScalarGeometry.transition (state K i)) := by
  let B := state K i
  let L := PlanarCorner.unitY + (rate i : ℝ) • imageState K i
  obtain ⟨q, hq⟩ := equal_area_translates B.convex B.isCompact L.convex L.isCompact
    (by rw [state_area hK hcal]; exact areaRat_pos i)
    (by simpa only [L, B, recurrence_area hK hcal, state_area hK hcal])
    (by simpa only [L, B, ← ConvexBody.coe_add, recurrence_sum_area hK hcal, state_area hK hcal])
  have hq' : L = translateBody q B := ConvexBody.ext (by simpa only [coe_translateBody] using hq)
  have hb : B = translateBody (-q) L := by
    rw [hq', translateBody_translate, neg_add_cancel, translateBody_zero]
  obtain ⟨p, hp⟩ := images_forced hK hcal i
  have hl : L = translateBody ((rate i : ℝ) • p)
      (PlanarCorner.unitY + (rate i : ℝ) • mapBody ScalarGeometry.transition B) := by
    dsimp [L]
    rw [hp, smul_translateBody]
    conv_lhs => lhs; rw [← translateBody_zero PlanarCorner.unitY]
    rw [translateBody_add, zero_add]
  refine ⟨-q + (rate i : ℝ) • p, ?_⟩
  rw [← translateBody_translate, ← hl]
  exact hb

theorem rate_le_one (i : Parameter) : (rate i : ℝ) ≤ 1 := by
  fin_cases i <;> norm_num [rate]

def canonicalState (i : Parameter) : ConvexBody Plane :=
  ScalarGeometry.body (rate i : ℝ) (rate_pos i).le (rate_le_one i)

theorem states_forced {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (i : Parameter) :
    ∃ q : Plane, state K i = translateBody q (canonicalState i) := by
  obtain ⟨p, hp⟩ := recurrence_forced hK hcal i
  have hp' : (state K i : Set Plane) = p +ᵥ
      (centeredSegment (0, 1) + ScalarGeometry.scaledTransition (rate i : ℝ) ''
        (state K i : Set Plane)) := by
    have h := congrArg (fun B : ConvexBody Plane => (B : Set Plane)) hp
    rw [← ScalarGeometry.mapBody_scaledTransition] at h
    simpa only [coe_translateBody, ConvexBody.coe_add, coe_mapBody,
      PlanarCorner.unitY, PlanarCorner.segmentBody, ConvexBody.coe_mk, ← centeredSegment_eq_planar] using h
  have h := ScalarGeometry.body_unique_up_to_translation (rate i : ℝ)
    (rate_pos i).le (rate_le_one i) (state K i : Set Plane)
    (state K i).isCompact (state K i).nonempty p hp'
  exact ⟨ScalarGeometry.translationCenter (rate i : ℝ) p,
    ConvexBody.ext (by simpa only [coe_translateBody, canonicalState] using h)⟩

end MixedVolume.ProjectedForcing

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ProjectedForcing.lean -/

/- BEGIN SOURCE: MixedVolume/ReferenceExpansion.lean -/
section


/-! A complete five-segment volume expansion obtained from actual extrusion.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ReferenceExpansion

open VolumePolynomials VolumePolynomials.Holonomy Set MeasureTheory
open ScalarPolynomial ProjectedForcing
open scoped Pointwise

section Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def linearWidth (l : E →L[ℝ] ℝ) (K : ConvexBody E) : ℝ :=
  volume.real (l '' (K : Set E))

def horizontalMap (l : E →L[ℝ] ℝ) : E →L[ℝ] Plane := l.prod 0

theorem linearWidth_eq_width (l : E →L[ℝ] ℝ) (K : ConvexBody E) :
    linearWidth l K = PlanarCorner.width (mapBody (horizontalMap l) K) := by
  dsimp [linearWidth, PlanarCorner.width, mapBody]
  rw [Set.image_image]
  rfl

theorem linearWidth_add (l : E →L[ℝ] ℝ) (K L : ConvexBody E) :
    linearWidth l (K + L) = linearWidth l K + linearWidth l L := by
  simp only [linearWidth_eq_width, mapBody_add, PlanarCorner.width_add]

theorem linearWidth_smul (l : E →L[ℝ] ℝ) (K : ConvexBody E)
    {r : ℝ} (hr : 0 ≤ r) : linearWidth l (r • K) = r * linearWidth l K := by
  simp only [linearWidth_eq_width, mapBody_smul, PlanarCorner.width_smul _ hr]

theorem linearWidth_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : F →L[ℝ] ℝ) (f : E →L[ℝ] F) (K : ConvexBody E) :
    linearWidth l (mapBody f K) = linearWidth (l.comp f) K := by
  dsimp [linearWidth]
  rw [Set.image_image]
  rfl

theorem image_centeredSegment [CompleteSpace E] (f : E →L[ℝ] Plane) (v : E) :
    f '' centeredSegment v = centeredSegment (f v) := by
  rw [centeredSegment_eq_image, centeredSegment_eq_image, Set.image_image]
  congr 1
  funext t
  exact f.map_smul t v

end Width

theorem linearWidth_centeredBody (l : Space 3 →L[ℝ] ℝ) (v : Space 3) :
    linearWidth l (centeredBody v) = |l v| := by
  dsimp [linearWidth]
  rw [centeredBody_carrier, Set.image_image]
  have hf : (fun t : ℝ => l (t • v)) = fun t => l v * t := by
    funext t
    simp only [Function.comp_apply, map_smul, smul_eq_mul, mul_comm]
  rw [hf, PlanarExtrusion.length_image_mul]
  norm_num

theorem linearWidth_add_smul_centeredBody (l : Space 3 →L[ℝ] ℝ)
    (K : Body 3) (v : Space 3) {r : ℝ} (hr : 0 ≤ r) :
    linearWidth l (K + r • centeredBody v) = linearWidth l K + r * |l v| := by
  rw [linearWidth_add, linearWidth_smul _ _ hr, linearWidth_centeredBody]

def determinantFunctional (v : Plane) : Plane →L[ℝ] ℝ :=
  (PlanarExtrusion.determinantMap v).toContinuousLinearMap

@[simp] theorem determinantFunctional_apply (v w : Plane) :
    determinantFunctional v w = v.1 * w.2 - v.2 * w.1 := rfl

theorem map_centered_to_plane (π : Space 3 →L[ℝ] Plane) (v : Space 3) :
    mapBody π (centeredBody v) = PlanarCorner.segmentBody (π v) := by
  apply ConvexBody.ext
  rw [coe_mapBody, centeredBody_carrier, ← centeredSegment_eq_image,
    image_centeredSegment, centeredSegment_eq_planar]
  rfl

theorem planarArea_add_segment (K : ConvexBody Plane) (v : Plane)
    {r : ℝ} (hr : 0 ≤ r) :
    volume.real (↑(K + r • PlanarCorner.segmentBody v) : Set Plane) =
      volume.real (K : Set Plane) + r * linearWidth (determinantFunctional v) K := by
  rw [PlanarMixedForm.area_add volume PlanarCorner.plane_finrank,
    PlanarCorner.area_smul _ hr, PlanarCorner.area_segmentBody,
    PlanarMixedForm.mixedArea_smul_right volume _ _ hr]
  have h := PlanarCorner.twice_mixedArea_segment K v
  change 2 * PlanarMixedForm.mixedArea volume K (PlanarCorner.segmentBody v) =
    linearWidth (determinantFunctional v) K at h
  have hscaled := congrArg (fun x : ℝ => r * x) h
  nlinarith

def projectionArea (π : Space 3 →L[ℝ] Plane) (K : Body 3) : ℝ :=
  volume.real (mapBody π K : Set Plane)

theorem projectionArea_add_segment (π : Space 3 →L[ℝ] Plane) (K : Body 3) (v : Space 3)
    {r : ℝ} (hr : 0 ≤ r) :
    projectionArea π (K + r • centeredBody v) = projectionArea π K +
      r * linearWidth ((determinantFunctional (π v)).comp π) K := by
  rw [projectionArea, mapBody_add, mapBody_smul, map_centered_to_plane,
    planarArea_add_segment _ _ hr, linearWidth_map]
  rfl

def referenceDirection (i : Fin 5) : Space 3 :=
  ![axis 0, axis 1, axis 2, ReferenceCalibration.sDirection, ReferenceCalibration.iDirection] i

def referenceProjection (i : Fin 5) : Space 3 →L[ℝ] Plane :=
  ![coordinateProjection 0, coordinateProjection 1, coordinateProjection 2, projectionS, projectionI] i

def referenceBody (i : Fin 5) : Body 3 := centeredBody (referenceDirection i)

theorem reference_extrusion (K : Body 3) (i : Fin 5) :
    bodyVolume (K + referenceBody i) - bodyVolume K = projectionArea (referenceProjection i) K := by
  fin_cases i
  · exact bodyExtrusion_axis K 0
  · exact bodyExtrusion_axis K 1
  · exact bodyExtrusion_axis K 2
  · exact extrusionS K
  · exact extrusionI K

theorem volume_add_reference (K : Body 3) (i : Fin 5) {r : ℝ} (hr : 0 ≤ r) :
    bodyVolume (K + r • referenceBody i) =
      bodyVolume K + r * projectionArea (referenceProjection i) K := by
  have h := bodyVolume_add_smul_segment K (-(1 / 2 : ℝ) • referenceDirection i)
    ((1 / 2 : ℝ) • referenceDirection i) hr
  change bodyVolume (K + r • referenceBody i) =
    bodyVolume K + r * (bodyVolume (K + referenceBody i) - bodyVolume K) at h
  rw [reference_extrusion] at h
  exact h

def referencePairFunctional (i j : Fin 5) : Space 3 →L[ℝ] ℝ :=
  (determinantFunctional (referenceProjection j (referenceDirection i))).comp (referenceProjection j)

def withReferences (K : Body 3) (u : Fin 5 → ℝ) : Body 3 :=
  K + u 0 • referenceBody 0 + u 1 • referenceBody 1 + u 2 • referenceBody 2 +
    u 3 • referenceBody 3 + u 4 • referenceBody 4

def referenceExpansion (K : Body 3) (u : Fin 5 → ℝ) : ℝ :=
  bodyVolume K +
    u 0 * projectionArea (referenceProjection 0) K +
    u 1 * projectionArea (referenceProjection 1) K +
    u 2 * projectionArea (referenceProjection 2) K +
    u 3 * projectionArea (referenceProjection 3) K +
    u 4 * projectionArea (referenceProjection 4) K +
    u 0 * u 1 * linearWidth (referencePairFunctional 0 1) K +
    u 0 * u 2 * linearWidth (referencePairFunctional 0 2) K +
    u 0 * u 3 * linearWidth (referencePairFunctional 0 3) K +
    u 0 * u 4 * linearWidth (referencePairFunctional 0 4) K +
    u 1 * u 2 * linearWidth (referencePairFunctional 1 2) K +
    u 1 * u 3 * linearWidth (referencePairFunctional 1 3) K +
    u 1 * u 4 * linearWidth (referencePairFunctional 1 4) K +
    u 2 * u 3 * linearWidth (referencePairFunctional 2 3) K +
    u 2 * u 4 * linearWidth (referencePairFunctional 2 4) K +
    u 3 * u 4 * linearWidth (referencePairFunctional 3 4) K +
    referenceCubic (u 0) (u 1) (u 2) (u 3) (u 4)

/-- Every repeated reference variable vanishes because extrusion is affine;
the ten cubic coefficients are the literal absolute determinants. -/
theorem volume_withReferences (K : Body 3) (u : Fin 5 → ℝ) (hu : ∀ i, 0 ≤ u i) :
    bodyVolume (withReferences K u) = referenceExpansion K u := by
  simp only [withReferences, volume_add_reference _ _ (hu _)]
  simp only [referenceBody, projectionArea_add_segment _ _ _ (hu _),
    linearWidth_add_smul_centeredBody _ _ _ (hu _)]
  norm_num [referenceExpansion, referencePairFunctional, referenceCubic,
    referenceDirection, referenceProjection, determinantFunctional_apply,
    projectionS_apply, projectionI_apply, coordinateProjection_apply,
    ReferenceCalibration.sDirection, ReferenceCalibration.iDirection, axis,
    Pi.single_apply] <;> ring

end MixedVolume.ReferenceExpansion

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ReferenceExpansion.lean -/

/- BEGIN SOURCE: MixedVolume/ParallelSeries.lean -/
section


/-! Minkowski addition of nonnegative parallel segment series.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ParallelSeries

open VolumePolynomials Set
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def weightedChoice (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (s t : Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  classical
  by_cases h : a + b = 0
  · exact ⟨0, by constructor <;> norm_num⟩
  · have hp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    refine ⟨(a * (s : ℝ) + b * (t : ℝ)) / (a + b), ?_, ?_⟩
    · apply (le_div_iff₀ hp).mpr
      nlinarith [mul_nonneg ha (sub_nonneg.mpr s.property.1),
        mul_nonneg hb (sub_nonneg.mpr t.property.1)]
    · apply (div_le_iff₀ hp).mpr
      nlinarith [mul_nonneg ha (sub_nonneg.mpr s.property.2),
        mul_nonneg hb (sub_nonneg.mpr t.property.2)]

theorem weightedChoice_identity (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (s t : Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    (weightedChoice a b ha hb s t : ℝ) * (a + b) =
      (s : ℝ) * a + (t : ℝ) * b := by
  classical
  unfold weightedChoice
  split
  · rename_i h
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · rename_i h
    dsimp
    rw [div_mul_cancel₀ _ h]
    ring

theorem segmentSeries_add (g : ℕ → E) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (has : Summable fun n => ‖a n • g n‖)
    (hbs : Summable fun n => ‖b n • g n‖)
    (habs : Summable fun n => ‖(a n + b n) • g n‖) :
    segmentSeries (fun n => (a n + b n) • g n) =
      segmentSeries (fun n => a n • g n) + segmentSeries (fun n => b n • g n) := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    refine Set.mem_add.mpr ⟨seriesPoint (fun n => a n • g n) t, ⟨t, rfl⟩,
      seriesPoint (fun n => b n • g n) t, ⟨t, rfl⟩, ?_⟩
    rw [seriesPoint, seriesPoint, seriesPoint,
      ← Summable.tsum_add (series_summable _ has t) (series_summable _ hbs t)]
    apply tsum_congr
    intro n
    simp only [smul_add, add_smul]
  · rintro x ⟨y, ⟨s, rfl⟩, z, ⟨t, rfl⟩, rfl⟩
    let c : SegmentChoice := fun n => weightedChoice (a n) (b n) (ha n) (hb n) (s n) (t n)
    refine ⟨c, ?_⟩
    change seriesPoint (fun n => (a n + b n) • g n) c =
      seriesPoint (fun n => a n • g n) s + seriesPoint (fun n => b n • g n) t
    rw [seriesPoint, seriesPoint, seriesPoint,
      ← Summable.tsum_add (series_summable _ has s) (series_summable _ hbs t)]
    apply tsum_congr
    intro n
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1
    exact weightedChoice_identity (a n) (b n) (ha n) (hb n) (s n) (t n)

theorem segmentSeries_smul (u : ℕ → E) (hu : Summable fun n => ‖u n‖) (r : ℝ) :
    segmentSeries (fun n => r • u n) = r • segmentSeries u := by
  let L : E →L[ℝ] E := r • ContinuousLinearMap.id ℝ E
  have h := VolumePolynomials.image_segmentSeries L u hu
  change (fun x : E => r • x) '' segmentSeries u = segmentSeries (fun n => r • u n) at h
  simpa only [← Set.image_smul] using h.symm

theorem summable_weighted_of_bounded (g : ℕ → E) (hg : Summable fun n => ‖g n‖)
    (a : ℕ → ℝ) (M : ℝ) (hM : ∀ n, |a n| ≤ M) :
    Summable fun n => ‖a n • g n‖ := by
  apply (hg.mul_left M).of_norm_bounded
  intro n
  rw [norm_norm, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _)

end MixedVolume.ParallelSeries

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ParallelSeries.lean -/

/- BEGIN SOURCE: MixedVolume/ScalarCombination.lean -/
section


/-! Exact moment formulae for all nonnegative combinations of the three
canonical bodies.  Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ScalarCombination

open VolumePolynomials VolumePolynomials.Holonomy ScalarPolynomial ScalarGeometry
open ProjectedForcing ReferenceExpansion Set MeasureTheory
open scoped Pointwise

def combination (b : Parameter → ℝ) : ConvexBody Holonomy.Plane :=
  b 0 • canonicalState 0 + b 1 • canonicalState 1 + b 2 • canonicalState 2

theorem canonical_height (i : Parameter) :
    PlanarCorner.height (canonicalState i) = rat (heightRat i) := by
  have h := body_height (rate i : ℝ) (rate_pos i).le (rate_le_one i)
  fin_cases i <;> simpa [canonicalState, heightRat, rate, rat] using h

theorem canonical_width (i : Parameter) :
    PlanarCorner.width (canonicalState i) = rat (widthRat i) := by
  have h := body_width (rate i : ℝ) (rate_pos i).le (rate_le_one i)
  fin_cases i <;> simpa [canonicalState, widthRat, heightRat, rate, rat] using h

theorem canonical_area (i : Parameter) :
    volume.real (canonicalState i : Set Holonomy.Plane) = rat (areaRat i) := by
  have h := body_area (rate i : ℝ) (rate_pos i).le (rate_le_one i)
  fin_cases i <;> simpa [canonicalState, areaRat, widthRat, heightRat, rate, rat] using h

theorem canonical_mixed (i j : Parameter) :
    PlanarMixedForm.mixedArea volume (canonicalState i) (canonicalState j) =
      rat (mixedRat i j) / 2 := by
  have h := mixed_body (rate i : ℝ) (rate j : ℝ)
    (rate_pos i).le (rate_le_one i) (rate_pos j).le (rate_le_one j)
  have hm : 2 * PlanarMixedForm.mixedArea volume (canonicalState i) (canonicalState j) =
      rat (mixedRat i j) := by
    fin_cases i <;> fin_cases j <;>
      simpa [canonicalState, mixedRat, widthRat, heightRat, rate, rat] using h
  linarith

theorem combination_height (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) :
    PlanarCorner.height (combination b) = height b := by
  simp only [combination, PlanarCorner.height_add, PlanarCorner.height_smul _ (hb _), canonical_height]
  dsimp [height]
  ring

theorem combination_width (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) :
    PlanarCorner.width (combination b) = width b := by
  simp only [combination, PlanarCorner.width_add, PlanarCorner.width_smul _ (hb _), canonical_width]
  dsimp [width]
  ring

theorem combination_area (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) :
    volume.real (combination b : Set Holonomy.Plane) = quadratic b := by
  simp only [combination, PlanarMixedForm.area_add volume PlanarCorner.plane_finrank,
    PlanarMixedForm.mixedArea_add_left,
    PlanarMixedForm.mixedArea_smul_left volume _ _ (hb _),
    PlanarMixedForm.mixedArea_smul_right volume _ _ (hb _),
    PlanarCorner.area_smul _ (hb _), canonical_area, canonical_mixed]
  dsimp [quadratic]
  ring

theorem combination_add (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    combination (fun i => b i + c i) = combination b + combination c := by
  simp only [combination, body_add_smul _ (hb _) (hc _)]
  ac_rfl

theorem combination_smul (r : ℝ) (b : Parameter → ℝ) :
    combination (fun i => r * b i) = r • combination b := by
  simp only [combination, smul_add, smul_smul]

theorem transition_combination_area (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) :
    volume.real (mapBody transition (combination b) : Set Holonomy.Plane) = quadratic b / 32 := by
  rw [area_transition, combination_area b hb]
  ring

theorem transition_canonical_height (i : Parameter) :
    PlanarCorner.height (mapBody transition (canonicalState i)) = rat (heightRat i) / 4 := by
  have h := congrArg PlanarCorner.height
    (body_recurrence (rate i : ℝ) (rate_pos i).le (rate_le_one i))
  change PlanarCorner.height (canonicalState i) =
    PlanarCorner.height (PlanarCorner.unitY + (rate i : ℝ) • mapBody transition (canonicalState i)) at h
  rw [PlanarCorner.height_add, PlanarCorner.height_unitY,
    PlanarCorner.height_smul _ (rate_pos i).le, canonical_height] at h
  fin_cases i <;> norm_num [heightRat, rate, rat] at h ⊢ <;> linarith

theorem transition_canonical_width (i : Parameter) :
    PlanarCorner.width (mapBody transition (canonicalState i)) =
      rat (1 / rate i) * rat (widthRat i) := by
  have h := scaled_transition_width (rate i : ℝ) (rate_pos i).le (rate_le_one i)
  change PlanarCorner.width ((rate i : ℝ) • mapBody transition (canonicalState i)) =
    PlanarCorner.width (canonicalState i) at h
  rw [PlanarCorner.width_smul _ (rate_pos i).le, canonical_width] at h
  fin_cases i <;> norm_num [widthRat, heightRat, rate, rat] at h ⊢ <;> linarith

theorem transition_combination_height (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) :
    PlanarCorner.height (mapBody transition (combination b)) = height b / 4 := by
  simp only [combination, mapBody_add, mapBody_smul, PlanarCorner.height_add,
    PlanarCorner.height_smul _ (hb _), transition_canonical_height]
  dsimp [height]
  ring

theorem transition_combination_width (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) :
    PlanarCorner.width (mapBody transition (combination b)) = width (divideRates b) := by
  simp only [combination, mapBody_add, mapBody_smul, PlanarCorner.width_add,
    PlanarCorner.width_smul _ (hb _), transition_canonical_width]
  dsimp [width, divideRates]
  ring

theorem divideRates_nonneg (c : Parameter → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∀ i, 0 ≤ divideRates c i := by
  intro i
  have h : (0 : ℝ) ≤ rat (1 / rate i) := by fin_cases i <;> norm_num [rat, rate]
  exact mul_nonneg h (hc i)

theorem combination_recurrence (c : Parameter → ℝ) (hc : ∀ i, 0 ≤ c i) :
    combination (divideRates c) =
      componentSum (divideRates c) • PlanarCorner.unitY + mapBody transition (combination c) := by
  have hi (i : Parameter) : divideRates c i • canonicalState i =
      divideRates c i • PlanarCorner.unitY + c i • mapBody transition (canonicalState i) := by
    have h := body_recurrence (rate i : ℝ) (rate_pos i).le (rate_le_one i)
    change canonicalState i = PlanarCorner.unitY + (rate i : ℝ) • mapBody transition (canonicalState i) at h
    conv_lhs => rw [h]
    rw [smul_add, smul_smul]
    have hcoeff : divideRates c i * (rate i : ℝ) = c i := by
      fin_cases i <;> norm_num [divideRates, rat, rate] <;> ring
    rw [hcoeff]
  have hd := divideRates_nonneg c hc
  simp only [combination, hi, mapBody_add, mapBody_smul, componentSum]
  rw [body_add_smul _ (add_nonneg (hd 0) (hd 1)) (hd 2), body_add_smul _ (hd 0) (hd 1)]
  ac_rfl

def planePair (B C : ConvexBody Holonomy.Plane) : Body 3 :=
  mapBody embedXZ B + mapBody embedXY C

theorem volume_planePair (B C : ConvexBody Holonomy.Plane) :
    bodyVolume (planePair B C) =
      volume.real (B : Set Holonomy.Plane) * PlanarCorner.height C +
        PlanarCorner.height B * volume.real (C : Set Holonomy.Plane) := by
  let g : Space 3 ≃L[ℝ] (ℝ × Holonomy.Plane) := (coordinateExtract 2).toContinuousLinearEquiv
  have hg : MeasurePreserving g volume volume := coordinateExtract_measurePreserving 2
  have heX : g.toContinuousLinearMap.comp embedXZ = PlanarInteraction.embedXZ := by
    ext p <;> simp [g, coordinateExtract_apply, embedXZ, PlanarInteraction.embedXZ]
  have heY : g.toContinuousLinearMap.comp embedXY = PlanarInteraction.embedXY := by
    ext p <;> simp [g, coordinateExtract_apply, embedXY, PlanarInteraction.embedXY]
  have h := PlanarInteraction.realVolume_image_equiv g hg (planePair B C : Set (Space 3))
  change volume.real (mapBody g.toContinuousLinearMap (planePair B C) : Set (ℝ × Holonomy.Plane)) =
    bodyVolume (planePair B C) at h
  rw [planePair, mapBody_add, mapBody_comp, mapBody_comp, heX, heY, add_comm,
    PlanarInteraction.volume_XY_XZ] at h
  change bodyVolume (mapBody embedXZ B + mapBody embedXY C) = _
  rw [← h]
  ring

def baseBody (b c : Parameter → ℝ) : Body 3 :=
  planePair (combination b) (mapBody transition (combination c))

theorem baseBody_volume (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    bodyVolume (baseBody b c) =
      quadratic b * height c / 4 + quadratic c * height b / 32 := by
  rw [baseBody, volume_planePair, combination_area b hb, transition_combination_height c hc,
    combination_height b hb, transition_combination_area c hc]
  ring

end MixedVolume.ScalarCombination

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ScalarCombination.lean -/

/- BEGIN SOURCE: MixedVolume/CanonicalProjections.lean -/
section


/-! All five projected areas in the complete rational cubic.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.CanonicalProjections

open VolumePolynomials VolumePolynomials.Holonomy ScalarPolynomial ScalarGeometry
open ProjectedForcing ReferenceExpansion ScalarCombination Set MeasureTheory
open scoped Pointwise

def rankOne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : E →L[ℝ] ℝ) (v : Holonomy.Plane) : E →L[ℝ] Holonomy.Plane :=
  (LinearMap.toSpanSingleton ℝ Holonomy.Plane v).toContinuousLinearMap.comp l

@[simp] theorem rankOne_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : E →L[ℝ] ℝ) (v : Holonomy.Plane) (x : E) : rankOne l v x = l x • v := rfl

theorem rankOne_series {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (l : E →L[ℝ] ℝ) (v : Holonomy.Plane) (u : ℕ → E) (hu : Summable fun n => ‖u n‖) :
    mapBody (rankOne l v) (segmentSeriesBody u hu) =
      linearWidth l (segmentSeriesBody u hu) • PlanarCorner.segmentBody v := by
  let s : ℝ := ∑' n, |l (u n)|
  have hs : 0 ≤ s := tsum_nonneg fun n => abs_nonneg _
  have hw : linearWidth l (segmentSeriesBody u hu) = s :=
    SeriesProjection.length_image_segmentSeries l u hu
  rw [hw]
  apply ConvexBody.ext
  change (fun x => l x • v) '' segmentSeries u = s • PlanarExtrusion.centeredSegment v
  have hi : Icc (-(1 / 2 : ℝ) * s) ((1 / 2 : ℝ) * s) =
      (fun t : ℝ => s * t) '' Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    rw [image_mul_left_Icc hs (by norm_num)]
    congr 1 <;> ring
  calc
    _ = (fun t : ℝ => t • v) '' (l '' segmentSeries u) := (Set.image_image _ _ _).symm
    _ = (fun t : ℝ => t • v) '' Icc (-(1 / 2 : ℝ) * s) ((1 / 2 : ℝ) * s) := by
      rw [SeriesProjection.image_segmentSeries l u hu]
    _ = _ := by
      rw [hi, Set.image_image]
      simp only [PlanarExtrusion.centeredSegment, ← Set.image_smul, Set.image_image]
      congr 1
      funext t
      simp [smul_smul, mul_comm]

theorem canonical_rankOne (l : Holonomy.Plane →L[ℝ] ℝ) (v : Holonomy.Plane) (i : Parameter) :
    mapBody (rankOne l v) (canonicalState i) =
      linearWidth l (canonicalState i) • PlanarCorner.segmentBody v :=
  rankOne_series l v (generator (rate i : ℝ))
    (generator_summable _ (rate_pos i).le (rate_le_one i))

theorem rankOne_combination (l : Holonomy.Plane →L[ℝ] ℝ) (v : Holonomy.Plane)
    (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) :
    mapBody (rankOne l v) (combination b) =
      linearWidth l (combination b) • PlanarCorner.segmentBody v := by
  have hw (i : Parameter) : 0 ≤ b i * linearWidth l (canonicalState i) :=
    mul_nonneg (hb i) measureReal_nonneg
  simp only [combination, mapBody_add, mapBody_smul, canonical_rankOne,
    linearWidth_add, linearWidth_smul _ _ (hb _), smul_smul]
  rw [body_add_smul _ (add_nonneg (hw 0) (hw 1)) (hw 2), body_add_smul _ (hw 0) (hw 1)]

theorem rankOne_map_combination (l : Holonomy.Plane →L[ℝ] ℝ) (v : Holonomy.Plane)
    (f : Holonomy.Plane →L[ℝ] Holonomy.Plane) (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) :
    mapBody (rankOne l v) (mapBody f (combination b)) =
      linearWidth l (mapBody f (combination b)) • PlanarCorner.segmentBody v := by
  rw [mapBody_comp, linearWidth_map]
  have he : (rankOne l v).comp f = rankOne (l.comp f) v := rfl
  rw [he, rankOne_combination _ _ b hb]

theorem projection_zero_state : (coordinateProjection 0).comp embedXZ =
    rankOne (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 1) := by
  ext p <;> simp [coordinateProjection_apply, embedXZ, rankOne]

theorem projection_zero_image : (coordinateProjection 0).comp embedXY =
    rankOne (ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) := by
  ext p <;> simp [coordinateProjection_apply, embedXY, rankOne]

theorem projection_one_state : (coordinateProjection 1).comp embedXZ = ContinuousLinearMap.id ℝ Holonomy.Plane := by
  ext p <;> simp [embedXZ]

theorem projection_one_image : (coordinateProjection 1).comp embedXY =
    rankOne (ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 0) := by
  ext p <;> simp [coordinateProjection_apply, embedXY, rankOne]

theorem projection_two_state : (coordinateProjection 2).comp embedXZ =
    rankOne (ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 0) := by
  ext p <;> simp [coordinateProjection_apply, embedXZ, rankOne]

theorem projection_two_image : (coordinateProjection 2).comp embedXY = ContinuousLinearMap.id ℝ Holonomy.Plane := by
  ext p <;> simp [embedXY]

theorem projected_zero (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    mapBody (coordinateProjection 0) (baseBody b c) =
      height b • PlanarCorner.unitY + (height c / 4) • PlanarCorner.unitX := by
  rw [baseBody, planePair, mapBody_add, mapBody_comp, mapBody_comp,
    projection_zero_state, projection_zero_image, rankOne_combination _ _ b hb,
    rankOne_map_combination _ _ _ c hc]
  change PlanarCorner.height (combination b) • PlanarCorner.unitY +
    PlanarCorner.height (mapBody transition (combination c)) • PlanarCorner.unitX = _
  rw [combination_height b hb, transition_combination_height c hc]

theorem projected_one (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    mapBody (coordinateProjection 1) (baseBody b c) =
      combination b + width (divideRates c) • PlanarCorner.unitX := by
  rw [baseBody, planePair, mapBody_add, mapBody_comp, mapBody_comp,
    projection_one_state, projection_one_image, mapBody_id, rankOne_map_combination _ _ _ c hc]
  change combination b + PlanarCorner.width (mapBody transition (combination c)) • PlanarCorner.unitX = _
  rw [transition_combination_width c hc]

theorem projected_two (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    mapBody (coordinateProjection 2) (baseBody b c) =
      width b • PlanarCorner.unitX + mapBody transition (combination c) := by
  rw [baseBody, planePair, mapBody_add, mapBody_comp, mapBody_comp,
    projection_two_state, projection_two_image, rankOne_combination _ _ b hb, mapBody_id]
  change PlanarCorner.width (combination b) • PlanarCorner.unitX +
    mapBody transition (combination c) = _
  rw [combination_width b hb]

theorem projected_s (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    mapBody projectionS (baseBody b c) =
      mapBody transition (combination (fun i => 8 * b i + c i)) := by
  rw [baseBody, planePair, mapBody_add, mapBody_comp, mapBody_comp,
    projectionS_embedXZ, projectionS_embedXY, mapBody_smul_map, mapBody_id]
  rw [combination_add _ _ (fun i => mul_nonneg (by norm_num) (hb i)) hc,
    combination_smul, mapBody_add, mapBody_smul]

theorem projected_i (b c : Parameter → ℝ) :
    mapBody projectionI (baseBody b c) = combination b + mapBody transition (combination c) := by
  rw [baseBody, planePair, mapBody_add, mapBody_comp, mapBody_comp,
    projectionI_embedXZ, projectionI_embedXY, mapBody_id, mapBody_id]

theorem height_nonneg (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) : 0 ≤ height b := by
  rw [← combination_height b hb]
  exact measureReal_nonneg

theorem width_nonneg (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) : 0 ≤ width b := by
  rw [← combination_width b hb]
  exact measureReal_nonneg

theorem area_zero_projection (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    projectionArea (coordinateProjection 0) (baseBody b c) = height b * height c / 4 := by
  rw [projectionArea, projected_zero b c hb hc, add_comm,
    PlanarCorner.area_add_scaled_unitY _ (height_nonneg b hb),
    PlanarCorner.area_smul _ (div_nonneg (height_nonneg c hc) (by norm_num)),
    PlanarCorner.unitX, PlanarCorner.area_segmentBody,
    PlanarCorner.width_smul _ (div_nonneg (height_nonneg c hc) (by norm_num))]
  change (height c / 4) ^ 2 * 0 + height b * (height c / 4 * PlanarCorner.width PlanarCorner.unitX) = _
  rw [PlanarCorner.width_unitX]
  ring

theorem area_one_projection (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    projectionArea (coordinateProjection 1) (baseBody b c) =
      quadratic b + width (divideRates c) * height b := by
  rw [projectionArea, projected_one b c hb hc,
    PlanarCorner.area_add_scaled_unitX _ (width_nonneg _ (divideRates_nonneg c hc)),
    combination_area b hb, combination_height b hb]

theorem area_two_projection (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    projectionArea (coordinateProjection 2) (baseBody b c) =
      quadratic c / 32 + width b * height c / 4 := by
  rw [projectionArea, projected_two b c hb hc, add_comm,
    PlanarCorner.area_add_scaled_unitX _ (width_nonneg b hb),
    transition_combination_area c hc, transition_combination_height c hc]
  ring

theorem area_s_projection (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    projectionArea projectionS (baseBody b c) = quadratic (fun i => 8 * b i + c i) / 32 := by
  rw [projectionArea, projected_s b c hb hc,
    transition_combination_area _ (fun i => add_nonneg (mul_nonneg (by norm_num) (hb i)) (hc i))]

theorem area_i_projection (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    projectionArea projectionI (baseBody b c) =
      quadratic (fun i => b i + divideRates c i) -
        componentSum (divideRates c) * width (fun i => b i + divideRates c i) := by
  let X := combination b + mapBody transition (combination c)
  let e := componentSum (divideRates c)
  have he : 0 ≤ e := by
    have hd := divideRates_nonneg c hc
    exact add_nonneg (add_nonneg (hd 0) (hd 1)) (hd 2)
  have hY : combination (fun i => b i + divideRates c i) = X + e • PlanarCorner.unitY := by
    rw [combination_add b _ hb (divideRates_nonneg c hc), combination_recurrence c hc]
    dsimp [X, e]
    ac_rfl
  have harea := congrArg (fun K : ConvexBody Holonomy.Plane => volume.real (K : Set Holonomy.Plane)) hY
  rw [combination_area _ (fun i => add_nonneg (hb i) (divideRates_nonneg c hc i)),
    PlanarCorner.area_add_scaled_unitY X he] at harea
  have hwidth : PlanarCorner.width X = width (fun i => b i + divideRates c i) := by
    dsimp [X]
    rw [PlanarCorner.width_add, combination_width b hb, transition_combination_width c hc,
      width_add]
  rw [hwidth] at harea
  rw [projectionArea, projected_i]
  change volume.real (X : Set Holonomy.Plane) = _
  linarith

end MixedVolume.CanonicalProjections

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/CanonicalProjections.lean -/

/- BEGIN SOURCE: MixedVolume/ReferenceWidths.lean -/
section


/-! The ten one-dimensional cross-projection lengths in the full cubic.
Every absolute value is justified on the complete infinite generator family.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ReferenceWidths

open VolumePolynomials VolumePolynomials.Holonomy ScalarPolynomial ScalarGeometry
open ProjectedForcing ReferenceExpansion ScalarCombination Set MeasureTheory
open scoped Pointwise

theorem generator_coordinates (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ (generator r n).1 ∧ (generator r n).1 ≤ (generator r n).2 := by
  have hp : (r / 8) ^ n ≤ (r / 4) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  have hn : 0 ≤ (r / 8) ^ n := by positivity
  constructor <;> dsimp [generator] <;> linarith

theorem sum_generator (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (∑' n, generator r n) =
      (1 / (1 - r / 4) - 1 / (1 - r / 8), 1 / (1 - r / 4)) := by
  have hu : Summable (generator r) := (generator_summable r hr₀ hr₁).of_norm
  ext
  · change (ContinuousLinearMap.fst ℝ ℝ ℝ) (∑' n, generator r n) = _
    rw [ContinuousLinearMap.map_tsum _ hu]
    change (∑' n, ((r / 4) ^ n - (r / 8) ^ n)) = _
    rw [Summable.tsum_sub
      (summable_geometric_of_lt_one (by positivity : 0 ≤ r / 4) (by linarith))
      (summable_geometric_of_lt_one (by positivity : 0 ≤ r / 8) (by linarith)),
      tsum_geometric_of_lt_one (by positivity) (by linarith),
      tsum_geometric_of_lt_one (by positivity) (by linarith)]
    simp only [one_div]
  · change (ContinuousLinearMap.snd ℝ ℝ ℝ) (∑' n, generator r n) = _
    rw [ContinuousLinearMap.map_tsum _ hu]
    change (∑' n, (r / 4) ^ n) = _
    rw [tsum_geometric_of_lt_one (by positivity) (by linarith)]
    simp only [one_div]

theorem canonical_sum_generator (i : Parameter) :
    (∑' n, generator (rate i : ℝ) n) = (rat (widthRat i), rat (heightRat i)) := by
  have h := sum_generator (rate i : ℝ) (rate_pos i).le (rate_le_one i)
  fin_cases i <;> simpa [rat, widthRat, heightRat, rate] using h

theorem canonical_width_from_sign (l m : Holonomy.Plane →L[ℝ] ℝ) (i : Parameter)
    (hm : ∀ n, |l (generator (rate i : ℝ) n)| = m (generator (rate i : ℝ) n)) :
    ReferenceExpansion.linearWidth l (canonicalState i) = m (rat (widthRat i), rat (heightRat i)) := by
  change volume.real (l '' segmentSeries (generator (rate i : ℝ))) = _
  rw [SeriesProjection.length_image_segmentSeries _ _
    (generator_summable _ (rate_pos i).le (rate_le_one i))]
  simp_rw [hm]
  rw [← m.map_tsum (generator_summable _ (rate_pos i).le (rate_le_one i)).of_norm,
    canonical_sum_generator]

def orientation (i : Fin 5) : ℝ := if i = 0 then 1 else -1

theorem orientation_abs (i : Fin 5) : |orientation i| = 1 := by
  simp only [orientation]
  split <;> norm_num

theorem abs_eq_oriented (ε x : ℝ) (hε : |ε| = 1) (h : 0 ≤ ε * x) : |x| = ε * x := by
  have he := abs_of_nonneg h
  rw [abs_mul, hε, one_mul] at he
  exact he

theorem pair_state_sign (i j : Fin 5) (hij : i < j) (p : Holonomy.Plane)
    (hx : 0 ≤ p.1) (hxy : p.1 ≤ p.2) :
    0 ≤ orientation i * referencePairFunctional i j (embedXZ p) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [orientation, referencePairFunctional, referenceDirection, referenceProjection,
      determinantFunctional_apply, embedXZ, projectionS_apply, projectionI_apply,
      coordinateProjection_apply, ReferenceCalibration.sDirection, ReferenceCalibration.iDirection,
      axis, Pi.single_apply] at * <;> nlinarith

theorem pair_image_sign (i j : Fin 5) (hij : i < j) (p : Holonomy.Plane)
    (hx : 0 ≤ p.1) (hxy : p.1 ≤ p.2) :
    0 ≤ orientation i * referencePairFunctional i j (embedXY (transition p)) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [orientation, referencePairFunctional, referenceDirection, referenceProjection,
      determinantFunctional_apply, embedXY, transition_apply, projectionS_apply, projectionI_apply,
      coordinateProjection_apply, ReferenceCalibration.sDirection, ReferenceCalibration.iDirection,
      axis, Pi.single_apply] at * <;> nlinarith

theorem canonical_pair_state_width (i j : Fin 5) (hij : i < j) (k : Parameter) :
    ReferenceExpansion.linearWidth ((referencePairFunctional i j).comp embedXZ) (canonicalState k) =
      orientation i * referencePairFunctional i j (embedXZ (rat (widthRat k), rat (heightRat k))) := by
  apply canonical_width_from_sign _ (orientation i • ((referencePairFunctional i j).comp embedXZ)) k
  intro n
  have h := generator_coordinates (rate k : ℝ) (rate_pos k).le n
  exact abs_eq_oriented _ _ (orientation_abs i) (pair_state_sign i j hij _ h.1 h.2)

theorem canonical_pair_image_width (i j : Fin 5) (hij : i < j) (k : Parameter) :
    ReferenceExpansion.linearWidth (((referencePairFunctional i j).comp embedXY).comp transition) (canonicalState k) =
      orientation i * referencePairFunctional i j
        (embedXY (transition (rat (widthRat k), rat (heightRat k)))) := by
  apply canonical_width_from_sign _
    (orientation i • (((referencePairFunctional i j).comp embedXY).comp transition)) k
  intro n
  have h := generator_coordinates (rate k : ℝ) (rate_pos k).le n
  exact abs_eq_oriented _ _ (orientation_abs i) (pair_image_sign i j hij _ h.1 h.2)

def pairWidth (b c : Parameter → ℝ) (i j : Fin 5) : ℝ :=
  ![![0, height b, height c / 4, 2 * height b + height c / 4, height b + height c / 4],
    ![0, 0, width b + width (divideRates c), width b + height b + width (divideRates c),
      width b + width (divideRates c)],
    ![0, 0, 0, 2 * width b + width c / 4, width b + width (divideRates c)],
    ![0, 0, 0, 0, height b - width b + height c / 4 - width (divideRates c)],
    ![0, 0, 0, 0, 0]] i j

theorem baseBody_pair_width (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (i j : Fin 5) (hij : i < j) :
    ReferenceExpansion.linearWidth (referencePairFunctional i j) (baseBody b c) = pairWidth b c i j := by
  rw [baseBody, planePair, linearWidth_add, linearWidth_map, linearWidth_map, linearWidth_map]
  simp only [combination, linearWidth_add, linearWidth_smul _ _ (hb _),
    linearWidth_smul _ _ (hc _), canonical_pair_state_width i j hij,
    canonical_pair_image_width i j hij]
  fin_cases i <;> fin_cases j <;>
    norm_num [pairWidth, orientation, referencePairFunctional, referenceDirection,
      referenceProjection, determinantFunctional_apply, embedXZ, embedXY, transition_apply,
      projectionS_apply, projectionI_apply, coordinateProjection_apply,
      ReferenceCalibration.sDirection, ReferenceCalibration.iDirection,
      axis, Pi.single_apply, width, height, divideRates, rat, widthRat, heightRat, rate] at * <;> ring

end MixedVolume.ReferenceWidths

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ReferenceWidths.lean -/

/- BEGIN SOURCE: MixedVolume/CanonicalFormula.lean -/
section


/-! The complete ordinary coefficient polynomial, proved from genuine volumes.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.CanonicalFormula

open VolumePolynomials VolumePolynomials.Holonomy ScalarPolynomial ScalarGeometry
open ProjectedForcing ReferenceExpansion ScalarCombination CanonicalProjections ReferenceWidths
open Set MeasureTheory
open scoped Pointwise BigOperators

theorem complete_canonical_volume (u : Fin 5 → ℝ) (b c : Parameter → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    bodyVolume (withReferences (baseBody b c) u) =
      canonicalFormula (u 0) (u 1) (u 2) (u 3) (u 4) b c := by
  rw [volume_withReferences _ _ hu]
  simp only [referenceExpansion, baseBody_volume b c hb hc, referenceProjection,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, area_zero_projection b c hb hc, area_one_projection b c hb hc,
    area_two_projection b c hb hc, area_s_projection b c hb hc, area_i_projection b c hb hc,
    baseBody_pair_width b c hb hc 0 1 (by decide),
    baseBody_pair_width b c hb hc 0 2 (by decide),
    baseBody_pair_width b c hb hc 0 3 (by decide),
    baseBody_pair_width b c hb hc 0 4 (by decide),
    baseBody_pair_width b c hb hc 1 2 (by decide),
    baseBody_pair_width b c hb hc 1 3 (by decide),
    baseBody_pair_width b c hb hc 1 4 (by decide),
    baseBody_pair_width b c hb hc 2 3 (by decide),
    baseBody_pair_width b c hb hc 2 4 (by decide),
    baseBody_pair_width b c hb hc 3 4 (by decide)]
  norm_num [pairWidth, canonicalFormula, rat, area_s_projection b c hb hc,
    area_i_projection b c hb hc] <;> ring

def tupleWithDeficit (D : ConvexBody Holonomy.Plane) : Label → Body 3 :=
  ![referenceBody 0, referenceBody 1, referenceBody 2, referenceBody 3, referenceBody 4,
    mapBody embedXZ (canonicalState 0), mapBody embedXZ (canonicalState 1),
    mapBody embedXZ (canonicalState 2),
    mapBody embedXY (mapBody transition (canonicalState 0)),
    mapBody embedXY (mapBody transition (canonicalState 1)),
    mapBody embedXY (mapBody transition (canonicalState 2)), mapBody embedXZ D]

theorem weightedSum_tupleWithDeficit (D : ConvexBody Holonomy.Plane) (w : Label → ℝ) :
    weightedSum (tupleWithDeficit D) w =
      withReferences (planePair
        (combination (fun i => w (stateLabel i)) + w deficitLabel • D)
        (mapBody transition (combination (fun i => w (imageLabel i)))))
        (fun i => w (ReferenceNormalization.referenceLabel i)) := by
  simp only [weightedSum, tupleWithDeficit, withReferences, planePair, combination,
    mapBody_add, mapBody_smul, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
    stateLabel, imageLabel, deficitLabel, ReferenceNormalization.referenceLabel,
    add_zero]
  norm_num [Fin.succ]
  let r₀ : Body 3 := w 0 • referenceBody 0
  let r₁ : Body 3 := w 1 • referenceBody 1
  let r₂ : Body 3 := w 2 • referenceBody 2
  let r₃ : Body 3 := w 3 • referenceBody 3
  let r₄ : Body 3 := w 4 • referenceBody 4
  let b₀ : Body 3 := w 5 • mapBody embedXZ (canonicalState 0)
  let b₁ : Body 3 := w 6 • mapBody embedXZ (canonicalState 1)
  let b₂ : Body 3 := w 7 • mapBody embedXZ (canonicalState 2)
  let c₀ : Body 3 := w 8 • mapBody embedXY (mapBody transition (canonicalState 0))
  let c₁ : Body 3 := w 9 • mapBody embedXY (mapBody transition (canonicalState 1))
  let c₂ : Body 3 := w 10 • mapBody embedXY (mapBody transition (canonicalState 2))
  let d : Body 3 := w 11 • mapBody embedXZ D
  change r₀ + (r₁ + (r₂ + (r₃ + (r₄ + (b₀ + (b₁ +
    (b₂ + (c₀ + (c₁ + (c₂ + d)))))))))) =
      b₀ + b₁ + b₂ + d + (c₀ + c₁ + c₂) + r₀ + r₁ + r₂ + r₃ + r₄
  ac_rfl

theorem volume_of_deficit_cancellation (D : ConvexBody Holonomy.Plane) (w : Label → ℝ)
    (b : Parameter → ℝ) (hw : ∀ i, 0 ≤ w i) (hb : ∀ i, 0 ≤ b i)
    (hcancel : combination (fun i => w (stateLabel i)) + w deficitLabel • D = combination b) :
    volumeFunction (tupleWithDeficit D) w =
      canonicalFormula (w 0) (w 1) (w 2) (w 3) (w 4) b
        (fun i => w (imageLabel i)) := by
  rw [volumeFunction, weightedSum_tupleWithDeficit, hcancel]
  exact complete_canonical_volume _ b _ (fun i => hw _) hb (fun i => hw _)

end MixedVolume.CanonicalFormula

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/CanonicalFormula.lean -/

/- BEGIN SOURCE: MixedVolume/ExposedLengths.lean -/
section


/-! Literal lengths of exposed faces.  No support-measure oracle is used.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ExposedLengths

open VolumePolynomials VolumePolynomials.Holonomy ScalarGeometry ProjectedForcing
open Set MeasureTheory
open scoped Pointwise

def exposedBody (l : Holonomy.Plane →L[ℝ] ℝ) (K : ConvexBody Holonomy.Plane) : ConvexBody Holonomy.Plane where
  carrier := l.toExposed (K : Set Holonomy.Plane)
  convex' := (ContinuousLinearMap.toExposed.isExposed (l := l) (A := (K : Set Holonomy.Plane))).convex K.convex
  isCompact' := (ContinuousLinearMap.toExposed.isExposed (l := l) (A := (K : Set Holonomy.Plane))).isCompact K.isCompact
  nonempty' := PolytopeFaces.exposed_nonempty l K.isCompact K.nonempty

def faceHeight (l : Holonomy.Plane →L[ℝ] ℝ) (K : ConvexBody Holonomy.Plane) : ℝ :=
  PlanarCorner.height (exposedBody l K)

theorem faceHeight_nonneg (l : Holonomy.Plane →L[ℝ] ℝ) (K : ConvexBody Holonomy.Plane) :
    0 ≤ faceHeight l K := measureReal_nonneg

theorem exposedBody_add (l : Holonomy.Plane →L[ℝ] ℝ) (K L : ConvexBody Holonomy.Plane) :
    exposedBody l (K + L) = exposedBody l K + exposedBody l L := by
  apply ConvexBody.ext
  exact PolytopeFaces.exposed_add l (K : Set Holonomy.Plane) (L : Set Holonomy.Plane)

theorem exposedBody_smul (l : Holonomy.Plane →L[ℝ] ℝ) (K : ConvexBody Holonomy.Plane)
    {r : ℝ} (hr : 0 < r) : exposedBody l (r • K) = r • exposedBody l K := by
  apply ConvexBody.ext
  exact PolytopeFaces.exposed_smul l (K : Set Holonomy.Plane) hr

theorem exposedBody_point (l : Holonomy.Plane →L[ℝ] ℝ) (p : Holonomy.Plane) :
    exposedBody l (pointBody p) = pointBody p := by
  apply ConvexBody.ext
  exact PolytopeFaces.exposed_singleton l p

theorem exposedBody_translate (l : Holonomy.Plane →L[ℝ] ℝ) (p : Holonomy.Plane) (K : ConvexBody Holonomy.Plane) :
    exposedBody l (translateBody p K) = translateBody p (exposedBody l K) := by
  simp only [translateBody, exposedBody_add, exposedBody_point]

theorem faceHeight_add (l : Holonomy.Plane →L[ℝ] ℝ) (K L : ConvexBody Holonomy.Plane) :
    faceHeight l (K + L) = faceHeight l K + faceHeight l L := by
  simp only [faceHeight, exposedBody_add, PlanarCorner.height_add]

theorem faceHeight_smul (l : Holonomy.Plane →L[ℝ] ℝ) (K : ConvexBody Holonomy.Plane)
    {r : ℝ} (hr : 0 < r) : faceHeight l (r • K) = r * faceHeight l K := by
  simp only [faceHeight, exposedBody_smul l K hr, PlanarCorner.height_smul _ hr.le]

theorem faceHeight_translate (l : Holonomy.Plane →L[ℝ] ℝ) (p : Holonomy.Plane) (K : ConvexBody Holonomy.Plane) :
    faceHeight l (translateBody p K) = faceHeight l K := by
  simp only [faceHeight, exposedBody_translate, PlanarCorner.height_translate]

theorem height_segmentBody (v : Holonomy.Plane) :
    PlanarCorner.height (PlanarCorner.segmentBody v) = |v.2| := by
  change volume.real (Prod.snd '' PlanarExtrusion.centeredSegment v) = |v.2|
  have h := PlanarExtrusion.length_determinant_centeredSegment (1, 0) v
  have hd : PlanarExtrusion.determinant (1, 0) = Prod.snd := by
    funext p
    simp [PlanarExtrusion.determinant]
  rw [hd] at h
  exact h

theorem body_faceHeight (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1) (k : ℕ) :
    faceHeight (tagNormal k) (body r hr₀.le hr₁) = (r / 4) ^ k := by
  obtain ⟨p, hp⟩ := body_exposed_face r hr₀ hr₁ k
  have heq : exposedBody (tagNormal k) (body r hr₀.le hr₁) =
      translateBody p (PlanarCorner.segmentBody (generator r k)) := by
    apply ConvexBody.ext
    change (tagNormal k).toExposed (body r hr₀.le hr₁ : Set Holonomy.Plane) = _
    rw [hp, coe_translateBody]
    change {x | ∃ t : Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      x = p + (t : ℝ) • generator r k} = p +ᵥ PlanarExtrusion.centeredSegment (generator r k)
    rw [← centeredSegment_eq_planar]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(t : ℝ) • generator r k, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  rw [faceHeight, heq, PlanarCorner.height_translate, height_segmentBody]
  exact abs_of_nonneg (pow_nonneg (by positivity) k)

theorem state_faceHeight {a : ScalarPolynomial.Parameter → ℝ}
    {K : ScalarPolynomial.Label → Body 3}
    (hK : ReferenceNormalization.IsTarget a K) (hcal : ReferenceNormalization.Calibrated K)
    (i : ScalarPolynomial.Parameter) (k : ℕ) :
    faceHeight (tagNormal k) (state K i) = ((ScalarPolynomial.rate i : ℝ) / 4) ^ k := by
  obtain ⟨p, hp⟩ := states_forced hK hcal i
  rw [hp, faceHeight_translate]
  exact body_faceHeight _ (rate_pos i) (rate_le_one i) k

end MixedVolume.ExposedLengths

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ExposedLengths.lean -/

/- BEGIN SOURCE: MixedVolume/DeficitForcing.lean -/
section


/-! The arbitrary-body converse of the scalar section.  All hypotheses are
literal realization equations for the complete cubic. Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.DeficitForcing

open VolumePolynomials VolumePolynomials.Holonomy ScalarPolynomial ReferenceNormalization
open ProjectedForcing ExposedLengths ScalarGeometry Set MeasureTheory
open scoped Pointwise

def stateCombination (K : Label → Body 3) (b : Parameter → ℝ) : ConvexBody Holonomy.Plane :=
  b 0 • state K 0 + b 1 • state K 1 + b 2 • state K 2

def stateWeights (b : Parameter → ℝ) (z : ℝ) : Label → ℝ :=
  weight (stateLabel 0) (b 0) + weight (stateLabel 1) (b 1) +
    weight (stateLabel 2) (b 2) + weight deficitLabel z

theorem stateWeights_nonneg {b : Parameter → ℝ} {z : ℝ}
    (hb : ∀ i, 0 ≤ b i) (hz : 0 ≤ z) : ∀ j, 0 ≤ stateWeights b z j := by
  intro j
  exact add_nonneg (add_nonneg (add_nonneg (weight_nonneg _ (hb 0) j)
    (weight_nonneg _ (hb 1) j)) (weight_nonneg _ (hb 2) j)) (weight_nonneg _ hz j)

theorem project_stateWeights (K : Label → Body 3) (b : Parameter → ℝ) (z : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hz : 0 ≤ z) :
    mapBody (coordinateProjection 1) (weightedSum K (stateWeights b z)) =
      stateCombination K b + z • deficit K := by
  have h₀ := weight_nonneg (stateLabel 0) (hb 0)
  have h₁ := weight_nonneg (stateLabel 1) (hb 1)
  have h₂ := weight_nonneg (stateLabel 2) (hb 2)
  have h₃ := weight_nonneg deficitLabel hz
  have h₀₁ : ∀ j, 0 ≤ (weight (stateLabel 0) (b 0) + weight (stateLabel 1) (b 1)) j :=
    fun j => add_nonneg (h₀ j) (h₁ j)
  have h₀₁₂ : ∀ j, 0 ≤ (weight (stateLabel 0) (b 0) + weight (stateLabel 1) (b 1) +
      weight (stateLabel 2) (b 2)) j := fun j => add_nonneg (h₀₁ j) (h₂ j)
  rw [stateWeights, weightedSum_add K _ _ h₀₁₂ h₃,
    weightedSum_add K _ _ h₀₁ h₂, weightedSum_add K _ _ h₀ h₁]
  simp only [weightedSum_weight, mapBody_add, mapBody_smul, stateCombination, state, deficit]

theorem delta_stateWeights (a b : Parameter → ℝ) (z : ℝ) :
    delta a 1 (stateWeights b z) = quadratic (fun i => b i - a i * z) := by
  simp [delta, stateWeights, weight, unitWeight, targetValue, canonicalFormula,
    referenceCubic, quadratic, height, width, componentSum, divideRates,
    stateLabel, imageLabel, deficitLabel, Pi.single_apply, rat] <;> ring

theorem combination_area {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) (b : Parameter → ℝ) (z : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hz : 0 ≤ z) :
    volume.real (↑(stateCombination K b + z • deficit K) : Set Holonomy.Plane) =
      quadratic (fun i => b i - a i * z) := by
  have h := extrusionAxis_eq_delta hK hcal 1 (stateWeights b z) (stateWeights_nonneg hb hz)
  rw [project_stateWeights K b z hb hz] at h
  exact h.trans (delta_stateWeights a b z)

theorem stateCombination_add (K : Label → Body 3) (b c : Parameter → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    stateCombination K (fun i => b i + c i) = stateCombination K b + stateCombination K c := by
  simp only [stateCombination, body_add_smul _ (hb _) (hc _)]
  ac_rfl

theorem stateCombination_faceHeight (K : Label → Body 3) (b : Parameter → ℝ)
    (hb : ∀ i, 0 < b i) (l : Holonomy.Plane →L[ℝ] ℝ) :
    faceHeight l (stateCombination K b) =
      b 0 * faceHeight l (state K 0) + b 1 * faceHeight l (state K 1) +
        b 2 * faceHeight l (state K 2) := by
  simp only [stateCombination, faceHeight_add, faceHeight_smul _ _ (hb _)]

def budget (a : Parameter → ℝ) : ℝ := 1 + |a 0| + |a 1| + |a 2|

theorem budget_pos (a : Parameter → ℝ) : 0 < budget a := by
  dsimp [budget]
  positivity

theorem budget_add_pos (a : Parameter → ℝ) (i : Parameter) : 0 < budget a + a i := by
  have h₀ := neg_abs_le (a 0)
  have h₁ := neg_abs_le (a 1)
  have h₂ := neg_abs_le (a 2)
  have h₀' := abs_nonneg (a 0)
  have h₁' := abs_nonneg (a 1)
  have h₂' := abs_nonneg (a 2)
  fin_cases i <;> dsimp [budget] <;> linarith

theorem quadratic_constant (r : ℝ) :
    quadratic (fun _ : Parameter => r) = r ^ 2 * quadratic (fun _ : Parameter => (1 : ℝ)) := by
  dsimp [quadratic]
  ring

theorem quadratic_ones_pos : 0 < quadratic (fun _ : Parameter => (1 : ℝ)) := by
  norm_num [quadratic, rat, areaRat, mixedRat, widthRat, heightRat, rate]

theorem deficit_sum_forced {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) :
    ∃ q : Holonomy.Plane, stateCombination K (fun i => budget a + a i) + deficit K =
      translateBody q (stateCombination K (fun _ => budget a)) := by
  let r := budget a
  let M := stateCombination K (fun _ => r)
  let L := stateCombination K (fun i => r + a i) + deficit K
  have hr : 0 < r := budget_pos a
  have hb : ∀ i, 0 < r + a i := budget_add_pos a
  have hm : volume.real (M : Set Holonomy.Plane) = quadratic (fun _ : Parameter => r) := by
    simpa only [body_zero_smul, add_zero, mul_zero, sub_zero] using
      combination_area hK hcal (fun _ => r) 0 (fun _ => hr.le) (by norm_num)
  have hl : volume.real (L : Set Holonomy.Plane) = quadratic (fun _ : Parameter => r) := by
    simpa only [one_smul, mul_one, add_sub_cancel_right] using
      combination_area hK hcal (fun i => r + a i) 1 (fun i => (hb i).le) (by norm_num)
  have hsum : M + L = stateCombination K (fun i => 2 * r + a i) + deficit K := by
    dsimp [M, L]
    rw [← add_assoc, ← stateCombination_add K _ _ (fun _ => hr.le) (fun i => (hb i).le)]
    congr 2
    funext i
    ring
  have hsumArea : volume.real (↑(M + L) : Set Holonomy.Plane) = 4 * volume.real (M : Set Holonomy.Plane) := by
    rw [hsum]
    have h := combination_area hK hcal (fun i => 2 * r + a i) 1
      (fun i => by linarith [hb i]) (by norm_num)
    simp only [one_smul, mul_one, add_sub_cancel_right] at h
    rw [h, hm, quadratic_constant (2 * r), quadratic_constant r]
    ring
  obtain ⟨q, hq⟩ := equal_area_translates M.convex M.isCompact L.convex L.isCompact
    (by rw [hm, quadratic_constant]; exact mul_pos (sq_pos_of_pos hr) quadratic_ones_pos)
    (by rw [hl, hm]) hsumArea
  exact ⟨q, ConvexBody.ext (by simpa only [coe_translateBody] using hq)⟩

/-- Necessity uses exposed faces of arbitrary compact convex deficit bodies;
it does not assume that a realization is a zonotope or has countably many edges. -/
theorem calibrated_target_implies_cone {a : Parameter → ℝ} {K : Label → Body 3}
    (hK : IsTarget a K) (hcal : Calibrated K) : cone a := by
  obtain ⟨q, hq⟩ := deficit_sum_forced hK hcal
  intro n
  have hf := congrArg (faceHeight (tagNormal n)) hq
  rw [faceHeight_add, faceHeight_translate,
    stateCombination_faceHeight K _ (budget_add_pos a),
    stateCombination_faceHeight K _ (fun _ => budget_pos a)] at hf
  simp only [state_faceHeight hK hcal, rate] at hf
  norm_num at hf
  have hnonneg := faceHeight_nonneg (tagNormal n) (deficit K)
  have hhalf : (1 / 8 : ℝ) ^ n = (1 / 4 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hquarter : (1 / 16 : ℝ) ^ n = (1 / 4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  rw [hhalf, hquarter] at hf
  have ht : 0 < (1 / 4 : ℝ) ^ n := by positivity
  have hprod : (1 / 4 : ℝ) ^ n *
      (a 0 + (1 / 2 : ℝ) ^ n * a 1 + (1 / 4 : ℝ) ^ n * a 2) ≤ 0 := by
    nlinarith
  exact nonpos_of_mul_nonpos_right hprod ht

theorem target_implies_cone (a : Parameter → ℝ) : TargetRealizable a → cone a := by
  intro h
  obtain ⟨K, hK⟩ := (targetRealizable_iff a).mp h
  obtain ⟨L, hL, hcal⟩ := normalize_references K hK
  exact calibrated_target_implies_cone hL hcal

end MixedVolume.DeficitForcing

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/DeficitForcing.lean -/

/- BEGIN SOURCE: MixedVolume/DeficitConstruction.lean -/
section


/-! Actual deficit bodies and the complete forward realization implication.
Polynomial equality is proved on a product of infinite real intervals, then
holds identically; no finite sample substitutes for the realization theorem.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.DeficitConstruction

open VolumePolynomials VolumePolynomials.Holonomy ScalarPolynomial ScalarGeometry
open ProjectedForcing ReferenceExpansion ScalarCombination CanonicalFormula
open DeficitForcing Set MeasureTheory
open scoped Pointwise

def amplitude (b : Parameter → ℝ) (n : ℕ) : ℝ :=
  b 0 + (1 / 2 : ℝ) ^ n * b 1 + (1 / 4 : ℝ) ^ n * b 2

theorem amplitude_add (b c : Parameter → ℝ) (n : ℕ) :
    amplitude (b + c) n = amplitude b n + amplitude c n := by
  dsimp [amplitude]
  ring

theorem amplitude_nonneg (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) (n : ℕ) :
    0 ≤ amplitude b n := by
  dsimp [amplitude]
  exact add_nonneg (add_nonneg (hb 0)
    (mul_nonneg (pow_nonneg (by norm_num) n) (hb 1)))
    (mul_nonneg (pow_nonneg (by norm_num) n) (hb 2))

theorem amplitude_bound (b : Parameter → ℝ) (n : ℕ) :
    |amplitude b n| ≤ |b 0| + |b 1| + |b 2| := by
  have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hq : (1 / 4 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp₀ : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hq₀ : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
  have hb₁ : |(1 / 2 : ℝ) ^ n * b 1| ≤ |b 1| := by
    rw [abs_mul, abs_of_nonneg hp₀]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (abs_nonneg (b 1))
  have hb₂ : |(1 / 4 : ℝ) ^ n * b 2| ≤ |b 2| := by
    rw [abs_mul, abs_of_nonneg hq₀]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq (abs_nonneg (b 2))
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl hb₁)) hb₂)

def commonGenerator : ℕ → Holonomy.Plane := generator 1

theorem commonGenerator_summable : Summable fun n => ‖commonGenerator n‖ :=
  generator_summable 1 (by norm_num) le_rfl

theorem amplitude_summable (b : Parameter → ℝ) :
    Summable fun n => ‖amplitude b n • commonGenerator n‖ :=
  ParallelSeries.summable_weighted_of_bounded commonGenerator commonGenerator_summable
    (amplitude b) (|b 0| + |b 1| + |b 2|) (amplitude_bound b)

def amplitudeBody (b : Parameter → ℝ) : ConvexBody Holonomy.Plane :=
  segmentSeriesBody (fun n => amplitude b n • commonGenerator n) (amplitude_summable b)

theorem generator_scale (r : ℝ) (n : ℕ) :
    generator r n = r ^ n • commonGenerator n := by
  rw [generator_factored, commonGenerator, generator_factored]
  simp only [one_pow, one_smul]

theorem amplitudeBody_single (i : Parameter) (r : ℝ) :
    amplitudeBody (Pi.single i r) = r • canonicalState i := by
  apply ConvexBody.ext
  change segmentSeries (fun n => amplitude (Pi.single i r) n • commonGenerator n) =
    r • segmentSeries (generator (rate i : ℝ))
  rw [← ParallelSeries.segmentSeries_smul _
    (generator_summable _ (rate_pos i).le (rate_le_one i))]
  congr 1
  funext n
  rw [generator_scale, smul_smul]
  congr 1
  fin_cases i <;> norm_num [amplitude, Pi.single_apply, rate] <;> ring

theorem amplitudeBody_add (b c : Parameter → ℝ)
    (hb : ∀ n, 0 ≤ amplitude b n) (hc : ∀ n, 0 ≤ amplitude c n) :
    amplitudeBody (b + c) = amplitudeBody b + amplitudeBody c := by
  apply ConvexBody.ext
  change segmentSeries (fun n => amplitude (b + c) n • commonGenerator n) =
    segmentSeries (fun n => amplitude b n • commonGenerator n) +
      segmentSeries (fun n => amplitude c n • commonGenerator n)
  simp_rw [amplitude_add]
  exact ParallelSeries.segmentSeries_add commonGenerator (amplitude b) (amplitude c)
    hb hc (amplitude_summable b) (amplitude_summable c)
    (by simpa only [amplitude_add] using amplitude_summable (b + c))

theorem amplitudeBody_eq_combination (b : Parameter → ℝ) (hb : ∀ i, 0 ≤ b i) :
    amplitudeBody b = combination b := by
  have hdecomp : b = Pi.single 0 (b 0) + Pi.single 1 (b 1) + Pi.single 2 (b 2) := by
    ext i
    fin_cases i <;> simp
  have hsingle (i : Parameter) : ∀ j, 0 ≤ (Pi.single i (b i) : Parameter → ℝ) j := by
    intro j
    by_cases h : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hb i
    · simp only [Pi.single_apply, if_neg h]
      exact le_rfl
  let e₀ : Parameter → ℝ := Pi.single 0 (b 0)
  let e₁ : Parameter → ℝ := Pi.single 1 (b 1)
  let e₂ : Parameter → ℝ := Pi.single 2 (b 2)
  have h₀₁ : amplitudeBody (e₀ + e₁) = amplitudeBody e₀ + amplitudeBody e₁ :=
    amplitudeBody_add e₀ e₁ (amplitude_nonneg e₀ (hsingle 0))
      (amplitude_nonneg e₁ (hsingle 1))
  have h₀₁₂ : amplitudeBody (e₀ + e₁ + e₂) =
      amplitudeBody (e₀ + e₁) + amplitudeBody e₂ :=
    amplitudeBody_add (e₀ + e₁) e₂
      (amplitude_nonneg (e₀ + e₁) (fun j => add_nonneg (hsingle 0 j) (hsingle 1 j)))
      (amplitude_nonneg e₂ (hsingle 2))
  calc
    amplitudeBody b = amplitudeBody (e₀ + e₁ + e₂) := congrArg amplitudeBody hdecomp
    _ = amplitudeBody e₀ + amplitudeBody e₁ + amplitudeBody e₂ := by rw [h₀₁₂, h₀₁]
    _ = combination b := by
      rw [show amplitudeBody e₀ = b 0 • canonicalState 0 from amplitudeBody_single 0 (b 0),
        show amplitudeBody e₁ = b 1 • canonicalState 1 from amplitudeBody_single 1 (b 1),
        show amplitudeBody e₂ = b 2 • canonicalState 2 from amplitudeBody_single 2 (b 2)]
      rfl

theorem budget_sub_pos (a : Parameter → ℝ) (i : Parameter) : 0 < budget a - a i := by
  have h₀ := le_abs_self (a 0)
  have h₁ := le_abs_self (a 1)
  have h₂ := le_abs_self (a 2)
  have h₀' := abs_nonneg (a 0)
  have h₁' := abs_nonneg (a 1)
  have h₂' := abs_nonneg (a 2)
  fin_cases i <;> dsimp [budget] <;> linarith

def deficitBody (a : Parameter → ℝ) : ConvexBody Holonomy.Plane := amplitudeBody (-a)

theorem deficit_identity (a : Parameter → ℝ) (ha : cone a) :
    deficitBody a + combination (fun _ => budget a) =
      combination (fun i => budget a - a i) := by
  have hneg : ∀ n, 0 ≤ amplitude (-a) n := by
    intro n
    have h := ha n
    dsimp [amplitude]
    change 0 ≤ -a 0 + (1 / 2 : ℝ) ^ n * -a 1 + (1 / 4 : ℝ) ^ n * -a 2
    linarith
  have hbudget := amplitude_nonneg (fun _ : Parameter => budget a) (fun _ => (budget_pos a).le)
  rw [deficitBody, ← amplitudeBody_eq_combination _ (fun _ => (budget_pos a).le),
    ← amplitudeBody_add _ _ hneg hbudget]
  have hf : (-a) + (fun _ : Parameter => budget a) = (fun i => budget a - a i) := by
    ext i
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  rw [hf, amplitudeBody_eq_combination _ (fun i => (budget_sub_pos a i).le)]

theorem cancellation_in_box (a : Parameter → ℝ) (ha : cone a)
    (b : Parameter → ℝ) (z : ℝ) (hz₀ : 0 ≤ z) (hz₁ : z ≤ 1)
    (hb : ∀ i, budget a ≤ b i) :
    combination b + z • deficitBody a = combination (fun i => b i - a i * z) := by
  let r := budget a
  let d : Parameter → ℝ := fun i => b i - r * z
  have hr : 0 < r := budget_pos a
  have hrz : r * z ≤ r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz₁ hr.le
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    dsimp [d]
    nlinarith [hb i]
  have hR : ∀ i : Parameter, 0 ≤ r * z := fun _ => mul_nonneg hr.le hz₀
  have hdiff : ∀ i, 0 ≤ r - a i := fun i => (budget_sub_pos a i).le
  have hbdecomp : combination b = combination d + z • combination (fun _ => r) := by
    rw [← combination_smul z, ← combination_add _ _ hd (fun _ => mul_nonneg hz₀ hr.le)]
    congr 1
    funext i
    dsimp [d]
    ring
  rw [hbdecomp]
  calc
    combination d + z • combination (fun _ => r) + z • deficitBody a =
        combination d + z • (deficitBody a + combination (fun _ => r)) := by
          rw [smul_add]
          ac_rfl
    _ = combination d + z • combination (fun i => r - a i) := by rw [deficit_identity a ha]
    _ = combination (fun i => d i + z * (r - a i)) := by
      rw [← combination_smul z, combination_add _ _ hd
        (fun i => mul_nonneg hz₀ (hdiff i))]
    _ = _ := by
      congr 1
      funext i
      dsimp [d]
      ring

def identityDomain (a : Parameter → ℝ) (i : Label) : Set ℝ :=
  if i = deficitLabel then Icc 0 1 else Ici (budget a)

theorem identityDomain_infinite (a : Parameter → ℝ) (i : Label) :
    (identityDomain a i).Infinite := by
  unfold identityDomain
  split
  · exact Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)
  · exact Set.Ici_infinite _

theorem cone_implies_target (a : Parameter → ℝ) (ha : cone a) : TargetRealizable a := by
  let K := tupleWithDeficit (deficitBody a)
  let P := volumePolynomial volume K
  have hpoly : P = targetPolynomial a := by
    apply MvPolynomial.funext_set (identityDomain a) (identityDomain_infinite a)
    intro w hw
    have hz : 0 ≤ w deficitLabel ∧ w deficitLabel ≤ 1 := by
      simpa [identityDomain] using hw deficitLabel (mem_univ _)
    have hb : ∀ i : Parameter, budget a ≤ w (stateLabel i) := by
      intro i
      have hi : stateLabel i ≠ deficitLabel := by
        intro h
        have hv := congrArg Fin.val h
        simp only [stateLabel, deficitLabel] at hv
        omega
      simpa only [identityDomain, if_neg hi, mem_Ici] using hw (stateLabel i) (mem_univ _)
    have hnonneg : ∀ i, 0 ≤ w i := by
      intro i
      by_cases hi : i = deficitLabel
      · simpa only [hi] using hz.1
      · have h := hw i (mem_univ _)
        simp only [identityDomain, if_neg hi, mem_Ici] at h
        exact (budget_pos a).le.trans h
    have hb' : ∀ i, 0 ≤ w (stateLabel i) - a i * w deficitLabel := by
      intro i
      have hr := budget_pos a
      have hd := budget_sub_pos a i
      have hrz : budget a * w deficitLabel ≤ budget a := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2 hr.le
      have hleft : 0 ≤ w (stateLabel i) - budget a * w deficitLabel := by linarith [hb i]
      have hright : 0 ≤ w deficitLabel * (budget a - a i) := mul_nonneg hz.1 hd.le
      nlinarith
    rw [show MvPolynomial.eval w P = volumeFunction K w from volumePolynomial_eval volume K w hnonneg,
      eval_targetPolynomial]
    exact volume_of_deficit_cancellation (deficitBody a) w
      (fun i => w (stateLabel i) - a i * w deficitLabel) hnonneg hb'
      (cancellation_in_box a ha _ _ hz.1 hz.2 hb)
  refine ⟨K, ?_⟩
  intro w hw
  rw [← hpoly]
  exact volumePolynomial_eval volume K w hw

/-- Complete global realization equivalence for the rational twelve-body
scalar section.  Every realizing object is an arbitrary compact convex body. -/
theorem target_iff_cone (a : Parameter → ℝ) : TargetRealizable a ↔ cone a :=
  ⟨target_implies_cone a, cone_implies_target a⟩

end MixedVolume.DeficitConstruction

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/DeficitConstruction.lean -/

/- BEGIN SOURCE: MixedVolume/DyadicCone.lean -/
section


/-! The exact dyadic half-space cone and its infinite boundary geometry.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.DyadicCone

open Set VolumePolynomials
open scoped Pointwise

def t (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem t_pos (n : ℕ) : 0 < t n := pow_pos (by norm_num) n
theorem t_le_one (n : ℕ) : t n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
theorem t_succ (n : ℕ) : t (n + 1) = t n / 2 := by simp [t, pow_succ, div_eq_mul_inv]

theorem t_strictAnti : StrictAnti t := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [t_succ]
  linarith [t_pos n]

theorem lower_index_gap (n k : ℕ) (h : n < k) : t k ≤ t n - t k := by
  have hpow := t_strictAnti.antitone (show n + 1 ≤ k by omega)
  rw [t_succ] at hpow
  linarith

theorem upper_index_gap (n k : ℕ) (h : k < n) : t n - t k ≤ -(t k / 2) := by
  have hpow := t_strictAnti.antitone (show k + 1 ≤ n by omega)
  rw [t_succ] at hpow
  linarith

def normal (n : ℕ) : (Fin 3 → ℝ) →L[ℝ] ℝ where
  toFun a := a 0 + t n * a 1 + t n ^ 2 * a 2
  map_add' a b := by simp only [Pi.add_apply]; ring
  map_smul' r a := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  cont := by fun_prop

def cone : Set (Fin 3 → ℝ) := {a | ∀ n, normal n a ≤ 0}

def plane (n : ℕ) : Set (Fin 3 → ℝ) := {a | normal n a = 0}

def point (ε : ℝ) (k : ℕ) : Fin 3 → ℝ := ![-ε * t k ^ 2, 2 * ε * t k, -ε]

theorem normal_point (ε : ℝ) (k n : ℕ) :
    normal n (point ε k) = -ε * (t n - t k) ^ 2 := by
  dsimp [normal, point]
  ring

theorem point_mem_cone (ε : ℝ) (hε : 0 ≤ ε) (k : ℕ) : point ε k ∈ cone := by
  intro n
  rw [normal_point]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) (sq_nonneg _)

theorem cone_mem_frontier {a : Fin 3 → ℝ} (ha : a ∈ cone) (k : ℕ)
    (hk : normal k a = 0) : a ∈ frontier cone := by
  apply exposed_mem_frontier (normal k) cone (Pi.single 0 1)
  · norm_num [normal, Pi.single_apply]
  · exact ⟨ha, fun b hb => by rw [hk]; exact hb k⟩

/-- The planar C=-1 section, retaining every dyadic inequality. -/
def planarSection : Set (ℝ × ℝ) :=
  {p | ∀ n, p.1 + t n * p.2 - t n ^ 2 ≤ 0}

def planarNormal (k : ℕ) : (ℝ × ℝ) →L[ℝ] ℝ where
  toFun p := p.1 + t k * p.2
  map_add' p q := by dsimp; ring
  map_smul' r p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring
  cont := by fun_prop

def segmentCenter (k : ℕ) : ℝ × ℝ := (-t k ^ 2, 2 * t k)
def segmentDirection (k : ℕ) : ℝ × ℝ := (-t k ^ 2 / 4, t k / 4)

theorem planar_segment_evaluation (k n : ℕ) (q : ℝ) :
    (segmentCenter k + q • segmentDirection k).1 +
      t n * (segmentCenter k + q • segmentDirection k).2 - t n ^ 2 =
        (t n - t k) * (q * t k / 4 - (t n - t k)) := by
  dsimp [segmentCenter, segmentDirection]
  ring

theorem segment_mem_planarSection (k : ℕ) (q : ℝ)
    (hq : q ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    segmentCenter k + q • segmentDirection k ∈ planarSection := by
  intro n
  have htk := t_pos k
  rw [planar_segment_evaluation]
  rcases lt_trichotomy n k with h | rfl | h
  · have hgap := lower_index_gap n k h
    apply mul_nonpos_of_nonneg_of_nonpos
    · linarith [t_pos k]
    · nlinarith [mul_nonneg (t_pos k).le (sub_nonneg.mpr hq.2)]
  · simp
  · have hgap := upper_index_gap n k h
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith [t_pos k]
    · nlinarith [mul_nonneg (t_pos k).le (sub_nonneg.mpr hq.1)]

theorem segment_mem_planar_frontier (k : ℕ) (q : ℝ)
    (hq : q ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    segmentCenter k + q • segmentDirection k ∈ frontier planarSection := by
  apply exposed_mem_frontier (planarNormal k) planarSection ((1 : ℝ), (0 : ℝ))
  · norm_num [planarNormal]
  · refine ⟨segment_mem_planarSection k q hq, ?_⟩
    intro y hy
    have hbound := hy k
    change y.1 + t k * y.2 ≤ _
    have heq : planarNormal k (segmentCenter k + q • segmentDirection k) = t k ^ 2 := by
      dsimp [planarNormal, segmentCenter, segmentDirection]
      ring
    rw [heq]
    linarith

theorem segmentDirections_nonparallel (i j : ℕ) (hij : i ≠ j) :
    (segmentDirection i).1 * (segmentDirection j).2 -
      (segmentDirection i).2 * (segmentDirection j).1 ≠ 0 := by
  have ht : t j - t i ≠ 0 := sub_ne_zero.mpr (t_strictAnti.injective.ne hij.symm)
  have heq : (segmentDirection i).1 * (segmentDirection j).2 -
      (segmentDirection i).2 * (segmentDirection j).1 =
        t i * t j * (t j - t i) / 16 := by
    dsimp [segmentDirection]
    ring
  rw [heq]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (t_pos i).ne' (t_pos j).ne') ht) (by norm_num)

theorem planarSection_not_semialgebraic :
    ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹' planarSection) :=
  not_semialgebraic_of_nonparallel_boundary_segments planarSection segmentCenter segmentDirection
    segmentDirections_nonparallel (fun k q hq =>
      segment_mem_planar_frontier k q (by simpa only [neg_div] using hq))

def sliceLinear : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x 0, x 1, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp

theorem cone_not_semialgebraic : ¬ TauCeti.IsSemialgebraic cone := by
  intro hc
  have hs := hc.preimage_affine sliceLinear (![0, 0, -1] : Fin 3 → ℝ)
  apply planarSection_not_semialgebraic
  convert hs using 1
  ext x
  change (∀ n, x 0 + t n * x 1 - t n ^ 2 ≤ 0) ↔
    (∀ n, (0 + x 0) + t n * (0 + x 1) + t n ^ 2 * (-1 + 0) ≤ 0)
  simp only [zero_add, add_zero, mul_neg_one, sub_eq_add_neg]


theorem dyadic_gap_squared (n k : ℕ) (hn : n ≠ k) :
    t k ^ 2 / 4 ≤ (t n - t k) ^ 2 := by
  rcases lt_or_gt_of_ne hn with h | h
  · have hgap := lower_index_gap n k h
    have hp := t_pos k
    have hsq := (sq_le_sq₀ (show 0 ≤ t k / 2 by positivity)
      (show 0 ≤ t n - t k by linarith)).mpr (show t k / 2 ≤ t n - t k by linarith)
    nlinarith
  · have hgap := upper_index_gap n k h
    have hp := t_pos k
    have hsq := (sq_le_sq₀ (show 0 ≤ t k / 2 by positivity)
      (show 0 ≤ -(t n - t k) by linarith)).mpr
        (show t k / 2 ≤ -(t n - t k) by linarith)
    nlinarith

theorem normal_deviation_bound (n : ℕ) (a b : Fin 3 → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (h : ∀ i, |a i - b i| ≤ δ) :
    normal n a ≤ normal n b + 3 * δ := by
  have h₀ := (le_abs_self (a 0 - b 0)).trans (h 0)
  have h₁ := (le_abs_self (a 1 - b 1)).trans (h 1)
  have h₂ := (le_abs_self (a 2 - b 2)).trans (h 2)
  have ht₀ := (t_pos n).le
  have ht₁ := t_le_one n
  have ht₂ : t n ^ 2 ≤ 1 := pow_le_one₀ ht₀ ht₁
  have hterm₁ := mul_le_mul_of_nonneg_left h₁ ht₀
  have hterm₂ := mul_le_mul_of_nonneg_left h₂ (sq_nonneg (t n))
  have hδ₁ := mul_le_mul_of_nonneg_right ht₁ hδ
  have hδ₂ := mul_le_mul_of_nonneg_right ht₂ hδ
  dsimp [normal]
  nlinarith

/-- Every supporting plane has a boundary patch at every positive scale. -/
theorem boundary_plane_patch_scaled (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ point ε k ∈ plane k ∧
      ∀ b, dist b (point ε k) < δ → b ∈ plane k → b ∈ frontier cone := by
  let a := point ε k
  let δ := ε * t k ^ 2 / 16
  have hδ : 0 < δ := div_pos (mul_pos hε (sq_pos_of_pos (t_pos k))) (by norm_num)
  refine ⟨δ, hδ, ?_, ?_⟩
  · change normal k (point ε k) = 0
    rw [normal_point]
    simp
  · intro b hb hbk
    apply cone_mem_frontier (k := k) ?_ hbk
    intro n
    by_cases hn : n = k
    · subst n
      exact hbk.le
    · have hcoords : ∀ i, |b i - a i| ≤ δ := by
        intro i
        have hi := norm_le_pi_norm (b - a) i
        have hnorm : ‖b - a‖ < δ := by simpa only [dist_eq_norm] using hb
        exact (show |b i - a i| ≤ ‖b - a‖ by
          simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi).trans hnorm.le
      have hbound := normal_deviation_bound n b a δ hδ.le hcoords
      have hgap := mul_le_mul_of_nonneg_left (dyadic_gap_squared n k hn) hε.le
      have ht : 0 < ε * t k ^ 2 := mul_pos hε (sq_pos_of_pos (t_pos k))
      dsimp [a] at hbound
      rw [normal_point] at hbound
      dsimp [δ] at hbound
      nlinarith

/-- Every supporting plane contains a relatively open patch of the boundary. -/
theorem boundary_plane_patch (k : ℕ) :
    ∃ a : Fin 3 → ℝ, ∃ δ : ℝ, 0 < δ ∧ a ∈ plane k ∧
      ∀ b, dist b a < δ → b ∈ plane k → b ∈ frontier cone := by
  exact ⟨point 1 k, boundary_plane_patch_scaled k 1 (by norm_num)⟩

theorem point_norm_le (ε : ℝ) (hε : 0 ≤ ε) (k : ℕ) : ‖point ε k‖ ≤ 2 * ε := by
  have ht₀ := (t_pos k).le
  have ht₁ := t_le_one k
  have ht₂ : t k ^ 2 ≤ 1 := pow_le_one₀ ht₀ ht₁
  have hmul₁ := mul_le_mul_of_nonneg_left ht₁ hε
  have hmul₂ := mul_le_mul_of_nonneg_left ht₂ hε
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤ 2 * ε by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · change |-ε * t k ^ 2| ≤ 2 * ε
    rw [abs_mul, abs_neg, abs_of_nonneg hε, abs_of_nonneg (sq_nonneg (t k))]
    nlinarith
  · change |2 * ε * t k| ≤ 2 * ε
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε) ht₀)]
    nlinarith
  · change |-ε| ≤ 2 * ε
    rw [abs_neg, abs_of_nonneg hε]
    linarith

/-- All infinitely many patches occur inside every neighbourhood of the origin. -/
theorem boundary_plane_patch_local (k : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ a : Fin 3 → ℝ, ∃ δ : ℝ, 0 < δ ∧ a ∈ plane k ∩ Metric.ball 0 R ∧
      ∀ b, dist b a < δ → b ∈ plane k → b ∈ frontier cone ∩ Metric.ball 0 R := by
  obtain ⟨δ, hδ, ha, hpatch⟩ := boundary_plane_patch_scaled k (R / 4) (by positivity)
  have hnorm : ‖point (R / 4) k‖ ≤ R / 2 := by
    convert point_norm_le (R / 4) (by positivity) k using 1 <;> ring
  refine ⟨point (R / 4) k, min δ (R / 2), lt_min hδ (by positivity),
    ⟨ha, ?_⟩, ?_⟩
  · simpa only [Metric.mem_ball, dist_zero_right] using hnorm.trans_lt (by linarith)
  · intro b hb hbk
    refine ⟨hpatch b (hb.trans_le (min_le_left _ _)) hbk, ?_⟩
    have hd : dist b (point (R / 4) k) < R / 2 := hb.trans_le (min_le_right _ _)
    have htriangle := dist_triangle b (point (R / 4) k) 0
    rw [dist_zero_right, dist_zero_right] at htriangle
    rw [Metric.mem_ball, dist_zero_right]
    linarith

end MixedVolume.DyadicCone

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/DyadicCone.lean -/

/- BEGIN SOURCE: MixedVolume/ScalarSection.lean -/
section


/-! The rational quadratic coefficient map and the geometric statement of
Theorem 6.1.  This is a new existential witness, not a claim that its defining
formula is the particular stochastic-matrix map printed in the paper.
Verification status is recorded in the build and axiom-audit manifests. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.ScalarSection

open VolumePolynomials ScalarPolynomial CanonicalFormula DeficitConstruction
open Set MeasureTheory MvPolynomial
open scoped Pointwise

def stateVariables : Parameter → MvPolynomial Label ℚ := fun i => X (stateLabel i)
def imageVariables : Parameter → MvPolynomial Label ℚ := fun i => X (imageLabel i)

def rationalLinearBody (i : Parameter) : MvPolynomial Label ℚ :=
  X deficitLabel *
    (kappa (X 1) (X 3) (X 4) imageVariables * bilinear stateVariables (Pi.single i 1) +
      linearStatePart (X 0) (X 1) (X 2) (X 3) (X 4) (Pi.single i 1) imageVariables)

def rationalQuadraticBody : MvPolynomial Label ℚ :=
  X deficitLabel ^ 2 * kappa (X 1) (X 3) (X 4) imageVariables

/-- One polynomial with rational coefficients for each ordinary degree-three
monomial in twelve body variables. There are no omitted array coordinates. -/
def rationalCoefficient (α : MultiIndex 12 3) : MvPolynomial Parameter ℚ :=
  C (canonicalRationalPolynomial.coeff (exponent α)) -
    C ((rationalLinearBody 0).coeff (exponent α)) * X 0 -
    C ((rationalLinearBody 1).coeff (exponent α)) * X 1 -
    C ((rationalLinearBody 2).coeff (exponent α)) * X 2 +
    C (rationalQuadraticBody.coeff (exponent α)) * quadratic (fun i => X i)

def coefficientMap (a : Parameter → ℝ) : Coefficients 12 3 :=
  fun α => eval₂ (algebraMap ℚ ℝ) a (rationalCoefficient α)

theorem canonicalFormula_coordinate_shift {R : Type*} [CommRing R] [Algebra ℚ R]
    (e₁ e₂ e₃ s ι z : R) (b c a : Parameter → R) :
    canonicalFormula e₁ e₂ e₃ s ι (fun i => b i - a i * z) c =
      canonicalFormula e₁ e₂ e₃ s ι b c -
      a 0 * (z * (kappa e₂ s ι c * bilinear b (Pi.single 0 1) +
        linearStatePart e₁ e₂ e₃ s ι (Pi.single 0 1) c)) -
      a 1 * (z * (kappa e₂ s ι c * bilinear b (Pi.single 1 1) +
        linearStatePart e₁ e₂ e₃ s ι (Pi.single 1 1) c)) -
      a 2 * (z * (kappa e₂ s ι c * bilinear b (Pi.single 2 1) +
        linearStatePart e₁ e₂ e₃ s ι (Pi.single 2 1) c)) +
      quadratic a * (z ^ 2 * kappa e₂ s ι c) := by
  rw [canonicalFormula_shift]
  simp only [linearStatePart, bilinear, quadratic, height, width, Pi.single_apply]
  norm_num
  ring

theorem targetPolynomial_decomposition (a : Parameter → ℝ) :
    targetPolynomial a =
      MvPolynomial.map (algebraMap ℚ ℝ) canonicalRationalPolynomial -
      C (a 0) * MvPolynomial.map (algebraMap ℚ ℝ) (rationalLinearBody 0) -
      C (a 1) * MvPolynomial.map (algebraMap ℚ ℝ) (rationalLinearBody 1) -
      C (a 2) * MvPolynomial.map (algebraMap ℚ ℝ) (rationalLinearBody 2) +
      C (quadratic a) * MvPolynomial.map (algebraMap ℚ ℝ) rationalQuadraticBody := by
  rw [targetPolynomial, canonicalFormula_coordinate_shift]
  apply MvPolynomial.funext
  intro w
  simp [canonicalRationalPolynomial, rationalLinearBody, rationalQuadraticBody,
    stateVariables, imageVariables, canonicalFormula, referenceCubic, kappa, linearStatePart, linearHeight,
    ScalarPolynomial.linearWidth, quadratic, bilinear, height, width, componentSum,
    divideRates, rat, Pi.single_apply, MvPolynomial.algebraMap_apply] <;> ring

theorem coefficientMap_eq (a : Parameter → ℝ) :
    coefficientMap a = coefficientsOfPolynomial (d := 3) (targetPolynomial a) := by
  ext α
  rw [coefficientsOfPolynomial, targetPolynomial_decomposition]
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_add,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp [coefficientMap, rationalCoefficient, quadratic, rat,
    MvPolynomial.algebraMap_apply] <;> ring

theorem rationalQuadratic_homogeneous :
    (quadratic (fun i : Parameter => (X i : MvPolynomial Parameter ℚ))).IsHomogeneous 2 := by
  have h₀ := (isHomogeneous_X_pow (R := ℚ) (0 : Parameter) 2).C_mul (areaRat 0)
  have h₁ := (isHomogeneous_X_pow (R := ℚ) (1 : Parameter) 2).C_mul (areaRat 1)
  have h₂ := (isHomogeneous_X_pow (R := ℚ) (2 : Parameter) 2).C_mul (areaRat 2)
  have h₀₁ := ((isHomogeneous_X ℚ (0 : Parameter)).C_mul (mixedRat 0 1)).mul (isHomogeneous_X ℚ 1)
  have h₀₂ := ((isHomogeneous_X ℚ (0 : Parameter)).C_mul (mixedRat 0 2)).mul (isHomogeneous_X ℚ 2)
  have h₁₂ := ((isHomogeneous_X ℚ (1 : Parameter)).C_mul (mixedRat 1 2)).mul (isHomogeneous_X ℚ 2)
  simpa only [quadratic, rat, MvPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    (((((h₀.add h₁).add h₂).add h₀₁).add h₀₂).add h₁₂)

theorem rationalCoefficient_degree_le_two (α : MultiIndex 12 3) :
    (rationalCoefficient α).totalDegree ≤ 2 := by
  have hlinear (r : ℚ) (i : Parameter) : (C r * X i : MvPolynomial Parameter ℚ).totalDegree ≤ 2 :=
    ((isHomogeneous_C_mul_X r i).totalDegree_le).trans (by decide)
  have hsub {p q : MvPolynomial Parameter ℚ} (hp : p.totalDegree ≤ 2) (hq : q.totalDegree ≤ 2) :
      (p - q).totalDegree ≤ 2 := (totalDegree_sub p q).trans (max_le hp hq)
  have hc : (C (canonicalRationalPolynomial.coeff (exponent α)) :
      MvPolynomial Parameter ℚ).totalDegree ≤ 2 := by simp
  exact (totalDegree_add _ _).trans (max_le
    (hsub (hsub (hsub hc (hlinear _ _)) (hlinear _ _)) (hlinear _ _))
    ((rationalQuadratic_homogeneous.C_mul _).totalDegree_le))

theorem eval_canonicalRationalPolynomial (w : Label → ℝ) :
    eval w (MvPolynomial.map (algebraMap ℚ ℝ) canonicalRationalPolynomial) =
      canonicalFormula (w 0) (w 1) (w 2) (w 3) (w 4)
        (fun i => w (stateLabel i)) (fun i => w (imageLabel i)) := by
  simp [canonicalRationalPolynomial, canonicalFormula, referenceCubic, quadratic,
    height, width, componentSum, divideRates, rat, MvPolynomial.algebraMap_apply]

theorem canonicalRationalPolynomial_homogeneous : canonicalRationalPolynomial.IsHomogeneous 3 := by
  let K := tupleWithDeficit (0 : ConvexBody (ℝ × ℝ))
  have heq : volumePolynomial volume K = MvPolynomial.map (algebraMap ℚ ℝ) canonicalRationalPolynomial := by
    apply volumePolynomial_eq_of_eval
    intro w hw
    rw [eval_canonicalRationalPolynomial]
    exact (volume_of_deficit_cancellation 0 w (fun i => w (stateLabel i)) hw
      (fun i => hw _) (by
        change ScalarCombination.combination (fun i => w (stateLabel i)) +
          w deficitLabel • (0 : ConvexBody (ℝ × ℝ)) = ScalarCombination.combination (fun i => w (stateLabel i))
        have hzero : w deficitLabel • (0 : ConvexBody (ℝ × ℝ)) = 0 := by
          apply ConvexBody.ext
          change w deficitLabel • ({0} : Set (ℝ × ℝ)) = {0}
          simp
        rw [hzero, add_zero])).symm
  have hh := volumePolynomial_homogeneous volume K
  rw [heq] at hh
  have hh' : (MvPolynomial.map (algebraMap ℚ ℝ) canonicalRationalPolynomial).IsHomogeneous 3 := by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hh
  exact MvPolynomial.IsHomogeneous.of_map Rat.cast_injective hh'

def substitution (a : Parameter → ℝ) : Label → MvPolynomial Label ℝ :=
  ![X 0, X 1, X 2, X 3, X 4,
    X 5 - C (a 0) * X deficitLabel, X 6 - C (a 1) * X deficitLabel,
    X 7 - C (a 2) * X deficitLabel, X 8, X 9, X 10, X 11]

theorem targetPolynomial_eq_aeval (a : Parameter → ℝ) :
    targetPolynomial a = aeval (substitution a) canonicalRationalPolynomial := by
  simp [targetPolynomial, canonicalRationalPolynomial, substitution, canonicalFormula,
    referenceCubic, quadratic, height, width, componentSum, divideRates, rat,
    stateLabel, imageLabel, deficitLabel, MvPolynomial.algebraMap_apply]

theorem targetPolynomial_homogeneous (a : Parameter → ℝ) : (targetPolynomial a).IsHomogeneous 3 := by
  rw [targetPolynomial_eq_aeval]
  have hs : ∀ i, (substitution a i).IsHomogeneous 1 := by
    intro i
    fin_cases i <;> simp only [substitution, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.tail_cons]
    all_goals first
      | exact isHomogeneous_X ℝ _
      | exact (isHomogeneous_X ℝ _).sub ((isHomogeneous_X ℝ _).C_mul _)
  simpa only [one_mul] using canonicalRationalPolynomial_homogeneous.aeval (substitution a) hs

/-- The complete full-array realization statement, with all real parameters. -/
theorem coefficientMap_mem_iff (a : Parameter → ℝ) :
    coefficientMap a ∈ VolumeLocus 12 3 ↔ ScalarPolynomial.cone a := by
  rw [coefficientMap_eq, mem_volumeLocus]
  constructor
  · rintro ⟨K, hK⟩
    apply (target_iff_cone a).mp
    refine ⟨K, ?_⟩
    intro w hw
    have h := hK w hw
    rw [evaluate_eq_polynomial_eval,
      coefficientPolynomial_coefficientsOfPolynomial _ (targetPolynomial_homogeneous a)] at h
    exact h
  · intro ha
    obtain ⟨K, hK⟩ := (target_iff_cone a).mpr ha
    exact ⟨K, realizes_of_homogeneous_polynomial K _ (targetPolynomial_homogeneous a) hK⟩

theorem scalar_cone_eq : {a | ScalarPolynomial.cone a} = DyadicCone.cone := by
  ext a
  have hpow (n : ℕ) : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  change (∀ n, a 0 + (1 / 2 : ℝ) ^ n * a 1 + (1 / 4 : ℝ) ^ n * a 2 ≤ 0) ↔
    (∀ n, a 0 + DyadicCone.t n * a 1 + DyadicCone.t n ^ 2 * a 2 ≤ 0)
  simp only [DyadicCone.t, hpow]

/-- A fixed rational quadratic section of the genuine twelve-body realization
locus is exactly the dyadic cone, globally and hence on every neighbourhood. -/
theorem rational_quadratic_section :
    (∀ α, (rationalCoefficient α).totalDegree ≤ 2) ∧
      coefficientMap ⁻¹' VolumeLocus 12 3 = DyadicCone.cone := by
  refine ⟨rationalCoefficient_degree_le_two, ?_⟩
  rw [← scalar_cone_eq]
  ext a
  exact coefficientMap_mem_iff a

theorem theorem_6_1_nonsemialgebraic : ¬ TauCeti.IsSemialgebraic (VolumeLocus 12 3) := by
  intro h
  have hp := h.preimage_eval (fun α => MvPolynomial.map (algebraMap ℚ ℝ) (rationalCoefficient α))
  have heq : (fun a α => MvPolynomial.eval a
      (MvPolynomial.map (algebraMap ℚ ℝ) (rationalCoefficient α))) = coefficientMap := by
    funext a α
    simp only [coefficientMap, eval_map]
  rw [heq] at hp
  apply DyadicCone.cone_not_semialgebraic
  rw [← rational_quadratic_section.2]
  exact hp

/-- The full geometric assertion of Theorem 6.1, with an explicit rational
quadratic witness and all supporting-plane patches arbitrarily close to the
interior point zero of the parameter domain `ℝ³`. -/
theorem theorem_6_1 :
    (∀ α, (rationalCoefficient α).totalDegree ≤ 2) ∧
      coefficientMap ⁻¹' VolumeLocus 12 3 = DyadicCone.cone ∧
      (∀ (k : ℕ) (R : ℝ), 0 < R →
        ∃ a : Fin 3 → ℝ, ∃ δ : ℝ, 0 < δ ∧
          a ∈ DyadicCone.plane k ∩ Metric.ball 0 R ∧
          ∀ b, dist b a < δ → b ∈ DyadicCone.plane k →
            b ∈ frontier DyadicCone.cone ∩ Metric.ball 0 R) ∧
      ¬ TauCeti.IsSemialgebraic (VolumeLocus 12 3) :=
  ⟨rational_quadratic_section.1, rational_quadratic_section.2,
    DyadicCone.boundary_plane_patch_local, theorem_6_1_nonsemialgebraic⟩

end MixedVolume.ScalarSection

end
end -- closes the original EOF public section
end -- closes the synthetic per-file scope
/- END SOURCE: MixedVolume/ScalarSection.lean -/

