module

public import VolumePolynomials.CommonLineCoordinates
public import VolumePolynomials.CrossPlaneVolume
public import VolumePolynomials.LinearFrame
public import VolumePolynomials.FiberVolume
public import VolumePolynomials.TrivariateMixedVolume
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # Actual volume identities in compatible common-line coordinates

Every pair uses the same intrinsic coordinates on each plane. Its actual
Haar factor appears in both repeated coefficients, so no determinant or
angular factor is postulated. Fiber integrability follows from Fubini on
the images of the actual total compact convex body.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.CommonLineVolume

abbrev Plane := ℝ × ℝ
abbrev ProductThree := ℝ × Plane

def area (A : ConvexBody Plane) : ℝ := volume.real (A : Set Plane)
def width (A : ConvexBody Plane) : ℝ :=
  volume.real (PlanarExtrusion.projection (A : Set Plane))

theorem pair_volume
    (T : Space 3 ≃L[ℝ] ProductThree)
    (f g : Plane →L[ℝ] Space 3)
    (hf : ∀ p, T (f p) = CrossPlaneVolume.firstPlane p)
    (hg : ∀ p, T (g p) = CrossPlaneVolume.secondPlane p)
    (A B : ConvexBody Plane) :
    volume.real (mapBody f A + mapBody g B : Set (Space 3)) =
      (LinearFrame.volumeFactor T : ℝ) *
        (area A * width B + width A * area B) := by
  first
  | have himage : T '' (mapBody f A + mapBody g B : Set (Space 3)) =
        CrossPlaneVolume.planeSum (A : Set Plane) (B : Set Plane) := by
      change T '' (f '' (A : Set Plane) + g '' (B : Set Plane)) = _
      rw [Set.image_add T, Set.image_image, Set.image_image]
      apply congrArg₂ (· + ·)
      · exact Set.image_congr (fun p _ => hf p)
      · exact Set.image_congr (fun p _ => hg p)
    have hv := LinearFrame.realVolume_eq_factor_mul_image T
      (mapBody f A + mapBody g B : Set (Space 3))
    rw [himage, CrossPlaneVolume.realVolume_planeSum
      A.isCompact B.isCompact A.convex B.convex] at hv
    exact hv

theorem pair_volume_smul
    (T : Space 3 ≃L[ℝ] ProductThree)
    (f g : Plane →L[ℝ] Space 3)
    (hf : ∀ p, T (f p) = CrossPlaneVolume.firstPlane p)
    (hg : ∀ p, T (g p) = CrossPlaneVolume.secondPlane p)
    (A B : ConvexBody Plane) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume.real (a • mapBody f A + b • mapBody g B : Set (Space 3)) =
      (LinearFrame.volumeFactor T : ℝ) *
        (area A * width B * a ^ 2 * b + width A * area B * a * b ^ 2) := by
  first
  | have h := pair_volume T f g hf hg (a • A) (b • B)
    rw [mapBody_smul, mapBody_smul] at h
    calc
      _ = (LinearFrame.volumeFactor T : ℝ) *
          (area (a • A) * width (b • B) + width (a • A) * area (b • B)) := h
      _ = _ := by
        simp only [area, width, ConvexBody.coe_smul, CrossPlaneVolume.projection_smul,
          CrossPlaneVolume.realVolume_smul_plane _ ha,
          CrossPlaneVolume.realVolume_smul_plane _ hb,
          CrossPlaneVolume.realVolume_smul_line _ ha,
          CrossPlaneVolume.realVolume_smul_line _ hb]
        ring

theorem pair_repeated_coefficients
    (T : Space 3 ≃L[ℝ] ProductThree)
    (f g : Plane →L[ℝ] Space 3)
    (hf : ∀ p, T (f p) = CrossPlaneVolume.firstPlane p)
    (hg : ∀ p, T (g p) = CrossPlaneVolume.secondPlane p)
    (A B : ConvexBody Plane) :
    3 * mixedVolume3 volume (mapBody f A) (mapBody f A) (mapBody g B) =
      (LinearFrame.volumeFactor T : ℝ) * area A * width B ∧
    3 * mixedVolume3 volume (mapBody g B) (mapBody g B) (mapBody f A) =
      (LinearFrame.volumeFactor T : ℝ) * width A * area B := by
  first
  | have hA := pair_volume_smul T f g hf hg A B
      (a := 1) (b := 0) (by norm_num) (by norm_num)
    have hB := pair_volume_smul T f g hf hg A B
      (a := 0) (b := 1) (by norm_num) (by norm_num)
    simp only [one_smul, Set.zero_smul_set (mapBody f A).nonempty,
      Set.zero_smul_set (mapBody g B).nonempty, add_zero, zero_add,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at hA hB
    have hdim : finrank ℝ (Space 3) = 3 := by simp [Space]
    have h1 := trivariate_volume_formula volume hdim
      (mapBody f A) (mapBody g B) (mapBody g B)
      (a := 1) (b := 1) (c := 0) (by norm_num) (by norm_num) (by norm_num)
    have h2 := trivariate_volume_formula volume hdim
      (mapBody f A) (mapBody g B) (mapBody g B)
      (a := 2) (b := 1) (c := 0) (by norm_num) (by norm_num) (by norm_num)
    have hp1 := pair_volume_smul T f g hf hg A B
      (a := 1) (b := 1) (by norm_num) (by norm_num)
    have hp2 := pair_volume_smul T f g hf hg A B
      (a := 2) (b := 1) (by norm_num) (by norm_num)
    simp only [one_smul, Set.zero_smul_set (mapBody g B).nonempty, add_zero] at h1 h2 hp1 hp2
    rw [hA, hB] at h1 h2
    constructor <;> nlinarith

section FiberMap

variable {E F U : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def mapTotal (f : E →L[ℝ] F) (C : ConvexBody (E × U)) : ConvexBody (F × U) :=
  mapBody (f.prodMap (ContinuousLinearMap.id ℝ U)) C

theorem projection_mapTotal (f : E →L[ℝ] F) (C : ConvexBody (E × U)) :
    ConvexFibers.projection (mapTotal f C) = ConvexFibers.projection C := by
  first
  | ext y
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hpy⟩
      exact ⟨p, hp, hpy⟩
    · rintro ⟨p, hp, hpy⟩
      exact ⟨(f p.1, p.2), ⟨p, hp, rfl⟩, hpy⟩

theorem fiberSet_mapTotal (f : E →L[ℝ] F) (C : ConvexBody (E × U)) (y : U) :
    ConvexFibers.fiberSet (mapTotal f C) y = f '' ConvexFibers.fiberSet C y := by
  first
  | ext x
    constructor
    · rintro ⟨⟨u, v⟩, huv, heq⟩
      have hv : v = y := congrArg Prod.snd heq
      subst v
      exact ⟨u, huv, congrArg Prod.fst heq⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u, y), hu, rfl⟩

theorem map_fiberBody (f : E →L[ℝ] F) (C : ConvexBody (E × U))
    {y : U} (hy : y ∈ ConvexFibers.projection C) :
    mapBody f (ConvexFibers.fiberBody C y) = ConvexFibers.fiberBody (mapTotal f C) y := by
  first
  | apply ConvexBody.ext
    have hy' : y ∈ ConvexFibers.projection (mapTotal f C) := by
      rwa [projection_mapTotal]
    rw [coe_mapBody, ConvexFibers.coe_fiberBody C hy,
      ConvexFibers.coe_fiberBody (mapTotal f C) hy', fiberSet_mapTotal]

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ U]
  [MeasureSpace F] [BorelSpace F] [MeasureSpace U] [BorelSpace U]
  [Measure.IsAddHaarMeasure (volume : Measure F)]
  [Measure.IsAddHaarMeasure (volume : Measure U)]

theorem integrable_image_fiberBody (f : E →L[ℝ] F) (C : ConvexBody (E × U)) :
    IntegrableOn (fun y => volume.real (f ''
      (ConvexFibers.fiberBody C y : Set E))) (ConvexFibers.projection C) := by
  first
  | apply (FiberVolume.integrable_fiber_realVolume (mapTotal f C)).integrableOn.congr_fun
      (hs := (ConvexFibers.projection_compact C).measurableSet)
    intro y hy
    dsimp only
    rw [ConvexFibers.coe_fiberBody C hy, fiberSet_mapTotal]

end FiberMap

theorem integral_pair_volume {k : ℕ}
    (T : Space 3 ≃L[ℝ] ProductThree)
    (f g : Plane →L[ℝ] Space 3)
    (hf : ∀ p, T (f p) = CrossPlaneVolume.firstPlane p)
    (hg : ∀ p, T (g p) = CrossPlaneVolume.secondPlane p)
    (F : ConvexBody (Plane × Space k)) (B : ConvexBody Plane)
    {r : ℝ} (hr : 0 ≤ r) :
    (∫ y in ConvexFibers.projection F,
      volume.real (mapBody f (ConvexFibers.fiberBody F y) + r • mapBody g B : Set (Space 3))) =
      (LinearFrame.volumeFactor T : ℝ) *
        ((∫ y in ConvexFibers.projection F, area (ConvexFibers.fiberBody F y)) * width B * r +
         (∫ y in ConvexFibers.projection F, width (ConvexFibers.fiberBody F y)) * area B * r ^ 2) := by
  first
  | have ha : IntegrableOn (fun y => area (ConvexFibers.fiberBody F y))
        (ConvexFibers.projection F) := by
      apply (FiberVolume.integrable_fiber_realVolume F).integrableOn.congr_fun
        (hs := (ConvexFibers.projection_compact F).measurableSet)
      intro y hy
      dsimp only
      rw [area, ConvexFibers.coe_fiberBody F hy]
    have hw : IntegrableOn (fun y => width (ConvexFibers.fiberBody F y))
        (ConvexFibers.projection F) :=
      integrable_image_fiberBody (ContinuousLinearMap.snd ℝ ℝ ℝ) F
    have hp (y : Space k) := pair_volume_smul T f g hf hg
      (ConvexFibers.fiberBody F y) B (a := 1) (b := r) (by norm_num) hr
    simp only [one_smul, one_pow, mul_one] at hp
    simp_rw [hp]
    rw [integral_const_mul, integral_add
      ((ha.mul_const (width B)).mul_const r)
      ((hw.mul_const (area B)).mul_const (r ^ 2))]
    simp only [integral_mul_const]

/-- The third finite difference is independent of the first body. This is an
identity of actual cubic volumes, derived from the verified multilinear expansion. -/
theorem third_difference (A B C : Body 3) :
    volume.real (A + (3 : ℝ) • B + (2 : ℝ) • C : Set (Space 3)) -
      2 * volume.real (A + (2 : ℝ) • B + (2 : ℝ) • C : Set (Space 3)) +
      volume.real (A + B + (2 : ℝ) • C : Set (Space 3)) -
      volume.real (A + (3 : ℝ) • B + C : Set (Space 3)) +
      2 * volume.real (A + (2 : ℝ) • B + C : Set (Space 3)) -
      volume.real (A + B + C : Set (Space 3)) = 6 * mixedVolume3 volume B B C := by
  first
  | have hd : finrank ℝ (Space 3) = 3 := by simp [Space]
    have h32 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 3) (c := 2) (by norm_num) (by norm_num) (by norm_num)
    have h22 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 2) (c := 2) (by norm_num) (by norm_num) (by norm_num)
    have h12 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 1) (c := 2) (by norm_num) (by norm_num) (by norm_num)
    have h31 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 3) (c := 1) (by norm_num) (by norm_num) (by norm_num)
    have h21 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 2) (c := 1) (by norm_num) (by norm_num) (by norm_num)
    have h11 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 1) (c := 1) (by norm_num) (by norm_num) (by norm_num)
    simp only [one_smul] at h32 h22 h12 h31 h21 h11
    rw [h32, h22, h12, h31, h21, h11]
    ring

def differenceGrid : Fin 6 → ℝ × ℝ := ![(3, 2), (2, 2), (1, 2), (3, 1), (2, 1), (1, 1)]
def differenceWeight : Fin 6 → ℝ := ![1, -2, 1, -1, 2, -1]

def fiberSumVolume {k : ℕ} (F : ConvexBody (Space 3 × Space k))
    (B C : Body 3) (b c : ℝ) (y : Space k) : ℝ :=
  volume.real (ConvexFibers.fiberBody F y + b • B + c • C : Set (Space 3))

theorem integrable_fiberSumVolume {k : ℕ} (F : ConvexBody (Space 3 × Space k))
    (B C : Body 3) (b c : ℝ) :
    IntegrableOn (fiberSumVolume F B C b c) (ConvexFibers.projection F) := by
  first
  | have h : IntegrableOn
        (fun y => volume.real (ConvexFibers.fiberSet
          (F + FiberVolume.embedBody (b • B + c • C)) y))
        (ConvexFibers.projection F) :=
      (FiberVolume.integrable_fiber_realVolume
        (F + FiberVolume.embedBody (b • B + c • C))).integrableOn
    apply h.congr_fun (hs := (ConvexFibers.projection_compact F).measurableSet)
    intro y hy
    have heq := FiberVolume.scaled_sum_fiber_volume F (b • B + c • C)
      (t := 1) (by norm_num) y
    rw [show (1 : ℝ) • F = F from one_smul ℝ F] at heq
    simpa only [one_smul, Set.indicator_of_mem hy, fiberSumVolume,
      ConvexBody.coe_add, ConvexBody.coe_smul, add_assoc] using heq

/-- Finite differences commute with the actual fiber integral. Every summand
is integrable because it is the fiber volume of an actual compact convex sum. -/
theorem integral_third_difference {k : ℕ}
    (F : ConvexBody (Space 3 × Space k)) (B C : Body 3) (J : ℝ) :
    (∑ i : Fin 6, differenceWeight i *
      (J * ∫ y in ConvexFibers.projection F,
        fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y)) =
      J * volume.real (ConvexFibers.projection F) * (6 * mixedVolume3 volume B B C) := by
  first
  | have hpoint (y : Space k) :
        (∑ i : Fin 6, differenceWeight i *
          fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y) =
            6 * mixedVolume3 volume B B C := by
      have h := third_difference (ConvexFibers.fiberBody F y) B C
      simp only [Fin.sum_univ_succ, differenceWeight, differenceGrid,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
        add_zero, one_mul, neg_mul, fiberSumVolume, one_smul] at ⊢
      linarith
    have hint : (∫ y in ConvexFibers.projection F,
        ∑ i : Fin 6, differenceWeight i *
          fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y) =
          volume.real (ConvexFibers.projection F) * (6 * mixedVolume3 volume B B C) := by
      simp_rw [hpoint]
      rw [setIntegral_const, smul_eq_mul]
    have hsum : (∫ y in ConvexFibers.projection F,
        ∑ i : Fin 6, differenceWeight i *
          fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y) =
        ∑ i : Fin 6, differenceWeight i *
          ∫ y in ConvexFibers.projection F,
            fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y := by
      rw [integral_finsetSum _ (fun i _ =>
        (integrable_fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2).const_mul _)]
      simp only [integral_const_mul]
    calc
      _ = J * (∑ i : Fin 6, differenceWeight i *
          ∫ y in ConvexFibers.projection F,
            fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← hsum, hint]; ring

end VolumePolynomials.CommonLineVolume
