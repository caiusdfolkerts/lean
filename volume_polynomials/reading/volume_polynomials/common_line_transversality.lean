module

public import VolumePolynomials.CommonLineVolume
public import VolumePolynomials.HigherLiftFiberFrame
public import Mathlib.Tactic.Positivity

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # The common-line obstruction, including averaged fibers in dimension zero

All six repeated coefficients are derived from the actual volume identity.
The two quantities contributed by the first body are its integrated planar
fiber area and its integrated transverse width. Each pair's positive Haar
factor occurs on both sides of the cyclic product, so the prescribed slice
with `0 < s < 1` cannot have a common line in its three planes.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.CommonLineCoordinates

open CommonLineVolume

def nextPlane : Fin 3 → Fin 3 := ![1, 2, 0]

theorem nextPlane_ne (i : Fin 3) : i ≠ nextPlane i := by
  first
  | fin_cases i <;> decide

def firstTwo : ProductThree →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ Plane).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane))

def Data.coordinate {P : Fin 3 → Submodule ℝ (Space 3)}
    (L : Data P) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hp : ∀ i j, i ≠ j → P i ⊔ P j = ⊤) (i : Fin 3) : Space 3 →L[ℝ] Plane :=
  firstTwo.comp (L.pairFrame (by simp [Space]) hP hp i (nextPlane i)
    (nextPlane_ne i)).toContinuousLinearMap

theorem Data.coordinate_planeMap {P : Fin 3 → Submodule ℝ (Space 3)}
    (L : Data P) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hp : ∀ i j, i ≠ j → P i ⊔ P j = ⊤) (i : Fin 3) (p : Plane) :
    L.coordinate hP hp i (L.planeMap i p) = p := by
  first
  | change firstTwo (L.pairFrame (by simp [Space]) hP hp i (nextPlane i)
      (nextPlane_ne i) (L.planeMap i p)) = p
    rw [L.pairFrame_left]
    rfl

theorem Data.planeMap_coordinate {P : Fin 3 → Submodule ℝ (Space 3)}
    (L : Data P) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hp : ∀ i j, i ≠ j → P i ⊔ P j = ⊤) (i : Fin 3)
    {x : Space 3} (hx : x ∈ P i) :
    L.planeMap i (L.coordinate hP hp i x) = x := by
  first
  | change x ∈ (P i : Set (Space 3)) at hx
    rw [← L.range_planeMap i] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [L.coordinate_planeMap]

theorem Data.body_reconstruction {P : Fin 3 → Submodule ℝ (Space 3)}
    (L : Data P) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hp : ∀ i j, i ≠ j → P i ⊔ P j = ⊤) (i : Fin 3)
    (K : Body 3) (hK : (K : Set (Space 3)) ⊆ P i) :
    mapBody (L.planeMap i) (mapBody (L.coordinate hP hp i) K) = K := by
  first
  | apply ConvexBody.ext
    change L.planeMap i '' (L.coordinate hP hp i '' (K : Set (Space 3))) = _
    rw [Set.image_image]
    calc
      _ = id '' (K : Set (Space 3)) :=
        Set.image_congr (fun x hx => L.planeMap_coordinate hP hp i (hK hx))
      _ = _ := Set.image_id' _

end VolumePolynomials.CommonLineCoordinates

namespace VolumePolynomials.HigherLift

open CommonLineVolume ConvexFibers FiberVolume

theorem FiberFrameData.integral_volume {k : ℕ} {α s z : ℝ}
    (D : FiberFrameData k α s z) {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    D.J * (∫ y in projection D.F, fiberSumVolume D.F D.B D.C b c y) =
      CubicSlice.value (correction k * α) s z ![1, b, c] := by
  first
  | have h := D.volume_identity ![1, b, c] (by
      intro i
      fin_cases i
      · norm_num
      · exact hb
      · exact hc)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, evaluate_coefficients,
      one_pow, one_smul, one_mul] at h
    have hf := realVolume_scaled_sum_of_pos D.F (b • D.B + c • D.C)
      (t := 1) (by norm_num)
    simp only [one_smul, one_pow, one_mul] at hf
    rw [hf] at h
    simpa only [fiberSumVolume, ConvexBody.coe_add, ConvexBody.coe_smul,
      add_assoc] using h

theorem FiberFrameData.pure_pair_coefficients {k : ℕ} {α s z : ℝ}
    (D : FiberFrameData k α s z) :
    D.J * volume.real (projection D.F) * (3 * mixedVolume3 volume D.B D.B D.C) = 3 ∧
    D.J * volume.real (projection D.F) * (3 * mixedVolume3 volume D.C D.C D.B) = 3 := by
  first
  | have hnonneg (i : Fin 6) : 0 ≤ (differenceGrid i).1 ∧ 0 ≤ (differenceGrid i).2 := by
      first
      | fin_cases i <;> norm_num [differenceGrid]
    have hnum : (∑ i : Fin 6, differenceWeight i *
        CubicSlice.value (correction k * α) s z
          ![1, (differenceGrid i).1, (differenceGrid i).2]) = 6 := by
      first
      | simp only [Fin.sum_univ_succ, differenceWeight, differenceGrid,
          Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Fin.sum_univ_zero, CubicSlice.value]
        ring
    have hnum' : (∑ i : Fin 6, differenceWeight i *
        CubicSlice.value (correction k * α) s z
          ![1, (differenceGrid i).2, (differenceGrid i).1]) = 6 := by
      first
      | simp only [Fin.sum_univ_succ, differenceWeight, differenceGrid,
          Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Fin.sum_univ_zero, CubicSlice.value]
        ring
    have hBC := integral_third_difference D.F D.B D.C D.J
    have hCB := integral_third_difference D.F D.C D.B D.J
    have hval (i : Fin 6) := D.integral_volume (hnonneg i).1 (hnonneg i).2
    simp_rw [hval] at hBC
    rw [hnum] at hBC
    have hval' (i : Fin 6) :
        D.J * (∫ y in projection D.F,
          fiberSumVolume D.F D.C D.B (differenceGrid i).1 (differenceGrid i).2 y) =
        CubicSlice.value (correction k * α) s z
          ![1, (differenceGrid i).2, (differenceGrid i).1] := by
      first
      | have h := D.integral_volume (hnonneg i).2 (hnonneg i).1
        convert h using 1
        congr 1
        apply setIntegral_congr_fun (projection_compact D.F).measurableSet
        intro y _
        unfold fiberSumVolume
        congr 1
        ac_rfl
    simp_rw [hval'] at hCB
    rw [hnum'] at hCB
    constructor <;> nlinarith

theorem FiberFrameData.transverse {k : ℕ} {α s z : ℝ}
    (D : FiberFrameData k α s z) (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1) :
    D.P 0 ⊓ D.P 1 ⊓ D.P 2 = ⊥ := by
  first
  | by_contra hcommon
    obtain ⟨L⟩ := CommonLineCoordinates.exists_data D.P D.planes hcommon
    let f (i : Fin 3) := L.planeMap i
    let c (i : Fin 3) := L.coordinate D.planes D.pair_spans i
    let A := mapTotal (c 0) D.F
    let B := mapBody (c 1) D.B
    let C := mapBody (c 2) D.C
    let T01 := L.pairFrame (by simp [Space]) D.planes D.pair_spans 0 1 (by decide)
    let T02 := L.pairFrame (by simp [Space]) D.planes D.pair_spans 0 2 (by decide)
    let T12 := L.pairFrame (by simp [Space]) D.planes D.pair_spans 1 2 (by decide)
    let j01 : ℝ := LinearFrame.volumeFactor T01
    let j02 : ℝ := LinearFrame.volumeFactor T02
    let j12 : ℝ := LinearFrame.volumeFactor T12
    let a : ℝ := ∫ y in projection A, area (fiberBody A y)
    let w : ℝ := ∫ y in projection A, width (fiberBody A y)
    let M : ℝ := volume.real (projection A)
    let β : ℝ := correction k * α
    have hβ : 0 < β := by
      first
      | apply mul_pos _ hα
        unfold correction
        positivity
    have hproj : projection A = projection D.F := projection_mapTotal (c 0) D.F
    have hA (y : Space k) (hy : y ∈ projection D.F) :
        mapBody (f 0) (fiberBody A y) = fiberBody D.F y := by
      first
      | rw [show fiberBody A y = mapBody (c 0) (fiberBody D.F y) from
          (map_fiberBody (c 0) D.F hy).symm]
        apply L.body_reconstruction D.planes D.pair_spans 0
        rw [coe_fiberBody D.F hy]
        exact D.fibers_in_plane y
    have hB : mapBody (f 1) B = D.B :=
      L.body_reconstruction D.planes D.pair_spans 1 D.B D.B_in_plane
    have hC : mapBody (f 2) C = D.C :=
      L.body_reconstruction D.planes D.pair_spans 2 D.C D.C_in_plane
    have h01l (p : Plane) : T01 (f 0 p) = CrossPlaneVolume.firstPlane p :=
      L.pairFrame_left (by simp [Space]) D.planes D.pair_spans 0 1 (by decide) p
    have h01r (p : Plane) : T01 (f 1 p) = CrossPlaneVolume.secondPlane p :=
      L.pairFrame_right (by simp [Space]) D.planes D.pair_spans 0 1 (by decide) p
    have h02l (p : Plane) : T02 (f 0 p) = CrossPlaneVolume.firstPlane p :=
      L.pairFrame_left (by simp [Space]) D.planes D.pair_spans 0 2 (by decide) p
    have h02r (p : Plane) : T02 (f 2 p) = CrossPlaneVolume.secondPlane p :=
      L.pairFrame_right (by simp [Space]) D.planes D.pair_spans 0 2 (by decide) p
    have h12l (p : Plane) : T12 (f 1 p) = CrossPlaneVolume.firstPlane p :=
      L.pairFrame_left (by simp [Space]) D.planes D.pair_spans 1 2 (by decide) p
    have h12r (p : Plane) : T12 (f 2 p) = CrossPlaneVolume.secondPlane p :=
      L.pairFrame_right (by simp [Space]) D.planes D.pair_spans 1 2 (by decide) p
    have hAB (r : ℝ) (hr : 0 ≤ r) :
        D.J * j01 * (a * width B * r + w * area B * r ^ 2) = 3 * β * r + 3 * r ^ 2 := by
      first
      | have hv := D.integral_volume hr (show (0 : ℝ) ≤ 0 by rfl)
        have heq : (∫ y in projection D.F, fiberSumVolume D.F D.B D.C r 0 y) =
            ∫ y in projection A,
              volume.real (mapBody (f 0) (fiberBody A y) + r • mapBody (f 1) B : Set (Space 3)) := by
          rw [hproj]
          apply setIntegral_congr_fun (projection_compact D.F).measurableSet
          intro y hy
          dsimp only
          rw [hA y hy, hB]
          change volume.real ((fiberBody D.F y + r • D.B + (0 : ℝ) • D.C : Body 3) :
            Set (Space 3)) =
            volume.real ((fiberBody D.F y + r • D.B : Body 3) : Set (Space 3))
          rw [body_zero_smul, add_zero]
        rw [heq, integral_pair_volume T01 (f 0) (f 1) h01l h01r A B hr] at hv
        change D.J * (j01 * (a * width B * r + w * area B * r ^ 2)) =
          CubicSlice.value β s z ![1, r, 0] at hv
        simpa [CubicSlice.value, mul_assoc] using hv
    have hAC (r : ℝ) (hr : 0 ≤ r) :
        D.J * j02 * (a * width C * r + w * area C * r ^ 2) = 3 * β * r + 3 * s * r ^ 2 := by
      first
      | have hv := D.integral_volume (show (0 : ℝ) ≤ 0 by rfl) hr
        have heq : (∫ y in projection D.F, fiberSumVolume D.F D.B D.C 0 r y) =
            ∫ y in projection A,
              volume.real (mapBody (f 0) (fiberBody A y) + r • mapBody (f 2) C : Set (Space 3)) := by
          rw [hproj]
          apply setIntegral_congr_fun (projection_compact D.F).measurableSet
          intro y hy
          dsimp only
          rw [hA y hy, hC]
          change volume.real ((fiberBody D.F y + (0 : ℝ) • D.B + r • D.C : Body 3) :
            Set (Space 3)) =
            volume.real ((fiberBody D.F y + r • D.C : Body 3) : Set (Space 3))
          rw [body_zero_smul, add_zero]
        rw [heq, integral_pair_volume T02 (f 0) (f 2) h02l h02r A C hr] at hv
        change D.J * (j02 * (a * width C * r + w * area C * r ^ 2)) =
          CubicSlice.value β s z ![1, 0, r] at hv
        simpa [CubicSlice.value, mul_assoc] using hv
    have hab1 := hAB 1 (by norm_num)
    have hab2 := hAB 2 (by norm_num)
    have hac1 := hAC 1 (by norm_num)
    have hac2 := hAC 2 (by norm_num)
    have hAAB : D.J * j01 * a * width B = 3 * β := by nlinarith
    have hABB : D.J * j01 * w * area B = 3 := by nlinarith
    have hAAC : D.J * j02 * a * width C = 3 * β := by nlinarith
    have hACC : D.J * j02 * w * area C = 3 * s := by nlinarith
    have hp := pair_repeated_coefficients T12 (f 1) (f 2) h12l h12r B C
    have hm := D.pure_pair_coefficients
    rw [← hB, ← hC] at hm
    have hBBC : D.J * M * j12 * area B * width C = 3 := by
      first
      | have h := hm.1
        rw [hp.1] at h
        simpa only [M, hproj, j12, mul_assoc] using h
    have hBCC : D.J * M * j12 * width B * area C = 3 := by
      first
      | have h := hm.2
        rw [hp.2] at h
        simpa only [M, hproj, j12, mul_assoc] using h
    have hcyclic :
        (D.J * j01 * a * width B) * (D.J * M * j12 * area B * width C) *
          (D.J * j02 * w * area C) =
        (D.J * j02 * a * width C) * (D.J * j01 * w * area B) *
          (D.J * M * j12 * width B * area C) := by ring
    rw [hAAB, hBBC, hACC, hAAC, hABB, hBCC] at hcyclic
    have hprod : (27 * β) * (s - 1) = 0 := by nlinarith [hcyclic]
    have hsEq : s - 1 = 0 := (mul_eq_zero.mp hprod).resolve_left (by positivity)
    linarith

end VolumePolynomials.HigherLift
