module

public import VolumePolynomials.HigherLiftFrame
public import VolumePolynomials.BodySubspaceCoordinates

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The actual fiber frame of an arbitrary lifted realization

The planes, total fiber body, quotient measure, and positive Jacobian are
constructed from the realizing tuple. The volume identity is a transported
identity of the original bodies, before any independence of the three
planes is proved.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

open ConvexFibers FiberVolume

structure FiberFrameData (k : ℕ) (α s z : ℝ) where
  F : ConvexBody (Space 3 × Space k)
  B : Body 3
  C : Body 3
  J : ℝ
  J_pos : 0 < J
  P : Fin 3 → Submodule ℝ (Space 3)
  planes : ∀ i, finrank ℝ (P i) = 2
  pair_spans : ∀ i j, i ≠ j → P i ⊔ P j = ⊤
  fibers_in_plane : ∀ y, fiberSet F y ⊆ P 0
  B_in_plane : (B : Set (Space 3)) ⊆ P 1
  C_in_plane : (C : Set (Space 3)) ⊆ P 2
  projection_pos : 0 < volume.real (projection F)
  volume_identity : ∀ t : Fin 3 → ℝ, (∀ i, 0 ≤ t i) →
    J * volume.real ((t 0 • F + embedBody (U := Space k) (t 1 • B + t 2 • C) :
      ConvexBody (Space 3 × Space k)) : Set (Space 3 × Space k)) =
      evaluate (coefficients k α s z) t

theorem sectionPlane_finrank_of_le {k : ℕ}
    (V W : Submodule ℝ (Space (3 + k))) (hVW : V ≤ W)
    (hdW : finrank ℝ W = 3) (hdV : finrank ℝ V = 2) :
    finrank ℝ (sectionPlane V W hdW) = 2 := by
  first
  | apply sectionPlane_finrank
    exact (congrArg (fun S : Submodule ℝ (Space (3 + k)) => finrank ℝ S)
      (inf_eq_left.mpr hVW)).trans hdV

theorem sectionPlane_sup_eq_top {k : ℕ}
    (H V W : Submodule ℝ (Space (3 + k))) (hVW : V ≤ W)
    (hspan : W ≤ H ⊔ V) (hdW : finrank ℝ W = 3) :
    sectionPlane H W hdW ⊔ sectionPlane V W hdW = ⊤ := by
  first
  | apply top_unique
    intro x _
    let w : W := (threeFrameLeft W hdW).symm x
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (hspan w.property)
    have huW : u ∈ W := by
      first
      | have heq : u = (w : Space (3 + k)) - v := by rw [← huv]; abel
        rw [heq]
        exact W.sub_mem w.property (hVW hv)
    let u' : W := ⟨u, huW⟩
    let v' : W := ⟨v, hVW hv⟩
    apply Submodule.mem_sup.mpr
    refine ⟨threeFrameLeft W hdW u', ⟨u', hu, rfl⟩,
      threeFrameLeft W hdW v', ⟨v', hv, rfl⟩, ?_⟩
    rw [← map_add]
    have heq : u' + v' = w := Subtype.ext huv
    rw [heq]
    exact (threeFrameLeft W hdW).apply_symm_apply x

theorem coordinate_body_in_plane {k : ℕ}
    (V W U : Submodule ℝ (Space (3 + k))) (hVW : V ≤ W)
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k)
    (K : Body (3 + k)) (hKV : (K : Set (Space (3 + k))) ⊆ V) :
    (mapBody (ContinuousLinearMap.fst ℝ (Space 3) (Space k))
      (mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap K) : Set (Space 3)) ⊆
      sectionPlane V W hdW := by
  first
  | rintro x ⟨_, ⟨p, hp, rfl⟩, hpx⟩
    refine ⟨(⟨p, hVW (hKV hp)⟩ : W), hKV hp, ?_⟩
    have ht := congrArg Prod.fst
      (threeFrame_on_left W U hWU hdW hdU ⟨p, hVW (hKV hp)⟩)
    exact ht.symm.trans hpx

theorem threeFrame_projection_positive {k : ℕ}
    (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k)
    (A B : Body (3 + k)) (hA0 : (0 : Space (3 + k)) ∈ A)
    (hBW : (B : Set (Space (3 + k))) ⊆ W)
    (hfull : linearHull (A + B) = ⊤) :
    0 < volume.real (projection (mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap A)) := by
  first
  | let T := threeFrame W U hWU hdW hdU
    let snd := ContinuousLinearMap.snd ℝ (Space 3) (Space k)
    let F := mapBody T.toContinuousLinearMap A
    let Z := mapBody snd F
    have hfullT := SubspaceCoordinates.linearHull_map_eq_top T.toContinuousLinearMap T.surjective
      (A + B) hfull
    have hfullZ := SubspaceCoordinates.linearHull_map_eq_top snd
      (show Function.Surjective snd from fun y => ⟨(0, y), rfl⟩)
      (mapBody T.toContinuousLinearMap (A + B)) hfullT
    have hmapB : mapBody snd (mapBody T.toContinuousLinearMap B) = 0 := by
      first
      | rw [frame_body_in_threeSpace W U hWU hdW hdU B hBW]
        exact FiberGrowth.map_snd_embedBody _
    rw [mapBody_add, mapBody_add, hmapB, add_zero] at hfullZ
    have hZ0 : (0 : Space k) ∈ Z := ⟨0, ⟨0, hA0, map_zero _⟩, map_zero _⟩
    have hp := (bodyVolume_pos_iff_linearHull_eq_top hZ0).mpr hfullZ
    exact hp

theorem exists_fiberFrameData {k : ℕ} {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) :
    Nonempty (FiberFrameData k α s z) := by
  first
  | classical
    choose p hp using fun i => (K i).nonempty
    let L : Fin 3 → Body (3 + k) := fun i => translateBody (-p i) (K i)
    have hL : Realizes L (coefficients k α s z) := hK.translate (fun i => -p i)
    have h0 (i : Fin 3) : (0 : Space (3 + k)) ∈ L i := zero_mem_translateBody_neg (hp i)
    obtain ⟨hdH, hdB, hdC, hdW, hHB, hHC⟩ := centered_dimensions hα hs hL h0
    obtain ⟨U, hUH, hWU, hdU, hdE, hsplit⟩ := lifted_subspaces hα hs hL h0
    let H := linearHull (L 0)
    let W := linearHull (L 1) ⊔ linearHull (L 2)
    let T := threeFrame W U hWU hdW hdU
    let F := mapBody T.toContinuousLinearMap (L 0)
    let B := mapBody (ContinuousLinearMap.fst ℝ (Space 3) (Space k))
      (mapBody T.toContinuousLinearMap (L 1))
    let C := mapBody (ContinuousLinearMap.fst ℝ (Space 3) (Space k))
      (mapBody T.toContinuousLinearMap (L 2))
    let P : Fin 3 → Submodule ℝ (Space 3) :=
      ![sectionPlane H W hdW, sectionPlane (linearHull (L 1)) W hdW,
        sectionPlane (linearHull (L 2)) W hdW]
    have hBW : (L 1 : Set (Space (3 + k))) ⊆ W :=
      fun _ hx => (le_sup_left : linearHull (L 1) ≤ W) (mem_linearHull hx)
    have hCW : (L 2 : Set (Space (3 + k))) ⊆ W :=
      fun _ hx => (le_sup_right : linearHull (L 2) ≤ W) (mem_linearHull hx)
    have hBembed : mapBody T.toContinuousLinearMap (L 1) = embedBody B :=
      frame_body_in_threeSpace W U hWU hdW hdU (L 1) hBW
    have hCembed : mapBody T.toContinuousLinearMap (L 2) = embedBody C :=
      frame_body_in_threeSpace W U hWU hdW hdU (L 2) hCW
    refine ⟨⟨F, B, C, LinearFrame.volumeFactor T, ?_, P, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact_mod_cast LinearFrame.volumeFactor_pos T
    · intro i
      fin_cases i
      · exact sectionPlane_finrank H W hdW hdE
      · exact sectionPlane_finrank_of_le (linearHull (L 1)) W le_sup_left hdW hdB
      · exact sectionPlane_finrank_of_le (linearHull (L 2)) W le_sup_right hdW hdC
    · have h01 : P 0 ⊔ P 1 = ⊤ := by
        first
        | apply sectionPlane_sup_eq_top H (linearHull (L 1)) W le_sup_left _ hdW
          change W ≤ linearHull (L 0) ⊔ linearHull (L 1)
          rw [hHB]
          exact le_top
      have h02 : P 0 ⊔ P 2 = ⊤ := by
        first
        | apply sectionPlane_sup_eq_top H (linearHull (L 2)) W le_sup_right _ hdW
          change W ≤ linearHull (L 0) ⊔ linearHull (L 2)
          rw [hHC]
          exact le_top
      have h12 : P 1 ⊔ P 2 = ⊤ :=
        sectionPlane_sup_eq_top (linearHull (L 1)) (linearHull (L 2)) W le_sup_right le_rfl hdW
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first | exact (hij rfl).elim | exact h01 | exact h02 | exact h12 |
        exact (sup_comm _ _).trans h01 | exact (sup_comm _ _).trans h02 |
        exact (sup_comm _ _).trans h12
    · intro y
      exact frame_fiber_subset_plane H W U hWU hUH hdW hdU (L 0)
        (fun _ hx => mem_linearHull hx) y
    · exact coordinate_body_in_plane (linearHull (L 1)) W U le_sup_left hWU hdW hdU
        (L 1) (fun _ hx => mem_linearHull hx)
    · exact coordinate_body_in_plane (linearHull (L 2)) W U le_sup_right hWU hdW hdU
        (L 2) (fun _ hx => mem_linearHull hx)
    · apply threeFrame_projection_positive W U hWU hdW hdU (L 0) (L 1) (h0 0) hBW
      rw [linearHull_add (h0 0) (h0 1)]
      exact hHB
    · intro t ht
      have hsum : mapBody T.toContinuousLinearMap (weightedSum L t) =
          t 0 • F + embedBody (t 1 • B + t 2 • C) := by
        first
        | simp only [weightedSum, Fin.sum_univ_three, mapBody_add, mapBody_smul,
            hBembed, hCembed, embedBody, mapBody_add, mapBody_smul]
          exact add_assoc _ _ _
      have hv := LinearFrame.realVolume_eq_factor_mul_image T
        (weightedSum L t : Set (Space (3 + k)))
      have heq : volume.real (T '' (weightedSum L t : Set (Space (3 + k)))) =
          volume.real ((t 0 • F + embedBody (U := Space k) (t 1 • B + t 2 • C) :
            ConvexBody (Space 3 × Space k)) : Set (Space 3 × Space k)) := by
        first
        | exact congrArg (fun S : ConvexBody (Space 3 × Space k) =>
            volume.real (S : Set (Space 3 × Space k))) hsum
      rw [heq] at hv
      exact hv.symm.trans (hL t ht).symm

end VolumePolynomials.HigherLift
