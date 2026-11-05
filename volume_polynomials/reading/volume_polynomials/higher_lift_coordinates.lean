module

public import VolumePolynomials.HigherLiftFiberFrame
public import VolumePolynomials.PlaneCoordinates
public import VolumePolynomials.PlanarCubicVolume

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# From independent planes to the literal planar integral

The first coordinate of the three-dimensional frame is the `z` coordinate.
Dropping that coordinate on the first body's fibers gives an actual compact
convex total set in `Plane × Space k`. Fubini transports the original
volume identity, retaining the positive Haar factor of the plane frame.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

open ConvexFibers FiberVolume PlanarExtrusion

def planarTotalMap (k : ℕ)
    (S : Space 3 ≃L[ℝ] PlanarInteraction.Space) :
    (Space 3 × Space k) →L[ℝ] (Plane × Space k) :=
  ((ContinuousLinearMap.snd ℝ ℝ Plane).comp S.toContinuousLinearMap).prodMap
    (ContinuousLinearMap.id ℝ (Space k))

@[simp] theorem planarTotalMap_apply (k : ℕ)
    (S : Space 3 ≃L[ℝ] PlanarInteraction.Space) (p : Space 3 × Space k) :
    planarTotalMap k S p = ((S p.1).2, p.2) := rfl

def extractYZ : PlanarInteraction.Space →L[ℝ] Plane :=
  ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane)).prod
    (ContinuousLinearMap.fst ℝ ℝ Plane)

def extractXZ : PlanarInteraction.Space →L[ℝ] Plane :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane)).prod
    (ContinuousLinearMap.fst ℝ ℝ Plane)

@[simp] theorem extractYZ_apply (p : PlanarInteraction.Space) : extractYZ p = (p.2.2, p.1) := rfl
@[simp] theorem extractXZ_apply (p : PlanarInteraction.Space) : extractXZ p = (p.2.1, p.1) := rfl

theorem projection_planarTotal {k : ℕ}
    (S : Space 3 ≃L[ℝ] PlanarInteraction.Space) (F : ConvexBody (Space 3 × Space k)) :
    projection (mapBody (planarTotalMap k S) F) = projection F := by
  first
  | ext y
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hpy⟩
      exact ⟨p, hp, hpy⟩
    · rintro ⟨p, hp, hpy⟩
      exact ⟨planarTotalMap k S p, ⟨p, hp, rfl⟩, hpy⟩

theorem map_fiberBody_planarTotal {k : ℕ}
    (S : Space 3 ≃L[ℝ] PlanarInteraction.Space) (F : ConvexBody (Space 3 × Space k))
    (hflat : ∀ p ∈ F, (S p.1).1 = 0) {y : Space k} (hy : y ∈ projection F) :
    mapBody S.toContinuousLinearMap (fiberBody F y) =
      mapBody PlanarInteraction.embedXY (fiberBody (mapBody (planarTotalMap k S) F) y) := by
  first
  | have hy' : y ∈ projection (mapBody (planarTotalMap k S) F) := by
      first
      | rwa [projection_planarTotal]
    apply ConvexBody.ext
    rw [coe_mapBody, coe_mapBody, coe_fiberBody F hy,
      coe_fiberBody (mapBody (planarTotalMap k S) F) hy']
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(S x).2, ?_, ?_⟩
      · exact ⟨(x, y), hx, rfl⟩
      · apply Prod.ext
        · exact (hflat (x, y) hx).symm
        · rfl
    · rintro ⟨x, ⟨⟨p, u⟩, hpu, hmap⟩, rfl⟩
      have hu : u = y := congrArg Prod.snd hmap
      subst u
      refine ⟨p, hpu, ?_⟩
      apply Prod.ext
      · exact hflat (p, y) hpu
      · exact congrArg Prod.fst hmap

theorem map_body_YZ (S : Space 3 ≃L[ℝ] PlanarInteraction.Space)
    (B : Body 3) (hB : ∀ x ∈ B, (S x).2.1 = 0) :
    mapBody S.toContinuousLinearMap B =
      mapBody PlanarInteraction.embedYZ (mapBody (extractYZ.comp S.toContinuousLinearMap) B) := by
  first
  | apply ConvexBody.ext
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨extractYZ (S x), ⟨x, hx, rfl⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact Prod.ext (hB x hx).symm rfl
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      apply Prod.ext
      · rfl
      · exact Prod.ext (hB x hx) rfl

theorem map_body_XZ (S : Space 3 ≃L[ℝ] PlanarInteraction.Space)
    (C : Body 3) (hC : ∀ x ∈ C, (S x).2.2 = 0) :
    mapBody S.toContinuousLinearMap C =
      mapBody PlanarInteraction.embedXZ (mapBody (extractXZ.comp S.toContinuousLinearMap) C) := by
  first
  | apply ConvexBody.ext
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨extractXZ (S x), ⟨x, hx, rfl⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact Prod.ext rfl (hC x hx).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      apply Prod.ext
      · rfl
      · exact Prod.ext rfl (hC x hx)

structure CoordinateFiberData (k : ℕ) (α s z : ℝ) where
  F : ConvexBody (Plane × Space k)
  B : ConvexBody Plane
  C : ConvexBody Plane
  J : ℝ
  J_pos : 0 < J
  projection_pos : 0 < volume.real (projection F)
  integral_identity : ∀ t : Fin 3 → ℝ, (∀ i, 0 < t i) →
    J * (∫ y in projection F, PlanarInteraction.coordinateVolume (fiberBody F y) B C t) =
      CubicSlice.value (correction k * α) s z t

theorem FiberFrameData.exists_coordinateFiberData {k : ℕ} {α s z : ℝ}
    (D : FiberFrameData k α s z) (htrans : D.P 0 ⊓ D.P 1 ⊓ D.P 2 = ⊥) :
    Nonempty (CoordinateFiberData k α s z) := by
  first
  | classical
    obtain ⟨T, hT⟩ := PlaneCoordinates.exists_plane_coordinates
      (by simp [Space] : finrank ℝ (Space 3) = 3) D.P D.planes htrans
    let S : Space 3 ≃L[ℝ] PlanarInteraction.Space := T.trans PlanarInteraction.coordinateEquiv
    have hS0 (x : Space 3) : x ∈ D.P 0 ↔ (S x).1 = 0 := by
      first
      | change x ∈ D.P 0 ↔ T x 0 = 0
        exact hT 0 x
    have hS1 (x : Space 3) : x ∈ D.P 1 ↔ (S x).2.1 = 0 := by
      first
      | change x ∈ D.P 1 ↔ T x 1 = 0
        exact hT 1 x
    have hS2 (x : Space 3) : x ∈ D.P 2 ↔ (S x).2.2 = 0 := by
      first
      | change x ∈ D.P 2 ↔ T x 2 = 0
        exact hT 2 x
    let F := mapBody (planarTotalMap k S) D.F
    let B := mapBody (extractYZ.comp S.toContinuousLinearMap) D.B
    let C := mapBody (extractXZ.comp S.toContinuousLinearMap) D.C
    let j : ℝ := LinearFrame.volumeFactor S
    have hj : 0 < j := by exact_mod_cast LinearFrame.volumeFactor_pos S
    have hflat (p : Space 3 × Space k) (hp : p ∈ D.F) : (S p.1).1 = 0 :=
      (hS0 p.1).mp (D.fibers_in_plane p.2 hp)
    have hB := map_body_YZ S D.B (fun x hx => (hS1 x).mp (D.B_in_plane hx))
    have hC := map_body_XZ S D.C (fun x hx => (hS2 x).mp (D.C_in_plane hx))
    have hproj : projection F = projection D.F := projection_planarTotal S D.F
    refine ⟨⟨F, B, C, D.J * j, mul_pos D.J_pos hj, ?_, ?_⟩⟩
    · rw [hproj]
      exact D.projection_pos
    · intro t ht
      have hvol := D.volume_identity t (fun i => (ht i).le)
      rw [realVolume_scaled_sum_of_pos D.F (t 1 • D.B + t 2 • D.C) (ht 0),
        evaluate_coefficients] at hvol
      have hkdim : finrank ℝ (Space k) = k := by simp [Space]
      rw [hkdim] at hvol
      have hfiber (y : Space k) (hy : y ∈ projection D.F) :
          volume.real (t 0 • fiberBody D.F y + (t 1 • D.B + t 2 • D.C) : Set (Space 3)) =
            j * PlanarInteraction.coordinateVolume (fiberBody F y) B C t := by
        first
        | have hm := LinearFrame.realVolume_eq_factor_mul_image S
            (t 0 • fiberBody D.F y + (t 1 • D.B + t 2 • D.C) : Set (Space 3))
          have hsum : mapBody S.toContinuousLinearMap
              (t 0 • fiberBody D.F y + (t 1 • D.B + t 2 • D.C)) =
              t 0 • mapBody PlanarInteraction.embedXY (fiberBody F y) +
                t 1 • mapBody PlanarInteraction.embedYZ B + t 2 • mapBody PlanarInteraction.embedXZ C := by
            rw [mapBody_add, mapBody_add, mapBody_smul, mapBody_smul, mapBody_smul,
              map_fiberBody_planarTotal S D.F hflat hy, hB, hC, ← add_assoc]
          have heq := congrArg (fun Q : ConvexBody PlanarInteraction.Space => volume.real (Q : Set PlanarInteraction.Space)) hsum
          exact hm.trans (congrArg (fun x : ℝ => j * x) heq)
      have hint : (∫ y in projection D.F, volume.real
          (t 0 • fiberBody D.F y + (t 1 • D.B + t 2 • D.C) : Set (Space 3))) =
          j * (∫ y in projection F, PlanarInteraction.coordinateVolume (fiberBody F y) B C t) := by
        first
        | rw [hproj, ← integral_const_mul]
          apply setIntegral_congr_fun (projection_compact D.F).measurableSet
          exact hfiber
      simp only [ConvexBody.coe_add, ConvexBody.coe_smul] at hvol
      rw [hint] at hvol
      apply mul_left_cancel₀ (pow_ne_zero k (ht 0).ne')
      calc
        t 0 ^ k * (D.J * j * _) = D.J * (t 0 ^ k * (j * _)) := by ring
        _ = _ := hvol

end VolumePolynomials.HigherLift
