module

public import VolumePolynomials.HigherLiftCoefficients
public import VolumePolynomials.SimplexCone
public import VolumePolynomials.FiberVolume
public import VolumePolynomials.RealizationCone
public import VolumePolynomials.LinearFrame
public import Mathlib.Topology.Algebra.Module.Equiv.Pi

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The converse in the higher-dimensional lifting proposition

An arbitrary realization of the cubic slice is lifted by the actual cone
over a simplex. Fubini and its proved first two height moments produce
exactly `X₁^k P_{cₖ α,s,z}`. A positive Haar factor accounts for the chosen
coordinate equivalence and is removed by a common dilation.
-/

open Set MeasureTheory MvPolynomial
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

open SimplexCoordinates SimplexCone ConvexFibers FiberVolume

def rawTuple (k : ℕ) (K : Fin 3 → Body 3) :
    Fin 3 → ConvexBody (Space 3 × Space k) :=
  ![coneBody (K 0) k, embedBody (K 1), embedBody (K 2)]

theorem raw_sum (k : ℕ) (K : Fin 3 → Body 3) (t : Fin 3 → ℝ) :
    (∑ i, t i • rawTuple k K i) =
      t 0 • coneBody (K 0) k + embedBody (t 1 • K 1 + t 2 • K 2) := by
  first
  | simp only [rawTuple, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      embedBody, mapBody_add, mapBody_smul, add_assoc]

theorem integrated_cubic {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (CubicSlice.coefficients α s z))
    (k : ℕ) (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∫ y in simplex k, bodyVolume
      ((t 0 * coneHeight y) • K 0 + t 1 • K 1 + t 2 • K 2)) =
      volume.real (simplex k) * CubicSlice.value (correction k * α) s z t := by
  first
  | let a₂ : ℝ := 3 * α * t 0 ^ 2 * t 1 + 3 * α * t 0 ^ 2 * t 2
    let a₁ : ℝ := 3 * t 0 * t 1 ^ 2 + 3 * s * t 0 * t 2 ^ 2 +
      6 * z * t 0 * t 1 * t 2
    let a₀ : ℝ := 3 * t 1 ^ 2 * t 2 + 3 * t 1 * t 2 ^ 2
    have heval (y : Space k) (hy : y ∈ simplex k) :
        bodyVolume ((t 0 * coneHeight y) • K 0 + t 1 • K 1 + t 2 • K 2) =
          a₂ * coneHeight y ^ 2 + a₁ * coneHeight y + a₀ := by
      first
      | have h := (CubicSlice.realizes_iff α s z K).mp hK
          ![t 0 * coneHeight y, t 1, t 2] (by
            intro i
            fin_cases i
            · exact mul_nonneg (ht 0) (coneHeight_nonnegative hy)
            · exact ht 1
            · exact ht 2)
        simp only [volumeFunction, weightedSum, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] at h
        rw [h]
        dsimp only [CubicSlice.value, a₂, a₁, a₀]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        ring
    have hρ : IntegrableOn (coneHeight : Space k → ℝ) (simplex k) :=
      (continuous_coneHeight k).continuousOn.integrableOn_compact (simplex_compact k)
    have hρ₂ : IntegrableOn (fun y : Space k => coneHeight y ^ 2) (simplex k) :=
      ((continuous_coneHeight k).pow 2).continuousOn.integrableOn_compact (simplex_compact k)
    have hconst : IntegrableOn (fun _ : Space k => a₀) (simplex k) :=
      integrableOn_const (simplex_compact k).measure_ne_top
    calc
      _ = ∫ y in simplex k, a₂ * coneHeight y ^ 2 + a₁ * coneHeight y + a₀ := by
        first
        | apply setIntegral_congr_fun (simplex_compact k).measurableSet
          exact heval
      _ = a₂ * (∫ y in simplex k, coneHeight y ^ 2) +
          a₁ * (∫ y in simplex k, coneHeight y) + a₀ * volume.real (simplex k) := by
        first
        | rw [integral_add
            (f := fun y : Space k => a₂ * coneHeight y ^ 2 + a₁ * coneHeight y)
            (g := fun _ : Space k => a₀)
            ((hρ₂.const_mul a₂).add (hρ.const_mul a₁)) hconst,
            integral_add (f := fun y : Space k => a₂ * coneHeight y ^ 2)
              (g := fun y : Space k => a₁ * coneHeight y)
              (hρ₂.const_mul a₂) (hρ.const_mul a₁),
            integral_const_mul, integral_const_mul, setIntegral_const]
          simp only [smul_eq_mul, mul_comm a₀]
      _ = _ := by
        first
        | rw [integral_coneHeight_sq, integral_coneHeight]
          dsimp only [a₂, a₁, a₀, CubicSlice.value, correction]
          ring

/-- The full volume identity before the harmless common dilation. -/
theorem raw_volume {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (CubicSlice.coefficients α s z))
    {k : ℕ} (hk : 0 < k) (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    volume.real ((∑ i, t i • rawTuple k K i : ConvexBody (Space 3 × Space k)) : Set (Space 3 × Space k)) =
      volume.real (simplex k) * evaluate (coefficients k α s z) t := by
  first
  | rw [raw_sum, realVolume_scaled_sum (by simpa [Space] using hk)
      (coneBody (K 0) k) (t 1 • K 1 + t 2 • K 2) (ht 0), cone_projection]
    have hinner : (∫ y in simplex k, volume.real
        ((t 0 • fiberBody (coneBody (K 0) k) y +
          (t 1 • K 1 + t 2 • K 2) : Body 3) : Set (Space 3))) =
        ∫ y in simplex k, bodyVolume
          ((t 0 * coneHeight y) • K 0 + t 1 • K 1 + t 2 • K 2) := by
      first
      | apply setIntegral_congr_fun (simplex_compact k).measurableSet
        intro y hy
        dsimp only
        rw [cone_fiberBody (K 0) k hy, smul_smul, ← add_assoc]
        rfl
    rw [hinner, integrated_cubic hK k t ht, evaluate_coefficients]
    simp only [Space, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    ring

def productLinearEquiv (k : ℕ) : (Space 3 × Space k) ≃ₗ[ℝ] Space (3 + k) where
  toFun p := Fin.addCases p.1 p.2
  invFun x := (fun i => x (Fin.castAdd k i), fun j => x (Fin.natAdd 3 j))
  left_inv p := by ext <;> simp
  right_inv x := by
    first
    | funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp
      · intro j; simp
  map_add' p q := by
    first
    | funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp
      · intro j; simp
  map_smul' r p := by
    first
    | funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp
      · intro j; simp

def productEquiv (k : ℕ) : (Space 3 × Space k) ≃L[ℝ] Space (3 + k) :=
  (productLinearEquiv k).toContinuousLinearEquiv

def rawScale (k : ℕ) : ℝ :=
  volume.real (simplex k) / (LinearFrame.volumeFactor (productEquiv k) : ℝ)

theorem rawScale_pos (k : ℕ) : 0 < rawScale k :=
  div_pos (simplex_volume_pos k) (by exact_mod_cast LinearFrame.volumeFactor_pos (productEquiv k))

def coordinateTuple (k : ℕ) (K : Fin 3 → Body 3) : Fin 3 → Body (3 + k) :=
  fun i => mapBody (productEquiv k).toContinuousLinearMap (rawTuple k K i)

theorem coordinate_realizes {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (CubicSlice.coefficients α s z)) {k : ℕ} (hk : 0 < k) :
    Realizes (coordinateTuple k K) (rawScale k • coefficients k α s z) := by
  first
  | intro t ht
    rw [evaluate_smul]
    have hsum : weightedSum (coordinateTuple k K) t =
        mapBody (productEquiv k).toContinuousLinearMap (∑ i, t i • rawTuple k K i) := by
      first
      | rw [show mapBody (productEquiv k).toContinuousLinearMap (∑ i, t i • rawTuple k K i) =
            ∑ i, mapBody (productEquiv k).toContinuousLinearMap (t i • rawTuple k K i) from
          map_sum (mapBodyHom (productEquiv k).toContinuousLinearMap) _ _]
        simp only [weightedSum, coordinateTuple, mapBody_smul]
    have hmeasure := LinearFrame.realVolume_eq_factor_mul_image (productEquiv k)
      ((∑ i, t i • rawTuple k K i : ConvexBody (Space 3 × Space k)) : Set (Space 3 × Space k))
    rw [raw_volume hK hk t ht] at hmeasure
    rw [volumeFunction, hsum]
    change rawScale k * evaluate (coefficients k α s z) t =
      volume.real (productEquiv k '' ((∑ i, t i • rawTuple k K i : ConvexBody _) : Set _))
    have hf : (LinearFrame.volumeFactor (productEquiv k) : ℝ) ≠ 0 :=
      (show 0 < (LinearFrame.volumeFactor (productEquiv k) : ℝ) by
        exact_mod_cast LinearFrame.volumeFactor_pos (productEquiv k)).ne'
    unfold rawScale
    field_simp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hmeasure

def dilation (k : ℕ) : ℝ := (rawScale k)⁻¹ ^ (((3 + k : ℕ) : ℝ)⁻¹)

def liftedTuple (k : ℕ) (K : Fin 3 → Body 3) : Fin 3 → Body (3 + k) :=
  fun i => dilation k • coordinateTuple k K i

/-- Every cubic realization lifts, without restrictions on its shape or
on the parameters beyond the original realization itself. -/
theorem lifted_realizes {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (CubicSlice.coefficients α s z)) {k : ℕ} (hk : 0 < k) :
    Realizes (liftedTuple k K) (coefficients k α s z) := by
  first
  | have hr : 0 ≤ dilation k := Real.rpow_nonneg (inv_pos.mpr (rawScale_pos k)).le _
    have hpow : dilation k ^ (3 + k) = (rawScale k)⁻¹ := by
      first
      | exact Real.rpow_inv_natCast_pow (inv_pos.mpr (rawScale_pos k)).le (by omega)
    have h := (coordinate_realizes hK hk).dilate hr
    rw [hpow, smul_smul, inv_mul_cancel₀ (rawScale_pos k).ne', one_smul] at h
    exact h

theorem mem_volumeLocus_of_cubic {α s z : ℝ}
    (h : CubicSlice.coefficients α s z ∈ VolumeLocus 3 3) {k : ℕ} (hk : 0 < k) :
    coefficients k α s z ∈ VolumeLocus 3 (3 + k) := by
  first
  | obtain ⟨K, hK⟩ := h
    exact ⟨liftedTuple k K, lifted_realizes hK hk⟩

/-- Finite convex hulls remain finite convex hulls through the construction. -/
theorem lifted_finiteHull (k : ℕ) (K : Fin 3 → Body 3)
    (hK : ∀ i, PolytopeGeometry.IsFiniteHull (K i : Set (Space 3))) (i : Fin 3) :
    PolytopeGeometry.IsFiniteHull (liftedTuple k K i : Set (Space (3 + k))) := by
  first
  | apply PolytopeGeometry.IsFiniteHull.smul
    apply PolytopeGeometry.IsFiniteHull.linear_image
    fin_cases i
    · exact cone_finiteHull (K 0) k (hK 0)
    · exact (hK 1).linear_image (ContinuousLinearMap.inl ℝ (Space 3) (Space k)).toLinearMap
    · exact (hK 2).linear_image (ContinuousLinearMap.inl ℝ (Space 3) (Space k)).toLinearMap

end VolumePolynomials.HigherLift
