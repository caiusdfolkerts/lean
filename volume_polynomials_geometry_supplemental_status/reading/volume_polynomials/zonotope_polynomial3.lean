module

public import VolumePolynomials.FiniteZonotope
public import VolumePolynomials.ExtrusionTransport
public import VolumePolynomials.ProjectionCoordinates
public import VolumePolynomials.PolynomialCoordinates
public import VolumePolynomials.BodyOperations
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Genuine volume polynomials for arbitrary finite three-dimensional zonotopes

The proof constructs a homogeneous cubic from actual product-coordinate
extrusion and actual planar zonotope area. Generators may be zero, repeated, or
linearly dependent. Labels may repeat. In particular this proves existence for
an arbitrary finite tuple of finite zonotopes, with every nonnegative real
weight simultaneously quantified.
-/

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped Pointwise BigOperators

namespace VolumePolynomials.FiniteZonotope

open PlanarExtrusion ProductExtrusion

abbrev ThreeSpace := Fin 3 → ℝ

/-- Reflection of the first product coordinate. -/
def reverseAxisLinear : (ℝ × Plane) ≃ₗ[ℝ] ℝ × Plane where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' c p := by ext <;> simp

def reverseAxis : (ℝ × Plane) ≃L[ℝ] ℝ × Plane :=
  reverseAxisLinear.toContinuousLinearEquiv

theorem reverseAxis_measurePreserving : MeasurePreserving reverseAxis volume volume := by
  first
  | exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure Plane))

/-- Every nonzero direction has positive axial length in a volume-preserving
product frame. This is proved by extracting a nonzero coordinate, shearing the
other two coordinates, and, when needed, reflecting the first coordinate. -/
theorem exists_positive_frame (v : ThreeSpace) (hv : v ≠ 0) :
    ∃ (c : ℝ), 0 < c ∧ ∃ T : ThreeSpace ≃L[ℝ] (ℝ × Plane),
      MeasurePreserving T volume volume ∧ T v = (c, 0) := by
  first
  | have hcoord : ∃ i, v i ≠ 0 := by
      by_contra h
      apply hv
      funext i
      exact not_not.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hcoord
    let u : Plane := (v i)⁻¹ • (v (i.succAbove 0), v (i.succAbove 1))
    let S := Holonomy.projectionFrame i u
    have hS : MeasurePreserving S volume volume := Holonomy.projectionFrame_measurePreserving i u
    have hSv : S v = (v i, 0) := by
      simp only [S, Holonomy.projectionFrame_apply, u, smul_smul, mul_inv_cancel₀ hi,
        one_smul, sub_self]
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · refine ⟨-v i, neg_pos.mpr hneg, S.trans reverseAxis, ?_, ?_⟩
      · exact reverseAxis_measurePreserving.comp hS
      · change reverseAxis (S v) = (-v i, 0)
        rw [hSv]
        rfl
    · exact ⟨v i, hpos, S, hS, hSv⟩

/-- An actual homogeneous cubic exists for the volume of every labelled finite
three-dimensional zonotope. -/
theorem exists_volumePolynomial {ι : Type*} (vs : List (ι × ThreeSpace)) :
    ∃ p : MvPolynomial ι ℝ, p.IsHomogeneous 3 ∧
      ∀ t : ι → ℝ, (∀ i, 0 ≤ t i) →
        eval t p = volume.real (weightedCarrier t vs) := by
  first
  | induction vs with
    | nil =>
        refine ⟨0, isHomogeneous_zero (σ := ι) (R := ℝ) 3, ?_⟩
        intro t ht
        simp [weightedCarrier, carrier, measureReal_def]
    | cons a vs ih =>
        obtain ⟨i, v⟩ := a
        obtain ⟨p, hp, hpval⟩ := ih
        by_cases hv : v = 0
        · subst v
          refine ⟨p, hp, ?_⟩
          intro t ht
          simpa [weightedCarrier_cons, segment_zero, Set.singleton_zero]
            using hpval t ht
        · obtain ⟨c, hc, T, hT, hTv⟩ := exists_positive_frame v hv
          let P : ThreeSpace →ₗ[ℝ] Plane := (LinearMap.snd ℝ ℝ Plane).comp T.toLinearMap
          let projected : List (ι × Plane) := vs.map (fun a => (a.1, P a.2))
          let q : MvPolynomial ι ℝ := areaPolynomial projected
          have hq : q.IsHomogeneous 2 := areaPolynomial_homogeneous projected
          refine ⟨p + (C c * X i) * q, ?_, ?_⟩
          · exact hp.add (((isHomogeneous_C (σ := ι) c).mul
              (isHomogeneous_X (R := ℝ) i)).mul hq)
          · intro t ht
            have hproj : projection (T '' weightedCarrier t vs) =
                weightedCarrier t projected := by
              rw [projection, Set.image_image]
              exact image_weightedCarrier P t vs
            have hscaled : T (t i • v) = (t i * c, 0) := by
              simp only [map_smul, hTv, Prod.smul_mk, smul_eq_mul, smul_zero]
            have hvol : volume.real (weightedCarrier t ((i, v) :: vs)) =
                volume.real (weightedCarrier t vs) +
                  (t i * c) * volume.real (weightedCarrier t projected) := by
              change volume.real (weightedCarrier t vs +
                (fun s : ℝ => s • (t i • v)) '' Icc (-(1 / 2 : ℝ)) (1 / 2)) = _
              rw [realVolume_add_centered_segment_nonneg (C := weightedCarrier t vs) T hT
                (carrier_compact _) (carrier_convex _) hscaled (mul_nonneg (ht i) hc.le), hproj]
            rw [eval_add, eval_mul, eval_mul, eval_C, eval_X, hpval t ht]
            change volume.real (weightedCarrier t vs) + (c * t i) *
              eval t (areaPolynomial projected) = _
            rw [areaPolynomial_realizes t ht, hvol]
            ring

/-- The convex body associated to a finite list of generators. -/
def toBody (vs : List ThreeSpace) : Body 3 :=
  ⟨carrier vs, carrier_convex vs, carrier_compact vs, ⟨0, zero_mem_carrier vs⟩⟩

@[simp] theorem coe_toBody (vs : List ThreeSpace) :
    (toBody vs : Set ThreeSpace) = carrier vs := rfl

theorem weightedSum_toBody {n : ℕ} (vs : Fin n → List ThreeSpace) (t : Fin n → ℝ) :
    (weightedSum (fun i => toBody (vs i)) t : Set ThreeSpace) =
      weightedCarrier t (labelled vs (List.finRange n)) := by
  first
  | rw [weightedSum, coe_sum_body, weightedCarrier_labelled, ← Fin.sum_univ_def]
    simp only [ConvexBody.coe_smul, coe_toBody]

/-- Every tuple of finite three-dimensional zonotopes has a genuine volume
polynomial in the paper's complete coefficient convention. -/
theorem exists_realizes {n : ℕ} (vs : Fin n → List ThreeSpace) :
    ∃ c : Coefficients n 3, Realizes (fun i => toBody (vs i)) c := by
  first
  | obtain ⟨p, hp, hvol⟩ := exists_volumePolynomial (labelled vs (List.finRange n))
    refine ⟨coefficientsOfPolynomial p, realizes_of_homogeneous_polynomial _ p hp ?_⟩
    intro t ht
    change eval t p = volume.real (weightedSum (fun i => toBody (vs i)) t : Set ThreeSpace)
    rw [weightedSum_toBody]
    exact hvol t ht

end VolumePolynomials.FiniteZonotope
