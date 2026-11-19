module

public import VolumePolynomials.PlanarZonotope
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

/-!
# Finite zonotopes and their planar area polynomials

The generic carrier is a literal finite Minkowski sum of centered segments.
Labels may repeat: this allows many generating segments to carry the same body
variable. The planar polynomial is proved from the exact area identity.
-/

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped Pointwise

namespace VolumePolynomials.FiniteZonotope

variable {E F ι : Type*} [AddCommGroup E] [Module ℝ E]

def segment (v : E) : Set E :=
  (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2)

def carrier : List E → Set E
  | [] => {0}
  | v :: vs => carrier vs + segment v

def weightedCarrier (t : ι → ℝ) (vs : List (ι × E)) : Set E :=
  carrier (vs.map (fun p => t p.1 • p.2))

@[simp] theorem segment_zero : segment (0 : E) = {0} := by
  ext x
  simp only [segment, Set.mem_image, smul_zero, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rfl
  · intro hx
    subst x
    exact ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem zero_mem_segment (v : E) : (0 : E) ∈ segment v := by
  exact ⟨0, ⟨by norm_num, by norm_num⟩, zero_smul ℝ v⟩

theorem zero_mem_carrier (vs : List E) : (0 : E) ∈ carrier vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => exact ⟨0, ih, 0, zero_mem_segment v, zero_add 0⟩

@[simp] theorem carrier_singleton (v : E) : carrier [v] = segment v := by
  simp [carrier, Set.singleton_zero]

theorem carrier_append (xs ys : List E) :
    carrier (xs ++ ys) = carrier xs + carrier ys := by
  induction xs with
  | nil => simp [carrier, Set.singleton_zero]
  | cons v xs ih => simp [carrier, ih, add_assoc, add_comm, add_left_comm]

theorem carrier_range_succ (u : ℕ → E) (N : ℕ) :
    carrier ((List.range (N + 1)).map u) =
      carrier ((List.range N).map u) + segment (u N) := by
  simp [List.range_succ, List.map_append, carrier_append]

@[simp] theorem weightedCarrier_cons (t : ι → ℝ) (p : ι × E) (vs : List (ι × E)) :
    weightedCarrier t (p :: vs) = weightedCarrier t vs + segment (t p.1 • p.2) := rfl

section Image

variable [AddCommGroup F] [Module ℝ F]

theorem image_segment (L : E →ₗ[ℝ] F) (v : E) : L '' segment v = segment (L v) := by
  simp only [segment, Set.image_image, map_smul, Function.comp_def]

theorem image_carrier (L : E →ₗ[ℝ] F) (vs : List E) :
    L '' carrier vs = carrier (vs.map L) := by
  induction vs with
  | nil => simp [carrier]
  | cons v vs ih =>
      simp only [carrier, List.map_cons, Set.image_add L, ih, image_segment]

theorem image_weightedCarrier (L : E →ₗ[ℝ] F) (t : ι → ℝ) (vs : List (ι × E)) :
    L '' weightedCarrier t vs =
      weightedCarrier t (vs.map (fun p => (p.1, L p.2))) := by
  simp only [weightedCarrier, image_carrier, List.map_map, Function.comp_def, map_smul]

end Image

theorem smul_carrier (a : ℝ) (vs : List E) :
    a • carrier vs = carrier (vs.map (fun v => a • v)) := by
  exact image_carrier (a • (LinearMap.id : E →ₗ[ℝ] E)) vs

theorem weightedCarrier_append (t : ι → ℝ) (xs ys : List (ι × E)) :
    weightedCarrier t (xs ++ ys) = weightedCarrier t xs + weightedCarrier t ys := by
  simp only [weightedCarrier, List.map_append, carrier_append]

theorem weightedCarrier_constantLabel (t : ι → ℝ) (i : ι) (vs : List E) :
    weightedCarrier t (vs.map (fun v => (i, v))) = t i • carrier vs := by
  simp only [weightedCarrier, List.map_map, Function.comp_def, smul_carrier]

def labelled (vs : ι → List E) : List ι → List (ι × E)
  | [] => []
  | i :: is => (vs i).map (fun v => (i, v)) ++ labelled vs is

theorem weightedCarrier_labelled (vs : ι → List E) (is : List ι) (t : ι → ℝ) :
    weightedCarrier t (labelled vs is) =
      (is.map (fun i => t i • carrier (vs i))).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [labelled, weightedCarrier_append, weightedCarrier_constantLabel, ih,
        List.map_cons, List.sum_cons]

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem segment_compact (v : E) : IsCompact (segment v) :=
  isCompact_Icc.image (continuous_id.smul continuous_const)

theorem carrier_compact (vs : List E) : IsCompact (carrier vs) := by
  induction vs with
  | nil => exact isCompact_singleton
  | cons v vs ih => exact ih.add (segment_compact v)

end Topology

theorem segment_convex (v : E) : Convex ℝ (segment v) :=
  (convex_Icc _ _).linear_image (LinearMap.toSpanSingleton ℝ E v)

theorem carrier_convex (vs : List E) : Convex ℝ (carrier vs) := by
  induction vs with
  | nil => exact convex_singleton 0
  | cons v vs ih => exact ih.add (segment_convex v)

section Planar

open PlanarExtrusion

theorem planar_carrier (vs : List Plane) : carrier vs = zonotope vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [carrier, zonotope, ih, segment, PlanarExtrusion.centeredSegment]

def widthPolynomial (v : Plane) : List (ι × Plane) → MvPolynomial ι ℝ
  | [] => 0
  | (i, w) :: ws => C |determinant v w| * X i + widthPolynomial v ws

def areaPolynomial : List (ι × Plane) → MvPolynomial ι ℝ
  | [] => 0
  | (i, v) :: vs => areaPolynomial vs + X i * widthPolynomial v vs

theorem widthPolynomial_homogeneous (v : Plane) (vs : List (ι × Plane)) :
    (widthPolynomial v vs).IsHomogeneous 1 := by
  induction vs with
  | nil => exact isHomogeneous_zero (σ := ι) (R := ℝ) 1
  | cons p vs ih =>
      obtain ⟨i, w⟩ := p
      exact ((isHomogeneous_C (σ := ι) _).mul (isHomogeneous_X (R := ℝ) i)).add ih

theorem areaPolynomial_homogeneous (vs : List (ι × Plane)) :
    (areaPolynomial vs).IsHomogeneous 2 := by
  induction vs with
  | nil => exact isHomogeneous_zero (σ := ι) (R := ℝ) 2
  | cons p vs ih =>
      obtain ⟨i, v⟩ := p
      exact ih.add ((isHomogeneous_X (R := ℝ) i).mul (widthPolynomial_homogeneous v vs))

theorem widthPolynomial_eval (t : ι → ℝ) (v : Plane) (vs : List (ι × Plane)) :
    eval t (widthPolynomial v vs) =
      (vs.map (fun p => t p.1 * |determinant v p.2|)).sum := by
  induction vs with
  | nil => simp [widthPolynomial]
  | cons p vs ih =>
      obtain ⟨i, w⟩ := p
      simp [widthPolynomial, ih, mul_comm]

theorem determinant_smul (s t : ℝ) (v w : Plane) :
    determinant (s • v) (t • w) = s * t * determinant v w := by
  simp only [determinant, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem areaPolynomial_eval (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (vs : List (ι × Plane)) :
    eval t (areaPolynomial vs) =
      pairArea (vs.map (fun p => t p.1 • p.2)) := by
  induction vs with
  | nil => simp [areaPolynomial, pairArea]
  | cons p vs ih =>
      obtain ⟨i, v⟩ := p
      simp only [areaPolynomial, eval_add, eval_mul, eval_X, ih,
        List.map_cons, pairArea, widthPolynomial_eval, List.map_map, Function.comp_def]
      congr 1
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [determinant_smul, abs_mul, abs_mul, abs_of_nonneg (ht i),
        abs_of_nonneg (ht p.1)]
      ring

/-- Literal planar volume is a homogeneous quadratic for every labelled finite
family of generating segments and all nonnegative variable assignments. -/
theorem areaPolynomial_realizes (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (vs : List (ι × Plane)) :
    eval t (areaPolynomial vs) = volume.real (weightedCarrier t vs) := by
  rw [weightedCarrier, planar_carrier, area_zonotope, areaPolynomial_eval t ht]

end Planar

end VolumePolynomials.FiniteZonotope
