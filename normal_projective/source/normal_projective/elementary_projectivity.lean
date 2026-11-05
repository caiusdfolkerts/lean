module
public import normal_projective.unit_normalization
public import normal_projective.admissible_projectivity
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.FieldSimp
/-! # Actual homogeneous matrices for the elementary projective moves -/
@[expose] public section
noncomputable section
open Set Matrix
open scoped BigOperators
namespace NormalProjective
namespace ElementaryProjectivity
open UnitNormalization ProjectiveBridge
open CanonicalModel.Realization
variable {d : ℕ}

def homogeneous (u : CanonicalModel.Space d →L[ℝ] ℝ) : HomogeneousMatrix d :=
  fun i j => match i, j with
    | none, none => 1
    | none, some j => coefficients u j
    | some _, none => 0
    | some i, some j => if i = j then 1 else 0

theorem homogeneous_inverse (u : CanonicalModel.Space d →L[ℝ] ℝ) :
    homogeneous (-u) * homogeneous u = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_option, homogeneous, coefficients,
      Matrix.one_apply, mul_ite, ite_mul]

theorem homogeneous_det_ne_zero (u : CanonicalModel.Space d →L[ℝ] ℝ) :
    (homogeneous u).det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse (homogeneous_inverse u)

@[simp] theorem homogeneous_denominator (u : CanonicalModel.Space d →L[ℝ] ℝ)
    (x : CanonicalModel.Space d) :
    denominator (homogeneous u) x = 1 + u x := by
  change 1 + (∑ j, coefficients u j * x j) = _
  rw [coefficient_expansion]

@[simp] theorem homogeneous_numerator (u : CanonicalModel.Space d →L[ℝ] ℝ)
    (x : CanonicalModel.Space d) : numerator (homogeneous u) x = x := by
  ext j
  simp [numerator, homogeneous, ite_mul]

@[simp] theorem homogeneous_map (u : CanonicalModel.Space d →L[ℝ] ℝ)
    (x : CanonicalModel.Space d) :
    projectiveMap (homogeneous u) x = elementary u.toLinearMap x := by
  ext j
  simp [projectiveMap, elementary, div_eq_mul_inv, mul_comm]

variable {ι : Type*}

theorem tight_iff (f : ι → CanonicalModel.Space d →ₗ[ℝ] ℝ)
    (h : ι → ℝ) (u : CanonicalModel.Space d →ₗ[ℝ] ℝ)
    (x : CanonicalModel.Space d) (hx : 0 < 1 + u x) (i : ι) :
    changedNormals f h u i (elementary u x) = h i ↔ f i x = h i := by
  rw [linear_elementary, changedNormals_apply, div_eq_iff (ne_of_gt hx)]
  constructor <;> intro hh <;> nlinarith

theorem elementary_image_facet (f : ι → CanonicalModel.Space d →ₗ[ℝ] ℝ)
    (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (hb : Bornology.IsBounded (HRegion f h))
    (u : CanonicalModel.Space d →ₗ[ℝ] ℝ)
    (hforward : ∀ x ∈ HRegion f h, 0 < 1 + u x) (i : ι) :
    elementary u '' {x ∈ HRegion f h | f i x = h i} =
      {y ∈ HRegion (changedNormals f h u) h | changedNormals f h u i y = h i} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
    exact ⟨(mem_changed_iff f h u x (hforward x hx)).mpr hx,
      (tight_iff f h u x (hforward x hx) i).mpr hxi⟩
  · rintro ⟨hy, hyi⟩
    rw [← elementary_image_HRegion f h hh hb u hforward] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨hx, (tight_iff f h u x (hforward x hx) i).mp hyi⟩, rfl⟩

variable [Fintype ι]

/-- The set-level formulas give precisely the canonical model's admissible P-step. -/
theorem canonical_step
    {R : CanonicalModel.Presentation d ι} (P Q : CanonicalModel.Realization R)
    (f : ι → CanonicalModel.Space d →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) (hb : Bornology.IsBounded (HRegion f h))
    (u : CanonicalModel.Space d →L[ℝ] ℝ)
    (hforward : ∀ x ∈ HRegion f h, 0 < 1 + u x)
    (hP : P.carrier = HRegion f h)
    (hQ : Q.carrier = HRegion (changedNormals f h u.toLinearMap) h)
    (hPF : ∀ i, P.facet i = {x ∈ HRegion f h | f i x = h i})
    (hQF : ∀ i, Q.facet i = {y ∈ HRegion (changedNormals f h u.toLinearMap) h |
      changedNormals f h u.toLinearMap i y = h i}) :
    ProjectiveStep P Q := by
  refine ⟨homogeneous u, homogeneous_det_ne_zero u, ?_, ?_, ?_⟩
  · intro x hx
    rw [homogeneous_denominator]
    exact ne_of_gt (hforward x (hP ▸ hx))
  · simp_rw [homogeneous_map]
    rw [hP, hQ]
    exact elementary_image_HRegion f h hh hb u.toLinearMap hforward
  · intro i
    simp_rw [homogeneous_map]
    rw [hPF i, hQF i]
    exact elementary_image_facet f h hh hb u.toLinearMap hforward i

end ElementaryProjectivity
end NormalProjective

