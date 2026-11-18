module

public import PaperVerification.E7Theorems
public import PaperVerification.LatticeMetricMeaning
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem coordinateInner_eq_euclidean_inner (x y : Fin 8 → ℝ) :
    coordinateInner x y=inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 y) := by
  simp [coordinateInner,EuclideanSpace.inner_toLp_toLp,dotProduct,mul_comm]

/-- `project8` is orthogonal projection for the Euclidean inner product,
independently of the default norm on an unbundled coordinate function type. -/
theorem project8_residual_orthogonal (x : Fin 8 → ℝ) (y : zeroSumSpace) :
    inner ℝ (WithLp.toLp 2 (x-(project8 x).val) : EuclideanSpace ℝ (Fin 8))
      (WithLp.toLp 2 y.val)=0 := by
  rw [← coordinateInner_eq_euclidean_inner]
  unfold coordinateInner
  simp only [Pi.sub_apply,project8_apply,sub_sub_cancel,← Finset.mul_sum,
    zeroSumSpace_sum,mul_zero]

theorem e7DualSet_euclidean_meaning (y : zeroSumSpace) : y ∈ e7DualSet ↔
    ∀ x ∈ e7Set, ∃ k : ℤ,
      inner ℝ (WithLp.toLp 2 y.val : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 x.val)=(k:ℝ) := by
  simp only [e7DualSet,Set.mem_setOf_eq,coordinateInner_eq_euclidean_inner]

def e7AmbientLattice : Set (Fin 8 → ℝ) := Subtype.val '' e7ProjectedSet

/-- The projected lattice and its ambient image have exactly the same points,
with no multiplicities introduced by the coordinate inclusion. -/
def e7AmbientLatticeEquiv : e7ProjectedSet ≃ e7AmbientLattice :=
  Equiv.ofBijective (fun y ↦ ⟨y.val.val, y.val, y.property, rfl⟩) ⟨by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : e7AmbientLattice ↦ v.val) h, by
    rintro ⟨v, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩⟩

theorem e7AmbientLattice_eq_dual_image :
    e7AmbientLattice = Subtype.val '' e7DualSet := by
  rw [e7DualSet_eq_projected]
  rfl

theorem e7Gaussian_eq_ambient (α : ℝ) (x : zeroSumSpace) :
    e7Gaussian α x = setGaussian e7AmbientLattice α x.val := by
  exact e7AmbientLatticeEquiv.tsum_eq
    (fun v : e7AmbientLattice ↦ Real.exp (-α * sqDist v.val x.val))

/-- The Gaussian in the principal E7 statement is the literal Gaussian sum
for the Euclidean realization of the integral dual lattice. -/
theorem e7Gaussian_eq_euclidean (α : ℝ) (x : zeroSumSpace) :
    e7Gaussian α x = ∑' v : euclideanRealization e7AmbientLattice,
      Real.exp (-α * dist v.val
        (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8)) ^ 2) := by
  rw [e7Gaussian_eq_ambient, setGaussian_eq_euclidean]

theorem isE7ColdSpot_iff_euclidean (α : ℝ) (x : zeroSumSpace) :
    IsE7ColdSpot α x ↔ ∀ y : EuclideanSpace ℝ (Fin 8), (∑ i, y i) = 0 →
      (∑' v : euclideanRealization e7AmbientLattice,
        Real.exp (-α * dist v.val
          (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8)) ^ 2)) ≤
        ∑' v : euclideanRealization e7AmbientLattice,
          Real.exp (-α * dist v.val y ^ 2) := by
  constructor
  · intro h y hy
    let z : zeroSumSpace := ⟨WithLp.ofLp y, hy⟩
    have hz := h z
    simpa only [e7Gaussian_eq_euclidean, z, WithLp.toLp_ofLp] using hz
  · intro h y
    have hy := h (WithLp.toLp 2 y.val) y.property
    simpa only [e7Gaussian_eq_euclidean] using hy

theorem e7SquaredDepth_eq_ambient (x : zeroSumSpace) :
    e7SquaredDepth x=squaredDepth e7AmbientLattice x.val := by
  unfold e7SquaredDepth squaredDepth e7AmbientLattice
  rw [Set.image_image]

theorem e7SquaredDepth_metric_meaning (x : zeroSumSpace) :
    e7SquaredDepth x=Metric.infDist (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8))
      (euclideanRealization e7AmbientLattice)^2 := by
  rw [e7SquaredDepth_eq_ambient]
  exact squaredDepth_eq_infDist_sq e7AmbientLattice
    (e7Projected_nonempty.image (fun y : zeroSumSpace ↦ y.val)) x.val

theorem isE7DeepHole_metric_meaning (x : zeroSumSpace) : IsE7DeepHole x ↔
    ∀ y : EuclideanSpace ℝ (Fin 8), (∑ i,y i)=0 →
      Metric.infDist y (euclideanRealization e7AmbientLattice) ≤
        Metric.infDist (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8))
          (euclideanRealization e7AmbientLattice) := by
  constructor
  · intro h y hy
    let z : zeroSumSpace := ⟨WithLp.ofLp y,hy⟩
    have hd := h z
    rw [e7SquaredDepth_metric_meaning,e7SquaredDepth_metric_meaning] at hd
    exact (sq_le_sq₀ Metric.infDist_nonneg Metric.infDist_nonneg).mp hd
  · intro h y
    rw [e7SquaredDepth_metric_meaning,e7SquaredDepth_metric_meaning]
    exact pow_le_pow_left₀ Metric.infDist_nonneg
      (h (WithLp.toLp 2 y.val) y.property) 2

def coordinateSumLinear : (Fin 8 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i,x i
  map_add' := by intro x y; simp [Finset.sum_add_distrib]
  map_smul' := by intro a x; simp [← Finset.mul_sum]

theorem coordinateSumLinear_surjective : Function.Surjective coordinateSumLinear := by
  intro c
  exact ⟨Pi.single 0 c,by simp [coordinateSumLinear,Pi.single_apply]⟩

theorem zeroSumSpace_finrank : Module.finrank ℝ zeroSumSpace=7 := by
  have hk : LinearMap.ker coordinateSumLinear=zeroSumSpace := rfl
  have hr : LinearMap.range coordinateSumLinear=⊤ :=
    LinearMap.range_eq_top.mpr coordinateSumLinear_surjective
  have h := LinearMap.finrank_range_add_finrank_ker coordinateSumLinear
  rw [hk,hr] at h
  norm_num at h
  omega

end PaperVerification.ColdSpots
