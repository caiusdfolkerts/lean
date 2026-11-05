module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic

/-!
# Pinning an infinitesimal Euclidean motion

The linear-algebra fact used in Section 2 of the manuscript is proved here
without appealing to the even-rank theorem for skew-symmetric matrices.
A skew-adjoint real linear map of rank at most one is zero.  Consequently,
an infinitesimal Euclidean motion which vanishes at `dim V` affinely
independent points vanishes everywhere.
-/

@[expose] public section

namespace Cubical.Pinning

open Module
open scoped Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A real skew-adjoint map has no nonzero rank-one case. -/
theorem skew_eq_zero_of_finrank_range_le_one
    (A : V →ₗ[ℝ] V)
    (hskew : ∀ x y : V, inner ℝ (A x) y = -inner ℝ x (A y))
    (hrank : finrank ℝ (LinearMap.range A) ≤ 1) : A = 0 := by
  obtain ⟨y, hy⟩ := (finrank_le_one_iff (K := ℝ)
    (V := LinearMap.range A)).mp hrank
  obtain ⟨x, hx⟩ := y.property
  obtain ⟨c, hc⟩ := hy ⟨A (y : V), ⟨(y : V), rfl⟩⟩
  have hc' : c • (y : V) = A (y : V) := congrArg Subtype.val hc
  have hxy : inner ℝ x (y : V) = 0 := by
    have h := hskew x x
    rw [hx, real_inner_comm x (y : V)] at h
    linarith
  have hyy : inner ℝ (y : V) (y : V) = 0 := by
    have h := hskew x (y : V)
    rw [hx, ← hc', inner_smul_right, hxy] at h
    simpa using h
  have hyzero : (y : V) = 0 := inner_self_eq_zero.mp hyy
  ext z
  obtain ⟨a, ha⟩ := hy ⟨A z, ⟨z, rfl⟩⟩
  have ha' : a • (y : V) = A z := congrArg Subtype.val ha
  simpa [hyzero] using ha'.symm

/-- Killing a subspace of codimension at most one kills a skew-adjoint map. -/
theorem skew_eq_zero_of_large_kernel
    (A : V →ₗ[ℝ] V)
    (hskew : ∀ x y : V, inner ℝ (A x) y = -inner ℝ x (A y))
    (hker : finrank ℝ V ≤ finrank ℝ (LinearMap.ker A) + 1) : A = 0 := by
  apply skew_eq_zero_of_finrank_range_le_one A hskew
  have h := A.finrank_range_add_finrank_ker
  omega

omit [FiniteDimensional ℝ V] in
/-- If an affine map vanishes on a set, its linear part kills the span of all
differences of points of that set. -/
theorem vectorSpan_le_ker_of_pinned
    {ι : Type*} (A : V →ₗ[ℝ] V) (t : V) (q : ι → V)
    (hpin : ∀ i, t + A (q i) = 0) :
    vectorSpan ℝ (Set.range q) ≤ LinearMap.ker A := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro z ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
  change A (q i - q j) = 0
  rw [map_sub, sub_eq_zero]
  exact add_left_cancel ((hpin i).trans (hpin j).symm)

/-- A Euclidean infinitesimal motion pinned on at least `dim V` affinely
independent points is the zero motion.  The cardinal hypothesis permits both
a facet simplex and a full-dimensional simplex. -/
theorem rigid_motion_pinned_on_affine_independent
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : V →ₗ[ℝ] V) (t : V) (q : ι → V)
    (hskew : ∀ x y : V, inner ℝ (A x) y = -inner ℝ x (A y))
    (hind : AffineIndependent ℝ q)
    (hcard : finrank ℝ V ≤ Fintype.card ι)
    (hpin : ∀ i, t + A (q i) = 0) :
    A = 0 ∧ t = 0 ∧ ∀ x : V, t + A x = 0 := by
  have hle := Submodule.finrank_mono (vectorSpan_le_ker_of_pinned A t q hpin)
  have hdim := hind.finrank_vectorSpan_add_one
  have hA : A = 0 := skew_eq_zero_of_large_kernel A hskew (by omega)
  have ht : t = 0 := by
    simpa [hA] using hpin (Classical.arbitrary ι)
  exact ⟨hA, ht, by simp [hA, ht]⟩

end Cubical.Pinning
