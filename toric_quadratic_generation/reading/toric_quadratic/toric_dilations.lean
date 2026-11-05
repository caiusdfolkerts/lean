module
public import PaperVerification.ToricIntegralAffine
public import PaperVerification.ToricInteriorDecomposition
public import Mathlib.Topology.Algebra.ConstMulAction
@[expose] public section
/-!
# Positive integral dilations of the literal smooth lattice polytope

Positive dilation preserves smoothness and the actual normal fan, multiplies
lattice edge lengths, and identifies the needed Minkowski sum with the next
dilation. These facts allow induction in the full integer-decomposition degree.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise BigOperators

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

theorem dilatedGenerators_image (k : ℕ) :
    (embed n) '' ((P.generators.image (fun z => (k : ℤ) • z)) : Set (Lattice n)) =
      (k : ℝ) • ((embed n) '' (P.generators : Set (Lattice n))) := by
  classical
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨embed n w, ⟨w, hw, rfl⟩, by simp only [embed_int_smul, Int.cast_natCast]⟩
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨(k : ℤ) • w, Finset.mem_image.mpr ⟨w, hw, rfl⟩,
      by simp only [embed_int_smul, Int.cast_natCast]⟩

/-- The ordinary dilation by a strictly positive natural number. -/
def dilate (k : ℕ) (hk : 0 < k) : LatticePolytope n where
  generators := P.generators.image (fun z => (k : ℤ) • z)
  nonempty := P.nonempty.image _
  fullDimensional := by
    rw [P.dilatedGenerators_image, convexHull_smul]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
    let e := LinearEquiv.smulOfNeZero ℝ (Ambient n) (k : ℝ) hkR
    change affineSpan ℝ (e.toLinearMap.toAffineMap '' P.carrier) = ⊤
    exact e.toLinearMap.toAffineMap.span_eq_top_of_surjective e.surjective P.fullDimensional

@[simp] theorem carrier_dilate (k : ℕ) (hk : 0 < k) :
    (P.dilate k hk).carrier = (k : ℝ) • P.carrier := by
  change convexHull ℝ ((embed n) ''
    ((P.generators.image (fun z => (k : ℤ) • z)) : Set (Lattice n))) = _
  rw [P.dilatedGenerators_image, convexHull_smul]
  rfl

/-- Actual edges are carried bijectively to actual edges by positive dilation. -/
theorem dilate_isEdge_iff (k : ℕ) (hk : 0 < k) (v w : Ambient n) :
    (P.dilate k hk).IsEdge ((k : ℝ) • v) ((k : ℝ) • w) ↔ P.IsEdge v w := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  let e := LinearEquiv.smulOfNeZero ℝ (Ambient n) (k : ℝ) hkR
  rw [IsEdge, IsEdge, P.carrier_dilate]
  change (e v ≠ e w ∧ IsExtreme ℝ (e.toLinearMap.toAffineMap '' P.carrier)
    (segment ℝ (e.toLinearMap.toAffineMap v) (e.toLinearMap.toAffineMap w))) ↔ _
  rw [← image_segment ℝ e.toLinearMap.toAffineMap,
    affine_isExtreme_image_iff e.toLinearMap.toAffineMap e.injective]
  constructor
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (congrArg e he), hface⟩
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (e.injective he), hface⟩

@[simp] theorem dilated_endpoint (k : ℕ) (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (l : ℕ) :
    embed n ((k : ℤ) • v + ((k * l : ℕ) : ℤ) • b i) =
      (k : ℝ) • embed n (v + (l : ℤ) • b i) := by
  simp only [map_add, embed_int_smul, Int.cast_natCast, Nat.cast_mul,
    Int.cast_mul, smul_add, smul_smul]

/-- Positive integral dilation keeps exactly the same primitive edge bases. -/
theorem smooth_dilate (hP : P.Smooth) (k : ℕ) (hk : 0 < k) :
    (P.dilate k hk).Smooth := by
  intro v hv
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  let e := LinearEquiv.smulOfNeZero ℝ (Ambient n) (k : ℝ) hkR
  have hvertices : (P.dilate k hk).carrier.extremePoints ℝ =
      e '' P.carrier.extremePoints ℝ := by
    rw [P.carrier_dilate]
    exact (image_extremePoints e P.carrier).symm
  rw [hvertices] at hv
  obtain ⟨v, hv, rfl⟩ := hv
  obtain ⟨vZ, b, l, hvZ, hedges, hall⟩ := hP v hv
  refine ⟨(k : ℤ) • vZ, b, fun i => k * l i, ?_, ?_, ?_⟩
  · simp only [embed_int_smul, Int.cast_natCast, hvZ]
    rfl
  · intro i
    refine ⟨Nat.mul_pos hk (hedges i).1, ?_⟩
    rw [dilated_endpoint]
    exact (P.dilate_isEdge_iff k hk _ _).mpr (hedges i).2
  · intro w hw
    obtain ⟨w, rfl⟩ := e.surjective w
    have hw' : P.IsEdge v w := (P.dilate_isEdge_iff k hk v w).mp hw
    obtain ⟨i, hi⟩ := hall w hw'
    refine ⟨i, ?_⟩
    rw [dilated_endpoint, hi]
    rfl

/-- Coordinate gcd, hence lattice edge length, scales by the same positive integer. -/
theorem latticeLength_smul (k : ℕ) (v w : Lattice n) :
    latticeLength ((k : ℤ) • v) ((k : ℤ) • w) = k * latticeLength v w := by
  simp only [latticeLength, Pi.smul_apply, smul_eq_mul, ← mul_sub,
    Int.natAbs_mul, Int.natAbs_natCast]
  rw [Finset.gcd_mul_left]
  simp

/-- Any fixed lower bound on actual edge lengths is preserved by positive integral dilation. -/
theorem edgesAtLeast_dilate {bound : ℕ} (hP : P.EdgesAtLeast bound)
    (k : ℕ) (hk : 0 < k) : (P.dilate k hk).EdgesAtLeast bound := by
  intro v w hvw
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  let e := LinearEquiv.smulOfNeZero ℝ (Ambient n) (k : ℝ) hkR
  obtain ⟨v, rfl⟩ := e.surjective v
  obtain ⟨w, rfl⟩ := e.surjective w
  have hvw' := (P.dilate_isEdge_iff k hk v w).mp hvw
  obtain ⟨vZ, wZ, hvZ, hwZ, hlen⟩ := hP v w hvw'
  refine ⟨(k : ℤ) • vZ, (k : ℤ) • wZ, ?_, ?_, ?_⟩
  · simp only [embed_int_smul, Int.cast_natCast, hvZ]
    rfl
  · simp only [embed_int_smul, Int.cast_natCast, hwZ]
    rfl
  · rw [latticeLength_smul]
    calc
      bound ≤ latticeLength vZ wZ := hlen
      _ = 1 * latticeLength vZ wZ := by simp
      _ ≤ k * latticeLength vZ wZ :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hk)

/-- The actual normal cone at a scaled point is unchanged. -/
theorem normalCone_dilate (k : ℕ) (hk : 0 < k) (x : Ambient n) :
    (P.dilate k hk).normalCone ((k : ℝ) • x) = P.normalCone x := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  ext u
  have hsum (y : Ambient n) :
      (∑ i, u i * (((k : ℝ) • y) i - ((k : ℝ) • x) i)) =
        (k : ℝ) * ∑ i, u i * (y i - x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · intro h y hy
    have hky : (k : ℝ) • y ∈ (P.dilate k hk).carrier := by
      rw [P.carrier_dilate]
      exact ⟨y, hy, rfl⟩
    have h' := h ((k : ℝ) • y) hky
    rw [hsum] at h'
    exact (mul_nonneg_iff_of_pos_left hkR).mp h'
  · intro h y hy
    rw [P.carrier_dilate] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    rw [hsum]
    exact mul_nonneg hkR.le (h y hy)

/-- Equality of ordinary normal fans under positive dilation. -/
theorem sameNormalFan_dilate (k : ℕ) (hk : 0 < k) :
    P.SameNormalFan (P.dilate k hk) := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(k : ℝ) • x, ?_, (P.normalCone_dilate k hk x).symm⟩
    rw [P.carrier_dilate]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hC⟩
    rw [P.carrier_dilate] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, hC.trans (P.normalCone_dilate k hk x)⟩

/-- Minkowski addition of a convex polytope and its positive dilation is the
next ordinary dilation. -/
theorem minkowskiSum_dilate (k : ℕ) (hk : 0 < k) :
    P.minkowskiSum (P.dilate k hk) = ((k + 1 : ℕ) : ℝ) • P.carrier := by
  rw [minkowskiSum, P.carrier_dilate]
  calc
    P.carrier + (k : ℝ) • P.carrier = (1 : ℝ) • P.carrier + (k : ℝ) • P.carrier := by simp
    _ = (1 + (k : ℝ)) • P.carrier :=
      ((convex_convexHull ℝ _).add_smul zero_le_one (Nat.cast_nonneg k)).symm
    _ = ((k + 1 : ℕ) : ℝ) • P.carrier := by congr 1; push_cast; ring

end LatticePolytope

end PaperVerification.ToricGeometry
