module
public import PaperVerification.ToricSmoothFaces
public import PaperVerification.ToricAffineInterior
@[expose] public section
/-!
# Exact passage from the mixed principal claims to quadratic generation

This file proves the complete face-coordinate and exchange reduction. The two
mixed principal statements are explicit inputs to this reduction; their proofs
are supplied by the dimension induction in `ToricMainTheorems`, which applies
the reduction to obtain the unconditional principal theorem. The unrestricted
integer-decomposition theorem used here has its own independent proof through
smooth face charts.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise
open PaperVerification.ToricExchange

namespace LatticePolytope

/-- Adding a convex polytope to itself is exactly its ordinary double dilation. -/
theorem minkowskiSum_self {n : ℕ} (P : LatticePolytope n) :
    P.minkowskiSum P = (2 : ℝ) • P.carrier := by
  change P.carrier + P.carrier = _
  have hconv : Convex ℝ P.carrier := convex_convexHull ℝ _
  have hone : (1 : ℝ) + 1 = 2 := by norm_num
  simpa only [hone, one_smul] using (hconv.add_smul
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)).symm

/-- The full prescribed-parity mixed statement supplies Proposition 2.1(i)
on every actual face in its saturated affine lattice. -/
theorem faceParity_of_mixed_parity {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hlP : P.EdgesAtLeast n)
    (hparity : Theorem1_2PolytopeStatement) :
    FaceParity (embed n) P.carrier := by
  intro F hFc hFP z hz c hc
  obtain ⟨x, hx, hxz⟩ := intrinsicInterior_subset hz
  obtain ⟨d, Q, e, hd, hstrict, hQ, hlQ, heF⟩ :=
    P.smooth_face_chart hP hlP F ⟨x, hx⟩ hFc hFP
  have hld : Q.EdgesAtLeast d := Q.edgesAtLeast_mono hlQ hd
  have hz' : embed n z ∈ intrinsicInterior ℝ ((2 : ℝ) • (e.realMap '' Q.carrier)) := by
    simpa only [heF] using hz
  obtain ⟨u, hu, huz⟩ := (e.lattice_intrinsicInterior_twice_image_iff Q z).mp hz'
  have hcRange : embed n c ∈ Set.range e.realMap := by
    rw [e.realMap_range_eq_affineSpan Q, heF]
    exact hc
  obtain ⟨c0, hc0⟩ := e.exists_latticeMap_of_mem_range c hcRange
  have huSum : embed d u ∈ interior (Q.minkowskiSum Q) := by
    simpa only [Q.minkowskiSum_self] using hu
  obtain ⟨a, b, ha, hb, hab, hpar⟩ :=
    hparity d Q Q hQ hQ rfl hld hld u huSum c0
  refine ⟨e.latticeMap a, e.latticeMap b, ?_, ?_, ?_, ?_⟩
  · rw [e.embed_latticeMap, ← heF]
    exact ⟨embed d a, ha, rfl⟩
  · rw [e.embed_latticeMap, ← heF]
    exact ⟨embed d b, hb, rfl⟩
  · rw [← e.scaleOrigin_two_latticeMap, hab, huz]
  · simpa only [hc0] using e.sameParity_latticeMap hpar

/-- On a proper face the original edge threshold `n` is at least `d+1`.
Thus the full adjoint mixed statement supplies exactly Proposition 2.1(ii). -/
theorem faceAdjoint_of_mixed_adjoint {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hlP : P.EdgesAtLeast n)
    (hadjoint : Theorem1_3PolytopeStatement) :
    FaceAdjoint (embed n) P.carrier := by
  intro F hFc hFP hproper z hz
  obtain ⟨x, hx, hxz⟩ := intrinsicInterior_subset hz
  obtain ⟨d, Q, e, hd, hQ, hlQ, heF⟩ :=
    P.proper_smooth_face_chart hP hlP F ⟨x, hx⟩ hFc hFP hproper
  have hld : Q.EdgesAtLeast (d + 1) := Q.edgesAtLeast_mono hlQ (by omega)
  have hz' : embed n z ∈ intrinsicInterior ℝ ((2 : ℝ) • (e.realMap '' Q.carrier)) := by
    simpa only [heF] using hz
  obtain ⟨u, hu, huz⟩ := (e.lattice_intrinsicInterior_twice_image_iff Q z).mp hz'
  have huSum : embed d u ∈ interior (Q.minkowskiSum Q) := by
    simpa only [Q.minkowskiSum_self] using hu
  obtain ⟨a, b, ha, hb, hab⟩ := (hadjoint d Q Q hQ hQ rfl hld hld u).mp huSum
  refine ⟨e.latticeMap a, e.latticeMap b, ?_, ?_, ?_⟩
  · rw [e.embed_latticeMap, ← heF]
    exact ⟨embed d a, ha, rfl⟩
  · rw [← heF, e.intrinsicInterior_image, e.embed_latticeMap]
    refine ⟨embed d b, ?_, rfl⟩
    rw [intrinsicInterior_eq_interior_of_fullSpan Q.carrier Q.fullDimensional]
    exact hb
  · rw [← e.scaleOrigin_two_latticeMap, hab, huz]

end LatticePolytope

/-- The exact principal quadratic-generation statement follows from the two
exact mixed principal statements, with all face and exchange dependencies
proved here. This reduction alone is not a verification of those inputs. -/
theorem theorem1_1_of_mixed (R : Type*) [Field R]
    (hparity : Theorem1_2PolytopeStatement) (hadjoint : Theorem1_3PolytopeStatement) :
    Theorem1_1Statement R := by
  intro n hn P hP hlP
  have hidp := P.integerDecomposition_of_smooth_long_edges hP hlP
  refine ⟨hidp, ?_⟩
  exact (P.proposition2_1 R hidp (P.faceParity_of_mixed_parity hP hlP hparity)
    (P.faceAdjoint_of_mixed_adjoint hP hlP hadjoint)).2

end PaperVerification.ToricGeometry
