module
public import PaperVerification.ToricIntegralAffine
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Topology.Algebra.ConstMulAction
@[expose] public section
/-!
# Relative interiors under saturated integral affine charts

Injective finite-dimensional affine maps preserve intrinsic interiors. The proof
factors an injective linear map through its actual range, using an affine
equivalence and the isometric subtype inclusion. Full-dimensional source charts
therefore convert intrinsic interior exactly to ordinary interior.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise
open PaperVerification.ToricExchange

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Relative interior commutes with an injective linear map between finite
real vector spaces, even when its image has lower ambient dimension. -/
theorem intrinsicInterior_linear_image {d n : ℕ}
    (L : Ambient d →ₗ[ℝ] Ambient n) (hL : Function.Injective L) (S : Set (Ambient d)) :
    intrinsicInterior ℝ (L '' S) = L '' intrinsicInterior ℝ S := by
  let e : Ambient d ≃ₗ[ℝ] L.range := LinearEquiv.ofInjective L hL
  let i := L.range.subtypeₗᵢ.toAffineIsometry
  have himage : L '' S = i '' (e.toAffineEquiv '' S) := by
    rw [Set.image_image]
    rfl
  have he : intrinsicInterior ℝ (e.toAffineEquiv '' S) =
      e.toAffineEquiv '' intrinsicInterior ℝ S :=
    AffineEquiv.intrinsicInterior_image (𝕜 := ℝ)
      (V := Ambient d) (W := L.range) (P := Ambient d) (Q := L.range)
      e.toAffineEquiv S
  rw [himage, i.intrinsicInterior_image, he, Set.image_image]
  rfl

/-- In the full-dimensional case, intrinsic interior is exactly ordinary interior. -/
theorem intrinsicInterior_eq_interior_of_fullSpan {n : ℕ} (S : Set (Ambient n))
    (hS : affineSpan ℝ S = ⊤) : intrinsicInterior ℝ S = interior S := by
  rw [intrinsicInterior, hS]
  let e := Homeomorph.Set.univ (Ambient n)
  change e '' interior (e ⁻¹' S) = interior S
  rw [e.image_interior, Set.image_preimage_eq S e.surjective]

namespace IntegralAffineEmbedding

variable {d n : ℕ} (e : IntegralAffineEmbedding d n)

/-- Relative interior commutes with the actual affine lattice chart. -/
theorem intrinsicInterior_image (S : Set (Ambient d)) :
    intrinsicInterior ℝ (e.realMap '' S) = e.realMap '' intrinsicInterior ℝ S := by
  let τ := AffineEquiv.constVAdd ℝ (Ambient n) (embed n e.origin)
  have himage : e.realMap '' S = τ '' (e.realLinear '' S) := by
    rw [Set.image_image]
    rfl
  rw [himage, τ.intrinsicInterior_image,
    intrinsicInterior_linear_image e.realLinear e.injective, Set.image_image]
  rfl

/-- Interior lattice points in source coordinates correspond exactly to
relative-interior ambient lattice points, with no omitted lattice classes. -/
theorem lattice_intrinsicInterior_image_iff (S : Set (Ambient d)) (z : Lattice n) :
    embed n z ∈ intrinsicInterior ℝ (e.realMap '' S) ↔
      ∃ w : Lattice d, embed d w ∈ intrinsicInterior ℝ S ∧ e.latticeMap w = z := by
  rw [e.intrinsicInterior_image]
  exact e.lattice_image_membership (intrinsicInterior ℝ S) z

/-- For a full-dimensional coordinate polytope, the source intrinsic interior
in the previous equivalence is its ordinary topological interior. -/
theorem lattice_interior_image_iff (P : LatticePolytope d) (z : Lattice n) :
    embed n z ∈ intrinsicInterior ℝ (e.realMap '' P.carrier) ↔
      ∃ w : Lattice d, embed d w ∈ interior P.carrier ∧ e.latticeMap w = z := by
  rw [e.lattice_intrinsicInterior_image_iff,
    intrinsicInterior_eq_interior_of_fullSpan P.carrier P.fullDimensional]

/-- Scale only the chart's integral origin; the saturated direction lattice
and its coordinate map remain unchanged. -/
def scaleOrigin (k : ℕ) : IntegralAffineEmbedding d n where
  origin := (k : ℤ) • e.origin
  linear := e.linear
  realLinear := e.realLinear
  injective := e.injective
  compatible := e.compatible
  saturated := e.saturated

/-- Dilating the coordinate set and the chart origin gives the ordinary
ambient dilation, including the translation multiplicity. -/
theorem scaleOrigin_image (k : ℕ) (S : Set (Ambient d)) :
    (e.scaleOrigin k).realMap '' ((k : ℝ) • S) = (k : ℝ) • (e.realMap '' S) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e.realMap x, ⟨x, hx, rfl⟩, ?_⟩
    simp only [realMap_apply, scaleOrigin, embed_int_smul, Int.cast_natCast,
      map_smul, smul_add]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(k : ℝ) • x, ⟨x, hx, rfl⟩, ?_⟩
    simp only [realMap_apply, scaleOrigin, embed_int_smul, Int.cast_natCast,
      map_smul, smul_add]

/-- The double-origin chart records the sum of two affine lattice images. -/
theorem scaleOrigin_two_latticeMap (x y : Lattice d) :
    (e.scaleOrigin 2).latticeMap (x + y) = e.latticeMap x + e.latticeMap y := by
  simp only [latticeMap, scaleOrigin, map_add]
  abel

/-- A nonzero dilation of a full-dimensional coordinate polytope still has
ordinary interior equal to intrinsic interior. -/
theorem intrinsicInterior_dilate_eq_interior (P : LatticePolytope d)
    (r : ℝ) (hr : r ≠ 0) :
    intrinsicInterior ℝ (r • P.carrier) = interior (r • P.carrier) := by
  rw [PaperVerification.ToricExchange.intrinsicInterior_smul r hr,
    intrinsicInterior_eq_interior_of_fullSpan P.carrier P.fullDimensional,
    interior_smul₀ hr]

/-- Relative-interior lattice targets in twice an affine face have exactly
ordinary-interior lattice coordinates in twice the coordinate polytope. -/
theorem lattice_intrinsicInterior_twice_image_iff (P : LatticePolytope d) (z : Lattice n) :
    embed n z ∈ intrinsicInterior ℝ ((2 : ℝ) • (e.realMap '' P.carrier)) ↔
      ∃ w : Lattice d, embed d w ∈ interior ((2 : ℝ) • P.carrier) ∧
        (e.scaleOrigin 2).latticeMap w = z := by
  have hdilate : (e.scaleOrigin 2).realMap '' ((2 : ℝ) • P.carrier) =
      (2 : ℝ) • (e.realMap '' P.carrier) := by
    simpa using e.scaleOrigin_image 2 P.carrier
  rw [← hdilate,
    (e.scaleOrigin 2).lattice_intrinsicInterior_image_iff,
    intrinsicInterior_dilate_eq_interior P (2 : ℝ) (by norm_num)]

end IntegralAffineEmbedding

end PaperVerification.ToricGeometry
