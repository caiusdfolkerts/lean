module

public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.Matrix
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Instances.Matrix
public import volume_polynomials.mixed_volume_basis
public import mixed_volume.general.rejection_arithmetic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import TauCeti.Analysis.Convex.Measure
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FunProp
public import mixed_volume.computability.rational_primrec
public import mixed_volume.general.geometry_arithmetic
public import mixed_volume.computability.effective_pfa
public import mixed_volume.all.padding
public import mixed_volume.general.automaton_bridge
public import mixed_volume.general.realization_forward
public import mixed_volume.computability.fixed_automata_all
public import mixed_volume.general.automaton_moments
public import mixed_volume.all
public import mixed_volume.all.neighborhood

/-! Four-unit verification layout. The bodies below are copied exactly from
reviewed component sources; generation alone establishes no theorem. -/

/- BEGIN FORMER UNIT: MixedVolume.General.RejectionSeparation -/
section

/-! Standby source partition. Generation is not a proof certificate.
Exact copied proof ranges are recorded in the adjacent manifest. -/

/- BEGIN SOURCE: support/TauCeti/LinearAlgebra/AffineSpace/Basis.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Affine equivalences between affine bases

Two affine bases indexed by the same type are related by an affine equivalence: there is an affine
equivalence sending the points of one basis to the corresponding points of the other
(`AffineBasis.exists_affineEquiv_apply_eq`), and every affine map that does so preserves
barycentric coordinates (`AffineBasis.coord_apply_of_forall_apply_eq`). This is how a statement
about barycentric coordinates relative to an arbitrary affine basis is reduced to one about a
fixed reference basis.

The file also computes the barycentric coordinates of a point after a homothety about the centroid
of an affine basis (`AffineBasis.coord_homothety_centroid`), which describes the homothetic images
of the simplex spanned by the basis.

## Main statements

* `AffineBasis.coord_apply_of_forall_apply_eq`: an affine map sending the affine basis `b` to the
  affine basis `b₂` carries barycentric coordinates relative to `b` to those relative to `b₂`;
* `AffineBasis.exists_affineEquiv_apply_eq`: there is an affine equivalence sending `b` to `b₂`;
* `AffineBasis.coord_homothety_centroid`: the barycentric coordinates of the image of a point under
  a homothety about the centroid of an affine basis.
-/

public section

namespace AffineBasis

variable {ι k V P V₂ P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] (b : AffineBasis ι k P)
  (b₂ : AffineBasis ι k P₂)

/-- An affine map sending each point `b i` of an affine basis to the point `b₂ i` of another affine
basis preserves barycentric coordinates. -/
theorem coord_apply_of_forall_apply_eq {f : P →ᵃ[k] P₂} (hf : ∀ i, f (b i) = b₂ i) (i : ι)
    (x : P) : b₂.coord i (f x) = b.coord i x := by
  have h : (b₂.coord i).comp f = b.coord i := by
    refine AffineMap.ext_on b.tot ?_
    rintro - ⟨j, rfl⟩
    rcases eq_or_ne i j with rfl | hij
    · simp [hf, coord_apply_eq]
    · simp [hf, coord_apply_ne _ hij]
  exact congr($h x)

/-- Two affine bases indexed by the same type are related by an affine equivalence sending each
point of the first basis to the corresponding point of the second. -/
theorem exists_affineEquiv_apply_eq : ∃ T : P ≃ᵃ[k] P₂, ∀ i, T (b i) = b₂ i := by
  obtain ⟨i₀⟩ := b.nonempty
  -- Translate `b i₀` to the origin, map the linear basis `b.basisOf i₀` to `b₂.basisOf i₀`, and
  -- translate the origin to `b₂ i₀`.
  let L : V ≃ₗ[k] V₂ := (b.basisOf i₀).equiv (b₂.basisOf i₀) (Equiv.refl _)
  refine ⟨((AffineEquiv.vaddConst k (b i₀)).symm.trans L.toAffineEquiv).trans
    (AffineEquiv.vaddConst k (b₂ i₀)), fun i => ?_⟩
  rcases eq_or_ne i i₀ with rfl | hi
  · simp
  · have hL : L (b i -ᵥ b i₀) = b₂ i -ᵥ b₂ i₀ := by
      rw [← b.basisOf_apply i₀ ⟨i, hi⟩, Module.Basis.equiv_apply, Equiv.refl_apply,
        basisOf_apply]
    simp [hL]

end AffineBasis

namespace AffineBasis

variable {ι k V P : Type*} [Fintype ι] [Field k] [CharZero k] [AddCommGroup V] [Module k V]
  [AddTorsor V P] (b : AffineBasis ι k P)

/-- The barycentric coordinates relative to an affine basis `b` of the image of a point `z` under
the homothety of ratio `t` about the centroid of `b`: the homothety moves each coordinate
`b.coord i z` towards the centroid's coordinate `1 / card ι` by the factor `t`. -/
theorem coord_homothety_centroid (t : k) (z : P) (i : ι) :
    b.coord i (AffineMap.homothety (Finset.univ.centroid k b) t z) =
      (1 - t) / Fintype.card ι + t * b.coord i z := by
  rw [AffineMap.homothety_eq_lineMap, AffineMap.apply_lineMap,
    b.coord_apply_centroid (Finset.mem_univ i), Finset.card_univ, AffineMap.lineMap_apply_ring']
  ring

end AffineBasis
end -- original EOF section
end -- component scope
/- END SOURCE: support/TauCeti/LinearAlgebra/AffineSpace/Basis.lean -/

/- BEGIN SOURCE: support/TauCeti/LinearAlgebra/AffineSpace/Matrix.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Determinants of matrices of barycentric coordinates

Fix an affine basis `b` of an affine space `P`. For a family `q` of points of `P`, the matrix
`b.toMatrix q` has the barycentric coordinates of `q i` with respect to `b` as its rows, and when
`q` is indexed like `b` its determinant is the signed (oriented) volume of the simplex with vertices
`q i`, measured relative to the simplex of `b`; the unsigned relative volume is its absolute value.

Replacing the vertex `q i` of an affine basis `q` by a point `x` scales this determinant by the
barycentric coordinate of `x` at `i` with respect to `q`
(`AffineBasis.det_toMatrix_update`). This is Cramer's rule for barycentric coordinates
(`AffineBasis.det_smul_coords_eq_cramer_coords`) read as a statement about volumes, and it is the
reason a simplex of maximal volume inside a set controls the barycentric coordinates of all points
of the set.

## Main statements

* `AffineBasis.toMatrix_update`: replacing a point of the family replaces the corresponding row by
  its barycentric coordinates;
* `AffineBasis.det_toMatrix_update`: replacing the vertex `q i` of an affine basis `q` by `x`
  multiplies the determinant by `q.coord i x`.
-/

public section

open Matrix

namespace AffineBasis

variable {ι ι' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

/-- Replacing the point `q i` of a family by `x` replaces the `i`-th row of the matrix of
barycentric coordinates by the coordinates of `x`. -/
@[simp]
theorem toMatrix_update [DecidableEq ι'] (q : ι' → P) (i : ι') (x : P) :
    b.toMatrix (Function.update q i x) = (b.toMatrix q).updateRow i (b.coords x) := by
  ext j l
  rcases eq_or_ne j i with rfl | hj
  · simp [toMatrix_apply]
  · simp [toMatrix_apply, hj]

end Ring

section CommRing

variable [CommRing k] [Module k V] [Fintype ι] [DecidableEq ι] (b b₂ : AffineBasis ι k P)

/-- Replacing the vertex `b₂ i` of the affine basis `b₂` by a point `x` multiplies the determinant
of the matrix of barycentric coordinates relative to `b` by the barycentric coordinate of `x` at
`i` with respect to `b₂`. -/
theorem det_toMatrix_update (i : ι) (x : P) :
    (b.toMatrix (Function.update b₂ i x)).det = (b.toMatrix b₂).det * b₂.coord i x := by
  have h := congr_fun (b.det_smul_coords_eq_cramer_coords b₂ x) i
  rw [Pi.smul_apply, coords_apply, smul_eq_mul, cramer_apply, updateCol_transpose,
    det_transpose] at h
  rw [toMatrix_update, h]

end CommRing

end AffineBasis
end -- original EOF section
end -- component scope
/- END SOURCE: support/TauCeti/LinearAlgebra/AffineSpace/Matrix.lean -/

/- BEGIN SOURCE: support/TauCeti/Analysis/Convex/AffineNormalization.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Affine normalization of convex bodies

A convex body in an `n`-dimensional real affine space can be moved by an affine equivalence to a
position between two balls whose radii depend only on the space. This is the normalization that
lets estimates for convex sets be proved for sets of unit size and transferred back; in the
regularity theory of the Monge–Ampère equation it is applied to the sections
`{y | u y < u x + ⟪p, y - x⟫ + h}` of a convex function `u`.

The normalization comes from a simplex of maximal volume. Let `K` be a compact set whose affine
span is the whole `n`-dimensional space, and choose `n + 1` points of `K` spanning a simplex of
maximal volume, where volume is measured by the absolute value of the determinant of the matrix of
barycentric coordinates relative to a fixed affine basis (the determinant itself is the signed
volume). Replacing the vertex `b i` by a point `x` multiplies this determinant by the barycentric
coordinate `b.coord i x` (`AffineBasis.det_toMatrix_update`), so maximality of its absolute value
forces `|b.coord i x| ≤ 1` for every `x ∈ K`
(`IsCompact.exists_affineBasis_abs_coord_le_one`).

In terms of the simplex `Δ = convexHull (range b)` with centroid `c`, the points whose barycentric
coordinates are all at most `1` form the image of `Δ` under the homothety of ratio `-n` about `c`
(`AffineBasis.mem_image_homothety_convexHull_iff`). Thus every compact spanning `K` contains the
vertices of a simplex `Δ` and lies inside its homothetic image of ratio `-n`
(`IsCompact.exists_affineBasis_subset_image_homothety_convexHull`); when `K` is convex it contains
`Δ` itself. Mapping `Δ` to a fixed reference simplex by an affine equivalence then gives the
normalization by balls (`TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`).

John's theorem gives the sharper statement in which the simplex is replaced by the ellipsoid of
maximal volume and the ratio `-n` by `n`, or by `√n` for centrally symmetric bodies. For the
normalization, a ratio depending only on the dimension suffices.

## Main statements

* `IsCompact.exists_affineBasis_abs_coord_le_one`: a compact set spanning a finite-dimensional real
  affine space contains an affine basis relative to which all its points have barycentric
  coordinates in `[-1, 1]`;
* `AffineBasis.mem_image_homothety_convexHull_iff`: the image of the simplex of an affine basis
  under the homothety of ratio `-n` about its centroid is the set of points whose barycentric
  coordinates are at most `1`;
* `IsCompact.exists_affineBasis_subset_image_homothety_convexHull`: a compact spanning set contains
  the vertices of a simplex and lies in the image of that simplex under the homothety of ratio `-n`
  about its centroid;
* `TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`: in a finite-dimensional real normed
  space there is `r > 0` such that every bounded convex set with nonempty interior is mapped by
  some affine equivalence to a set between the balls of radii `r` and `1` about `0`.

## References

* F. John, *Extremum problems with inequalities as subsidiary conditions*, Studies and Essays
  Presented to R. Courant on his 60th Birthday, Interscience, 1948, 187–204.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.8 (normalized convex sets).
* K. Ball, *An elementary introduction to modern convex geometry*, in *Flavors of Geometry*,
  MSRI Publications 31, Cambridge University Press, 1997, Lecture 3.
-/

public section

open Set Module Metric

/-! ### A simplex of maximal volume -/

section Compact

variable {ι V P : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [PseudoMetricSpace P] [NormedAddTorsor V P]

/-- **Affine bases with bounded barycentric coordinates.** A compact set `K` whose affine span is
the whole finite-dimensional real affine space contains an affine basis `b`, indexed by any type
with `finrank + 1` elements, such that every point of `K` has all its barycentric coordinates
relative to `b` in `[-1, 1]`. -/
theorem IsCompact.exists_affineBasis_abs_coord_le_one {K : Set P} (hK : IsCompact K)
    (hspan : affineSpan ℝ K = ⊤) (hι : Fintype.card ι = finrank ℝ V + 1) :
    ∃ b : AffineBasis ι ℝ P, (∀ i, b i ∈ K) ∧ ∀ x ∈ K, ∀ i, |b.coord i x| ≤ 1 := by
  classical
  -- A reference affine basis with vertices in `K`.
  obtain ⟨s, hsK, b₀, hb₀⟩ := AffineBasis.exists_affine_subbasis hspan
  lift s to Finset P using b₀.setFinite
  let b₁ : AffineBasis ι ℝ P :=
    b₀.reindex (Fintype.equivOfCardEq (by rw [hι, ← b₀.card_eq_finrank_add_one]))
  have hb₁ : ∀ i, b₁ i ∈ K := fun i => by
    simp only [b₁, AffineBasis.reindex_apply, hb₀]
    exact hsK (Subtype.prop _)
  -- Choose vertices in `K` maximizing the volume `|det|` relative to `b₁`.
  let f : (ι → P) → ℝ := fun q => |(b₁.toMatrix q).det|
  -- Continuity goes through the linear part: Mathlib's `continuous_barycentric_coord` assumes
  -- `MetricSpace P`, which this pseudometric setting does not provide.
  have hcoord : ∀ j, Continuous (b₁.coord j) := fun j =>
    AffineMap.continuous_linear_iff.1 (b₁.coord j).linear.continuous_of_finiteDimensional
  have hf : Continuous f :=
    ((continuous_matrix fun i j => (hcoord j).comp (continuous_apply i)).matrix_det).abs
  obtain ⟨q, hqK, hq⟩ := (isCompact_univ_pi fun _ => hK).exists_isMaxOn
    ⟨b₁, fun i _ => hb₁ i⟩ hf.continuousOn
  have hfq : 0 < f q := by
    have hb₁K : (b₁ : ι → P) ∈ univ.pi fun _ => K := fun i _ => hb₁ i
    have := hq hb₁K
    simp only [mem_ofPred_eq, b₁.toMatrix_self, Matrix.det_one, abs_one, f] at this
    linarith
  -- A family of points of nonzero volume is an affine basis.
  obtain ⟨hind, htot⟩ := (b₁.isUnit_toMatrix_iff q).1 <|
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (abs_pos.1 hfq))
  let b : AffineBasis ι ℝ P := ⟨q, hind, htot⟩
  have hbq : (b : ι → P) = q := rfl
  have hbK : ∀ j, b j ∈ K := fun j => hbq ▸ hqK j (mem_univ j)
  refine ⟨b, hbK, fun x hx i => ?_⟩
  -- Replacing the vertex `b i` by `x` multiplies the volume by `|b.coord i x|`.
  have hle : f (Function.update b i x) ≤ f b := by
    rw [hbq]
    refine hq fun j _ => ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hx
    · simpa [hj, hbq] using hbK j
  have hupdate : f (Function.update b i x) = f b * |b.coord i x| := by
    simp only [f, b₁.det_toMatrix_update b, abs_mul]
  rw [hupdate] at hle
  exact (mul_le_iff_le_one_right (hbq ▸ hfq)).1 hle

end Compact

/-! ### The homothetic image of a simplex -/

section Homothety

variable {ι k E : Type*} [Fintype ι] [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [Module k E] (b : AffineBasis ι k E)

/-- The image of the simplex spanned by an affine basis of an `n`-dimensional space under the
homothety of ratio `-n` about its centroid is the set of points whose barycentric coordinates are
all at most `1`. -/
theorem AffineBasis.mem_image_homothety_convexHull_iff {x : E} :
    x ∈ AffineMap.homothety (Finset.univ.centroid k b) (-(finrank k E : k)) ''
        convexHull k (range b) ↔ ∀ i, b.coord i x ≤ 1 := by
  have hn : (0 : k) ≤ finrank k E := Nat.cast_nonneg _
  have hn1 : (finrank k E : k) + 1 ≠ 0 := by positivity
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    rw [b.convexHull_eq_nonneg_coord] at hz
    rw [b.coord_homothety_centroid, b.card_eq_finrank_add_one, Nat.cast_add_one,
      div_eq_one_iff_eq hn1 |>.2 (by ring)]
    nlinarith [hz i]
  · intro hx
    rcases hn.eq_or_lt with h0 | hpos
    · -- In dimension zero the homothety is constant and the space is a point.
      have : Subsingleton E := by
        have := b.finiteDimensional
        exact finrank_zero_iff.1 (by exact_mod_cast h0.symm)
      obtain ⟨i⟩ := b.nonempty
      exact ⟨b i, subset_convexHull k _ (mem_range_self i), Subsingleton.elim _ _⟩
    · refine ⟨AffineMap.homothety (Finset.univ.centroid k b) (-(finrank k E : k)⁻¹) x, ?_, ?_⟩
      · rw [b.convexHull_eq_nonneg_coord]
        intro i
        rw [b.coord_homothety_centroid, b.card_eq_finrank_add_one, Nat.cast_add_one]
        have := hx i
        field_simp
        nlinarith
      · rw [← AffineMap.homothety_mul_apply, neg_mul_neg, mul_inv_cancel₀ hpos.ne',
          AffineMap.homothety_one, AffineMap.id_apply]

end Homothety

section CompactHomothety

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Affine normalization of compact sets.** A compact set `K` whose affine span is the whole
`n`-dimensional real normed space contains the vertices of a simplex `Δ` and lies in the image of
`Δ` under the homothety of ratio `-n` about the centroid of `Δ`. When `K` is convex, it also
contains `Δ`, by `convexHull_min`. -/
theorem IsCompact.exists_affineBasis_subset_image_homothety_convexHull {K : Set E}
    (hK : IsCompact K) (hspan : affineSpan ℝ K = ⊤) (hι : Fintype.card ι = finrank ℝ E + 1) :
    ∃ b : AffineBasis ι ℝ E, (∀ i, b i ∈ K) ∧
      K ⊆ AffineMap.homothety (Finset.univ.centroid ℝ b) (-(finrank ℝ E : ℝ)) ''
        convexHull ℝ (range b) := by
  obtain ⟨b, hbK, hb⟩ := hK.exists_affineBasis_abs_coord_le_one hspan hι
  exact ⟨b, hbK, fun x hx => b.mem_image_homothety_convexHull_iff.2 fun i =>
    (le_abs_self _).trans (hb x hx i)⟩

end CompactHomothety

/-! ### Normalization by balls -/

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- **Normalization of convex bodies.** In a finite-dimensional real normed space `E` there is a
radius `r > 0`, depending only on `E`, such that every bounded convex set `s` with nonempty
interior is mapped by some affine equivalence `T` to a set between the balls of radii `r` and `1`
about `0`. -/
theorem exists_affineEquiv_ball_subset_image_subset_ball :
    ∃ r > 0, ∀ s : Set E, Convex ℝ s → Bornology.IsBounded s → (interior s).Nonempty →
      ∃ T : E ≃ᵃ[ℝ] E, ball 0 r ⊆ T '' s ∧ T '' s ⊆ ball 0 1 := by
  -- A reference simplex: its interior contains a ball about its centroid `c`, and the points with
  -- barycentric coordinates in `[-1, 1]` lie in the ball of radius `∑ i, ‖b₁ i‖` about `0`.
  let ι := Fin (finrank ℝ E + 1)
  have hι : Fintype.card ι = finrank ℝ E + 1 := Fintype.card_fin _
  obtain ⟨b₁⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional (k := ℝ) (P := E) hι
  set c := Finset.univ.centroid ℝ b₁
  have hc : c ∈ interior (convexHull ℝ (range b₁)) := b₁.centroid_mem_interior_convexHull
  rw [b₁.interior_convexHull] at hc
  have hopen : IsOpen {y | ∀ i, 0 < b₁.coord i y} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (continuous_barycentric_coord b₁ i)
  obtain ⟨ρ, hρ, hball⟩ := isOpen_iff.1 hopen c hc
  have hbound : ∀ y, (∀ i, |b₁.coord i y| ≤ 1) → ‖y‖ ≤ ∑ i, ‖b₁ i‖ := fun y hy => by
    conv_lhs => rw [← b₁.linear_combination_coord_eq_self y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hy i)
  set R := ∑ i, ‖b₁ i‖ + ‖c‖ + 1
  have hR : 0 < R := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => norm_nonneg (b₁ i)
    have := norm_nonneg c
    linarith
  refine ⟨ρ / R, div_pos hρ hR, fun s hs hsb hsi => ?_⟩
  -- An affine basis in the closure of `s` relative to which the barycentric coordinates of the
  -- points of the closure lie in `[-1, 1]`.
  have hspan : affineSpan ℝ (closure s) = ⊤ :=
    top_unique <| (isOpen_interior.affineSpan_eq_top hsi).symm.le.trans
      (affineSpan_mono ℝ (interior_subset.trans subset_closure))
  obtain ⟨b, hbs, hb⟩ := hsb.isCompact_closure.exists_affineBasis_abs_coord_le_one hspan hι
  -- Move it onto the reference simplex, then recentre at `0` and rescale by `R⁻¹`.
  obtain ⟨T₀, hT₀⟩ := b.exists_affineEquiv_apply_eq b₁
  have hcoord : ∀ x i, b₁.coord i (T₀ x) = b.coord i x := fun x i =>
    b.coord_apply_of_forall_apply_eq b₁ (f := T₀.toAffineMap) hT₀ i x
  let T : E ≃ᵃ[ℝ] E := (T₀.trans (AffineEquiv.constVAdd ℝ E (-c))).trans
    (AffineEquiv.homothetyUnitsMulHom (0 : E) (Units.mk0 R⁻¹ (inv_ne_zero hR.ne')))
  have hT : ∀ x, T x = R⁻¹ • (T₀ x - c) := fun x => by
    simp [T, AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply,
      neg_add_eq_sub]
  refine ⟨T, fun y hy => ?_, ?_⟩
  · -- The preimage of a small ball lies in the interior of the simplex of `b`, inside `s`.
    have hy' : T₀.symm (c + R • y) ∈ s := by
      have hpos : ∀ i, 0 < b.coord i (T₀.symm (c + R • y)) := fun i => by
        rw [← hcoord, AffineEquiv.apply_symm_apply]
        refine hball ?_ i
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
        rw [mem_ball_zero_iff, lt_div_iff₀ hR] at hy
        linarith
      have hhull : convexHull ℝ (range b) ⊆ closure s :=
        convexHull_min (range_subset_iff.2 hbs) hs.closure
      have hmem : T₀.symm (c + R • y) ∈ interior (convexHull ℝ (range b)) := by
        rw [b.interior_convexHull]
        exact hpos
      exact interior_subset (hs.interior_closure_eq_interior_of_nonempty_interior hsi ▸
        interior_mono hhull hmem)
    refine ⟨_, hy', ?_⟩
    rw [hT, AffineEquiv.apply_symm_apply, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ hR.ne', one_smul]
  · -- The image of `s` lies within distance `R - 1` of `c` before rescaling.
    rintro - ⟨x, hx, rfl⟩
    have hle := hbound (T₀ x) fun i => by
      rw [hcoord]
      exact hb x (subset_closure hx) i
    rw [mem_ball_zero_iff, hT, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
      inv_mul_lt_iff₀ hR, mul_one]
    linarith [norm_sub_le (T₀ x) c]

end TauCeti
end -- original EOF section
end -- component scope
/- END SOURCE: support/TauCeti/Analysis/Convex/AffineNormalization.lean -/

/- BEGIN SOURCE: VolumePolynomials/VolumeLipschitz.lean -/
section

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# An explicit volume modulus on a bounded box

Coefficient nonnegativity bounds the volume added by a small Minkowski summand.
Hausdorff distance in `Space d` is the supremum norm, so its unit ball is a cube.
Combining these facts gives a rational uniform modulus for the effective nets.
This follows polynomiality; the qualitative continuity used to prove
polynomiality was established independently by dominated convergence.
-/

open Set MeasureTheory Finset Metric
open scoped Pointwise BigOperators

namespace VolumePolynomials

def coordinateCube (d : ℕ) : Body d where
  carrier := Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))
  convex' := convex_Icc _ _
  isCompact' := isCompact_Icc
  nonempty' := ⟨0, ⟨fun _ => neg_nonpos.mpr zero_le_one, fun _ => zero_le_one⟩⟩

/-- Every nonconstant power of a number in `[0,1]` is bounded by that number. -/
theorem bodyVolume_add_smul_sub_le {d : ℕ} (K L : Body d) {h : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    bodyVolume (K + h • L) - bodyVolume K ≤ h * bodyVolume (K + L) := by
  first
  | obtain ⟨c, hc, hr⟩ := exists_nonnegative_volume_polynomial ![K, L]
    have heval (s : ℝ) (hs : 0 ≤ s) :
        (∑ α : MultiIndex 2 d, c α * s ^ (α.1 1 : ℕ)) = bodyVolume (K + s • L) := by
      first
      | have hnonneg : ∀ i : Fin 2, 0 ≤ (![1, s] : Fin 2 → ℝ) i := by
          intro i
          fin_cases i <;> simp [hs]
        simpa [evaluate, volumeFunction, weightedSum, Fin.sum_univ_two,
          Fin.prod_univ_two] using hr ![1, s] hnonneg
    have heval0 : (∑ α : MultiIndex 2 d, c α * (0 : ℝ) ^ (α.1 1 : ℕ)) = bodyVolume K := by
      first
      | simpa only [body_zero_smul, add_zero] using heval 0 le_rfl
    have heval1 : (∑ α : MultiIndex 2 d, c α) = bodyVolume (K + L) := by
      first
      | simpa only [one_pow, mul_one, one_smul] using heval 1 zero_le_one
    rw [← heval h hh0, ← heval0, ← heval1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α _
    by_cases hk : (α.1 1 : ℕ) = 0
    · simpa only [hk, pow_zero, mul_one, sub_self] using mul_nonneg hh0 (hc α)
    · simp only [zero_pow hk, mul_zero, sub_zero]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (pow_le_of_le_one hh0 hh1 hk) (hc α)

/-- Hausdorff control gives literal Minkowski containment in the coordinate cube. -/
theorem body_le_add_coordinateCube_of_dist_le {d : ℕ} (K L : Body d)
    {h : ℝ} (hh : 0 ≤ h) (hKL : dist K L ≤ h) : K ≤ L + h • coordinateCube d := by
  first
  | rcases hh.eq_or_lt with heq | hpos
    · have hz : h = 0 := heq.symm
      rw [hz] at hKL ⊢
      have hsame : K = L := dist_le_zero.mp hKL
      rw [hsame, body_zero_smul, add_zero]
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
      have hnorm : ‖x - y‖ ≤ h := by
        first
        | rw [← dist_eq_norm, ← hxy]
          exact (infDist_le_hausdorffDist_of_mem hx ConvexBody.hausdorffEDist_ne_top).trans hKL
      let u : Space d := h⁻¹ • (x - y)
      have hu : u ∈ coordinateCube d := by
        first
        | have habs : ∀ i, |u i| ≤ 1 := by
            intro i
            have hi : |(x - y) i| ≤ h := by
              calc
                |(x - y) i| = ‖(x - y) i‖ := (Real.norm_eq_abs _).symm
                _ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
                _ ≤ h := hnorm
            change |h⁻¹ * (x - y) i| ≤ 1
            rw [abs_mul, abs_inv, abs_of_pos hpos]
            calc
              h⁻¹ * |(x - y) i| ≤ h⁻¹ * h :=
                mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hpos.le)
              _ = 1 := inv_mul_cancel₀ hpos.ne'
          exact ⟨fun i => (abs_le.mp (habs i)).1, fun i => (abs_le.mp (habs i)).2⟩
      have hscaled : h • u = x - y := by
        first
        | simp only [u, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      exact Set.mem_add.mpr ⟨y, hy, x - y, ⟨u, hu, hscaled⟩, by abel⟩

theorem bodyVolume_add_coordinateCube_le {d : ℕ} (K : Body d) {R : ℝ}
    (hR : 0 ≤ R) (hK : (K : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R)) :
    bodyVolume (K + coordinateCube d) ≤ (2 * R + 2) ^ d := by
  first
  | have hsub : ((K + coordinateCube d : Body d) : Set (Space d)) ⊆
        Icc (fun _ => -(R + 1)) (fun _ => R + 1) := by
      first
      | rintro _ ⟨x, hx, y, hy, rfl⟩
        have hx' := hK hx
        change y ∈ Icc (fun _ : Fin d => (-1 : ℝ)) (fun _ => (1 : ℝ)) at hy
        constructor
        · intro i
          change -(R + 1) ≤ x i + y i
          linarith [hx'.1 i, hy.1 i]
        · intro i
          change x i + y i ≤ R + 1
          linarith [hx'.2 i, hy.2 i]
    have hbound := measureReal_mono hsub
      (show volume (Icc (fun _ : Fin d => -(R + 1)) (fun _ => R + 1)) ≠ ⊤ from
        isCompact_Icc.measure_lt_top.ne)
    have hbox : volume.real (Icc (fun _ : Fin d => -(R + 1)) (fun _ => R + 1)) =
        (2 * R + 2) ^ d := by
      first
      | rw [measureReal_def, Real.volume_Icc_pi_toReal
          (show (fun _ : Fin d => -(R + 1)) ≤ (fun _ => R + 1) from
            fun _ => by linarith)]
        simp only [show R + 1 - -(R + 1) = 2 * R + 2 by ring,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact hbound.trans_eq hbox

/-- Explicit uniform continuity of volume on all convex bodies in the box,
including arbitrarily thin and lower-dimensional ones. -/
theorem abs_bodyVolume_sub_le_of_dist_le {d : ℕ} (K L : Body d) {R h : ℝ}
    (hR : 0 ≤ R) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hK : (K : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R))
    (hL : (L : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R))
    (hKL : dist K L ≤ h) :
    |bodyVolume K - bodyVolume L| ≤ h * (2 * R + 2) ^ d := by
  first
  | have hforward : bodyVolume K - bodyVolume L ≤ h * (2 * R + 2) ^ d := by
      first
      | calc
          _ ≤ bodyVolume (L + h • coordinateCube d) - bodyVolume L :=
            sub_le_sub_right (bodyVolume_mono (body_le_add_coordinateCube_of_dist_le K L hh0 hKL)) _
          _ ≤ h * bodyVolume (L + coordinateCube d) := bodyVolume_add_smul_sub_le L _ hh0 hh1
          _ ≤ h * (2 * R + 2) ^ d :=
            mul_le_mul_of_nonneg_left (bodyVolume_add_coordinateCube_le L hR hL) hh0
    have hreverse : bodyVolume L - bodyVolume K ≤ h * (2 * R + 2) ^ d := by
      first
      | calc
          _ ≤ bodyVolume (K + h • coordinateCube d) - bodyVolume K :=
            sub_le_sub_right (bodyVolume_mono (body_le_add_coordinateCube_of_dist_le L K hh0
              (by rwa [dist_comm]))) _
          _ ≤ h * bodyVolume (K + coordinateCube d) := bodyVolume_add_smul_sub_le K _ hh0 hh1
          _ ≤ h * (2 * R + 2) ^ d :=
            mul_le_mul_of_nonneg_left (bodyVolume_add_coordinateCube_le K hR hK) hh0
    exact abs_le.mpr ⟨by linarith, hforward⟩

end VolumePolynomials
end -- original EOF section
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/VolumeLipschitz.lean -/

/- BEGIN SOURCE: VolumePolynomials/CoefficientModulus.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# A rational modulus for all ordinary coefficients

The coefficient map is controlled by the literal Hausdorff distances of the
input bodies. The constants are explicit rational expressions in the dimension,
number of bodies, box radius, and rational interpolation data. No effective
modulus is inferred merely from qualitative compactness or continuity.
-/

open Set Finset MeasureTheory Metric
open scoped Pointwise BigOperators

namespace VolumePolynomials

section Geometry

theorem exists_near_weightedSum {n d : ℕ} (K L : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {ε : ℝ}
    (hKL : ∀ i, dist (K i) (L i) ≤ ε) {x : Space d}
    (hx : x ∈ weightedSum K t) :
    ∃ y ∈ weightedSum L t, dist x y ≤ ε * ∑ i, t i := by
  first
  | classical
    obtain ⟨a, ha, hax⟩ := (mem_sum_body (fun i => t i • K i) x).mp hx
    have hpoints : ∀ i, ∃ p ∈ K i, t i • p = a i := by
      first
      | intro i
        exact Set.mem_smul_set.mp (ha i)
    choose p hp hpa using hpoints
    choose q hq hdist using fun i =>
      (L i).isCompact.exists_infDist_eq_dist (L i).nonempty (p i)
    have hpq : ∀ i, dist (p i) (q i) ≤ ε := by
      first
      | intro i
        rw [← hdist i]
        exact (infDist_le_hausdorffDist_of_mem (hp i)
          ConvexBody.hausdorffEDist_ne_top).trans (hKL i)
    have hpx : ∑ i, t i • p i = x := by
      first
      | simpa only [hpa] using hax
    refine ⟨∑ i, t i • q i, (mem_sum_body _ _).mpr
      ⟨fun i => t i • q i, fun i => ⟨q i, hq i, rfl⟩, rfl⟩, ?_⟩
    rw [← hpx, dist_eq_norm, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ‖t i • p i - t i • q i‖ := norm_sum_le _ _
      _ = ∑ i, t i * dist (p i) (q i) := by
        first
        | apply Finset.sum_congr rfl
          intro i _
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg (ht i), dist_eq_norm]
      _ ≤ ∑ i, t i * ε := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hpq i) (ht i)
      _ = ε * ∑ i, t i := by rw [← Finset.sum_mul, mul_comm]

theorem dist_weightedSum_le {n d : ℕ} (K L : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {ε : ℝ} (hε : 0 ≤ ε)
    (hKL : ∀ i, dist (K i) (L i) ≤ ε) :
    dist (weightedSum K t) (weightedSum L t) ≤ ε * ∑ i, t i := by
  first
  | change hausdorffDist (weightedSum K t : Set (Space d))
      (weightedSum L t : Set (Space d)) ≤ _
    exact hausdorffDist_le_of_mem_dist (mul_nonneg hε (Finset.sum_nonneg fun i _ => ht i))
      (fun _ hx => exists_near_weightedSum K L t ht hKL hx)
      (fun _ hy => exists_near_weightedSum L K t ht
        (fun i => by simpa only [dist_comm] using hKL i) hy)

theorem weightedSum_subset_box {n d : ℕ} (K : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {R : ℝ}
    (hK : ∀ i, (K i : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R)) :
    (weightedSum K t : Set (Space d)) ⊆
      Icc (fun _ => -(R * ∑ i, t i)) (fun _ => R * ∑ i, t i) := by
  first
  | intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_sum_body (fun i => t i • K i) x).mp hx
    have hpoints : ∀ i, ∃ p ∈ K i, t i • p = a i := by
      first
      | intro i
        exact Set.mem_smul_set.mp (ha i)
    choose p hp hpa using hpoints
    have hupper (j : Fin d) : (∑ i, a i) j ≤ R * ∑ i, t i := by
      first
      | simp only [Finset.sum_apply, ← hpa, Pi.smul_apply, smul_eq_mul]
        calc
          _ ≤ ∑ i, t i * R := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left ((hK i (hp i)).2 j) (ht i)
          _ = R * ∑ i, t i := by rw [← Finset.sum_mul, mul_comm]
    have hlower (j : Fin d) : -(R * ∑ i, t i) ≤ (∑ i, a i) j := by
      first
      | simp only [Finset.sum_apply, ← hpa, Pi.smul_apply, smul_eq_mul]
        calc
          _ = ∑ i, t i * -R := by rw [← Finset.sum_mul]; ring
          _ ≤ _ := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left ((hK i (hp i)).1 j) (ht i)
    exact ⟨hlower, hupper⟩

end Geometry

/-- One strict rational bound for the sum of every interpolation weight vector. -/
def interpolationWeightBound (n d : ℕ) : ℚ :=
  1 + ∑ j : Fin (interpolationSize n d), ∑ i : Fin n, interpolationWeight j i

theorem interpolationWeightBound_pos (n d : ℕ) : 0 < interpolationWeightBound n d := by
  first
  | exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
        (interpolationWeight_pos j i).le)

theorem interpolationWeight_sum_le {n d : ℕ} (j : Fin (interpolationSize n d)) :
    (∑ i : Fin n, interpolationWeight j i) ≤ interpolationWeightBound n d := by
  first
  | apply (Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun i _ => (interpolationWeight_pos k i).le)
      (Finset.mem_univ j)).trans
    exact le_add_of_nonneg_left zero_le_one

/-- Entirely rational coefficient-modulus constant for bodies in `[-R,R]^d`. -/
def coefficientModulus (n d : ℕ) (R : ℚ) : ℚ :=
  coefficientExtractionBound n d * interpolationWeightBound n d *
    (2 * R * interpolationWeightBound n d + 2) ^ d

/-- Uniform coefficient control, including lower-dimensional bodies. The only
smallness restriction is on the approximation error, not on the geometry. -/
theorem Realizes.coefficient_sub_le_of_dist_le {n d : ℕ}
    {K L : Fin n → Body d} {c c' : Coefficients n d}
    (hc : Realizes K c) (hc' : Realizes L c') (R : ℚ) (hR : 0 ≤ R)
    (hK : ∀ i, (K i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))
    (hL : ∀ i, (L i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ε * (interpolationWeightBound n d : ℝ) ≤ 1)
    (hKL : ∀ i, dist (K i) (L i) ≤ ε) (α : MultiIndex n d) :
    |c α - c' α| ≤ ε * (coefficientModulus n d R : ℝ) := by
  first
  | let T : ℝ := interpolationWeightBound n d
    have hT : 0 < T := by
      first
      | dsimp [T]
        exact_mod_cast interpolationWeightBound_pos n d
    have hR' : 0 ≤ (R : ℝ) := by exact_mod_cast hR
    have hη : 0 ≤ ε * T * (2 * (R : ℝ) * T + 2) ^ d := by positivity
    have hsamples : ∀ j : Fin (interpolationSize n d),
        |evaluate c (fun i => (interpolationWeight j i : ℝ)) -
          evaluate c' (fun i => (interpolationWeight j i : ℝ))| ≤
            ε * T * (2 * (R : ℝ) * T + 2) ^ d := by
      first
      | intro j
        let t : Fin n → ℝ := fun i => interpolationWeight j i
        have ht : ∀ i, 0 ≤ t i := by
          intro i
          dsimp [t]
          exact_mod_cast (interpolationWeight_pos j i).le
        have hsum : ∑ i, t i ≤ T := by
          dsimp [t, T]
          exact_mod_cast interpolationWeight_sum_le j
        have hbox : ∀ P : Fin n → Body d,
            (∀ i, (P i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) →
            (weightedSum P t : Set (Space d)) ⊆
              Icc (fun _ => -((R : ℝ) * T)) (fun _ => (R : ℝ) * T) := by
          intro P hP x hx
          obtain ⟨hlo, hhi⟩ := weightedSum_subset_box P t ht hP hx
          have hbound := mul_le_mul_of_nonneg_left hsum hR'
          exact ⟨fun k => (neg_le_neg hbound).trans (hlo k),
            fun k => (hhi k).trans hbound⟩
        rw [hc _ ht, hc' _ ht]
        simpa only [volumeFunction, mul_assoc] using
          abs_bodyVolume_sub_le_of_dist_le (weightedSum K t) (weightedSum L t)
          (mul_nonneg hR' hT.le) (mul_nonneg hε hT.le) hsmall
          (hbox K hK) (hbox L hL)
          ((dist_weightedSum_le K L t ht hε hKL).trans
            (mul_le_mul_of_nonneg_left hsum hε))
    have h := abs_coefficient_sub_le_of_samples c c' hη hsamples α
    convert h using 1
    simp only [coefficientModulus, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_ofNat]
    dsimp [T]
    ring

end VolumePolynomials
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/CoefficientModulus.lean -/

/- BEGIN SOURCE: VolumePolynomials/QuadraticSeparation.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Rational quadratic separation from certified finite rational nets

This file verifies the abstract separation step used in Section 8 of
`Volume polynomials and the Heine–Shephard problem`.

It does **not** assume or assert that a particular set is a volume-polynomial
locus. Its interface records every geometric input needed to apply the result:
a closed target, finite rational approximations to that target, and certified
vanishing errors in both directions. The centers need not lie exactly in the
target. Proving these inputs for convex bodies is a separate obligation.
-/

open scoped BigOperators Topology
open Filter Metric

namespace VolumePolynomials.QuadraticSeparation

variable {ι : Type*} [Fintype ι]

abbrev Space (ι : Type*) := PiLp 2 (fun _ : ι => ℝ)

/-- A vector with rational coordinates, regarded as a Euclidean vector. -/
def ofRat (a : ι → ℚ) : Space ι := WithLp.toLp 2 (fun i => (a i : ℝ))

theorem real_norm_sq_eq (x : Space ι) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  first
  | simpa only [Real.norm_eq_abs, sq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) x)

@[simp] theorem ofRat_apply (a : ι → ℚ) (i : ι) : ofRat a i = (a i : ℝ) := rfl

theorem denseRange_ofRat : DenseRange (ofRat (ι := ι)) := by
  first
  | have h : DenseRange (fun a : ι → ℚ => fun i => (a i : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    exact (PiLp.homeomorph 2 (fun _ : ι => ℝ)).symm.surjective.denseRange.comp h
      (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))

/-- Squared distances between rational vectors can be tested using only rationals. -/
theorem dist_ofRat_sq (a b : ι → ℚ) :
    dist (ofRat a) (ofRat b) ^ 2 = ((∑ i, (a i - b i) ^ 2 : ℚ) : ℝ) := by
  first
  | rw [dist_eq_norm, real_norm_sq_eq]
    simp [ofRat, Rat.cast_sum]

/-- The precise interface supplied by the finite-net construction in Section 8.1. -/
structure Model (ι : Type*) [Fintype ι] where
  target : Set (Space ι)
  closed : IsClosed target
  net : ℕ → Finset (ι → ℚ)
  error : ℕ → ℚ
  error_nonneg : ∀ m, 0 ≤ error m
  error_tendsto : Tendsto (fun m => (error m : ℝ)) atTop (𝓝 0)
  net_near : ∀ m q, q ∈ net m →
    ∃ y ∈ target, dist (ofRat q) y ≤ (error m : ℝ)
  covers : ∀ m x, x ∈ target → ∃ q ∈ net m, dist x (ofRat q) ≤ (error m : ℝ)

namespace Model

variable (M : Model ι)

/-- The finite rational admission test (8.4), with the net's certified radius. -/
def Admitted (a : ι → ℚ) (r : ℚ) (m : ℕ) : Prop :=
  0 < r ∧ ∀ q ∈ M.net m, (r + M.error m) ^ 2 < ∑ i, (a i - q i) ^ 2

instance admittedDecidable (a : ι → ℚ) (r : ℚ) (m : ℕ) :
    Decidable (M.Admitted a r m) := by
  first
  | unfold Admitted
    infer_instance

/-- An admitted rational ball is disjoint from the target, with strict separation. -/
theorem admitted_separates {a : ι → ℚ} {r : ℚ} {m : ℕ}
    (ha : M.Admitted a r m) {x : Space ι} (hx : x ∈ M.target) :
    (r : ℝ) < dist x (ofRat a) := by
  first
  | obtain ⟨q, hq, hdist⟩ := M.covers m x hx
    have hr : 0 < (r : ℝ) := by exact_mod_cast ha.1
    have he : 0 ≤ (M.error m : ℝ) := by exact_mod_cast M.error_nonneg m
    have hsq : ((r : ℝ) + (M.error m : ℝ)) ^ 2 < dist (ofRat a) (ofRat q) ^ 2 := by
      first
      | rw [dist_ofRat_sq]
        exact_mod_cast ha.2 q hq
    have hlt : (r : ℝ) + (M.error m : ℝ) < dist (ofRat a) (ofRat q) :=
      (sq_lt_sq₀ (by positivity) dist_nonneg).mp hsq
    have htri := dist_triangle (ofRat a) x (ofRat q)
    rw [dist_comm (ofRat a) x] at htri
    linarith

/-- Every point outside the closed target belongs to an admitted rational ball. -/
theorem exists_admitted_of_not_mem {x : Space ι} (hx : x ∉ M.target) :
    ∃ a : ι → ℚ, ∃ r : ℚ, ∃ m : ℕ,
      M.Admitted a r m ∧ dist x (ofRat a) < (r : ℝ) := by
  first
  | obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp M.closed.isOpen_compl x hx
    obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp denseRange_ofRat x (δ / 8) (by positivity)
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show δ / 4 < δ / 2 by linarith)
    have hevent : ∀ᶠ m in atTop, (M.error m : ℝ) < δ / 8 :=
      M.error_tendsto.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm⟩ := hevent.exists
    have hr : 0 < (r : ℝ) := by linarith
    refine ⟨a, r, m, ⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hr
    · intro q hq
      obtain ⟨y, hy, hqy⟩ := M.net_near m q hq
      have hδy : δ ≤ dist x y := by
        first
        | by_contra! h
          exact hball (by simpa [Metric.mem_ball, dist_comm] using h) hy
      have hxy := dist_triangle x (ofRat q) y
      have htri := dist_triangle x (ofRat a) (ofRat q)
      have hlt : (r : ℝ) + (M.error m : ℝ) < dist (ofRat a) (ofRat q) := by
        first
        | linarith
      have he : 0 ≤ (M.error m : ℝ) := by exact_mod_cast M.error_nonneg m
      have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ (r : ℝ) + (M.error m : ℝ))
        dist_nonneg).mpr hlt
      rw [dist_ofRat_sq] at hsq
      exact_mod_cast hsq
    · linarith

/-- The exact rational-ball characterization before homogenizing (8.5). -/
theorem mem_iff_admitted_balls (x : Space ι) :
    x ∈ M.target ↔
      ∀ (a : ι → ℚ) (r : ℚ) (m : ℕ), M.Admitted a r m →
        (r : ℝ) ^ 2 ≤ dist x (ofRat a) ^ 2 := by
  first
  | constructor
    · intro hx a r m ha
      have hr : 0 ≤ (r : ℝ) := by exact_mod_cast ha.1.le
      exact (sq_le_sq₀ hr dist_nonneg).mpr (M.admitted_separates ha hx).le
    · intro h
      by_contra hx
      obtain ⟨a, r, m, hadm, hdist⟩ := M.exists_admitted_of_not_mem hx
      have hr : 0 ≤ (r : ℝ) := by exact_mod_cast hadm.1.le
      have hlt := (sq_lt_sq₀ dist_nonneg hr).mpr hdist
      exact (not_lt_of_ge (h a r m hadm)) hlt

/-- The finite tests at every scale characterize membership in the closed target. -/
theorem mem_iff_all_finite_tests (x : Space ι) :
    x ∈ M.target ↔ ∀ m, ∃ q ∈ M.net m, dist x (ofRat q) ≤ (M.error m : ℝ) := by
  first
  | refine ⟨fun hx m => M.covers m x hx, ?_⟩
    intro h
    by_contra hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp M.closed.isOpen_compl x hx
    obtain ⟨m, hm⟩ :=
      (M.error_tendsto.eventually (gt_mem_nhds (by positivity : 0 < δ / 2))).exists
    obtain ⟨q, hq, hdist⟩ := h m
    obtain ⟨y, hy, hqy⟩ := M.net_near m q hq
    have hxy : dist x y < δ := by
      first
      | have htri := dist_triangle x (ofRat q) y
        linarith
    exact hball (by simpa [Metric.mem_ball, dist_comm] using hxy) hy

end Model

/-- The paper's exact rational nets are a special case of the certified
approximate-net interface. This constructor makes the equivalence explicit. -/
def Model.ofExact (target : Set (Space ι)) (closed : IsClosed target)
    (net : ℕ → Finset (ι → ℚ)) (error : ℕ → ℚ)
    (error_nonneg : ∀ m, 0 ≤ error m)
    (error_tendsto : Tendsto (fun m => (error m : ℝ)) atTop (𝓝 0))
    (net_mem : ∀ m q, q ∈ net m → ofRat q ∈ target)
    (covers : ∀ m x, x ∈ target → ∃ q ∈ net m, dist x (ofRat q) ≤ (error m : ℝ)) :
    Model ι where
  target := target
  closed := closed
  net := net
  error := error
  error_nonneg := error_nonneg
  error_tendsto := error_tendsto
  net_near := by
    first
    | intro m q hq
      refine ⟨ofRat q, net_mem m q hq, ?_⟩
      have hm : 0 ≤ (error m : ℝ) := by exact_mod_cast error_nonneg m
      simpa only [dist_self] using hm
  covers := covers

/-- Sum of the ordinary coefficients. -/
def total (c : Space ι) : ℝ := ∑ i, c i

/-- Division by the coefficient sum, used only with a proved nonzero sum. -/
noncomputable def normalize (c : Space ι) : Space ι := (total c)⁻¹ • c

/-- The real quadratic form in (8.5), written intrinsically in Euclidean space. -/
noncomputable def quadratic (a : ι → ℚ) (r : ℚ) (c : Space ι) : ℝ :=
  ‖c - total c • ofRat a‖ ^ 2 - (r : ℝ) ^ 2 * total c ^ 2

theorem quadratic_eq_sum (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    quadratic a r c = ∑ i, (c i - total c * (a i : ℝ)) ^ 2 -
      (r : ℝ) ^ 2 * total c ^ 2 := by
  first
  | rw [quadratic, real_norm_sq_eq]
    rfl

@[simp] theorem total_zero : total (0 : Space ι) = 0 := by simp [total]

@[simp] theorem total_smul (t : ℝ) (c : Space ι) : total (t • c) = t * total c := by
  first
  | simp [total, Finset.mul_sum]

@[simp] theorem quadratic_zero (a : ι → ℚ) (r : ℚ) :
    quadratic a r (0 : Space ι) = 0 := by simp [quadratic]

/-- Exact homogeneity: each admitted inequality is a homogeneous quadratic. -/
theorem quadratic_smul (a : ι → ℚ) (r : ℚ) (t : ℝ) (c : Space ι) :
    quadratic a r (t • c) = t ^ 2 * quadratic a r c := by
  first
  | simp only [quadratic, total_smul, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring

theorem quadratic_eq_normalized (a : ι → ℚ) (r : ℚ) (c : Space ι)
    (hc : total c ≠ 0) :
    quadratic a r c = total c ^ 2 *
      (dist (normalize c) (ofRat a) ^ 2 - (r : ℝ) ^ 2) := by
  first
  | have heq : c - total c • ofRat a = total c • (normalize c - ofRat a) := by
      first
      | simp [normalize, smul_sub, smul_smul, hc]
    rw [quadratic, heq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, dist_eq_norm]
    ring

/-- Rational polynomial representing exactly the real quadratic form. -/
noncomputable def rationalForm (a : ι → ℚ) (r : ℚ) : MvPolynomial ι ℚ :=
  ∑ i, (MvPolynomial.X i - (∑ j, MvPolynomial.X j) * MvPolynomial.C (a i)) ^ 2 -
    MvPolynomial.C (r ^ 2) * (∑ j, MvPolynomial.X j) ^ 2

theorem eval_rationalForm (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (rationalForm a r) =
      quadratic a r c := by
  first
  | rw [quadratic_eq_sum]
    simp [rationalForm, total, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_pow, MvPolynomial.eval₂_mul]

/-- The polynomial form, not merely its evaluation, is homogeneous of degree two. -/
theorem rationalForm_isHomogeneous (a : ι → ℚ) (r : ℚ) :
    (rationalForm a r).IsHomogeneous 2 := by
  first
  | have hsum : (∑ i : ι, (MvPolynomial.X i : MvPolynomial ι ℚ)).IsHomogeneous 1 :=
      MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_X _ i)
    unfold rationalForm
    apply MvPolynomial.IsHomogeneous.sub
    · apply MvPolynomial.IsHomogeneous.sum
      intro i _
      have hlin : (MvPolynomial.X i - (∑ j, MvPolynomial.X j) *
          MvPolynomial.C (a i) : MvPolynomial ι ℚ).IsHomogeneous 1 := by
        first
        | apply (MvPolynomial.isHomogeneous_X _ i).sub
          simpa [mul_comm] using hsum.C_mul (a i)
      simpa using hlin.pow 2
    · exact (hsum.pow 2).C_mul (r ^ 2)

/-- A computable index type for the rational centers, radii, and net scales. -/
abbrev CertificateIndex (ι : Type*) := (ι → ℚ) × ℚ × ℕ

/-- Computable enumeration of the admitted descriptors, relative to the rational net data. -/
def enumeratedCertificate [Encodable ι] (M : Model ι) (k : ℕ) : Option (CertificateIndex ι) :=
  match Encodable.decode (α := CertificateIndex ι) k with
  | none => none
  | some (a, r, m) => if M.Admitted a r m then some (a, r, m) else none

/-- Every admitted descriptor is returned at its explicit natural-number code. -/
theorem enumeratedCertificate_encode [Encodable ι] (M : Model ι)
    (a : ι → ℚ) (r : ℚ) (m : ℕ) (h : M.Admitted a r m) :
    enumeratedCertificate M (Encodable.encode (a, r, m)) = some (a, r, m) := by
  first
  | simp [enumeratedCertificate, h]

/-- An explicitly computable rational matrix of coefficients for (8.5). -/
def rationalMatrix [DecidableEq ι] (a : ι → ℚ) (r : ℚ) (i j : ι) : ℚ :=
  (if i = j then 1 else 0) - a i - a j + (∑ k, a k ^ 2) - r ^ 2

theorem quadratic_expansion (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    quadratic a r c = (∑ i, c i ^ 2) -
      2 * total c * (∑ i, (a i : ℝ) * c i) +
      total c ^ 2 * ((∑ i, (a i : ℝ) ^ 2) - (r : ℝ) ^ 2) := by
  first
  | rw [quadratic_eq_sum]
    have h : (∑ i, (c i - total c * (a i : ℝ)) ^ 2) =
        (∑ i, c i ^ 2) - 2 * total c * (∑ i, (a i : ℝ) * c i) +
          total c ^ 2 * (∑ i, (a i : ℝ) ^ 2) := by
      first
      | calc
          _ = ∑ i, (c i ^ 2 - 2 * total c * ((a i : ℝ) * c i) +
              total c ^ 2 * (a i : ℝ) ^ 2) := by
            first
            | apply Finset.sum_congr rfl
              intro i _
              ring
          _ = _ := by
            first
            | simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h]
    ring

/-- The computable rational matrix evaluates to exactly (8.5), with every coefficient checked. -/
theorem quadratic_eq_matrix [DecidableEq ι] (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    quadratic a r c = ∑ i, ∑ j, (rationalMatrix a r i j : ℝ) * c i * c j := by
  first
  | rw [quadratic_expansion]
    have hdiag : (∑ i, ∑ j, ((if i = j then 1 else 0 : ℝ) * c i * c j)) =
        ∑ i, c i ^ 2 := by
      first
      | simp [sq, ite_mul]
    have hleft : (∑ i, ∑ j, (a i : ℝ) * c i * c j) =
        (∑ i, (a i : ℝ) * c i) * total c := by
      first
      | calc
          _ = ∑ i, ((a i : ℝ) * c i) * total c := by
            first
            | apply Finset.sum_congr rfl
              intro i _
              rw [total, Finset.mul_sum]
          _ = _ := (Finset.sum_mul _ _ _).symm
    have hright : (∑ i, ∑ j, (a j : ℝ) * c i * c j) =
        total c * (∑ i, (a i : ℝ) * c i) := by
      first
      | calc
          _ = ∑ i, c i * (∑ j, (a j : ℝ) * c j) := by
            first
            | apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
          _ = _ := (Finset.sum_mul _ _ _).symm
    have hconst (t : ℝ) : (∑ i, ∑ j, t * c i * c j) = t * total c ^ 2 := by
      first
      | simp only [total, sq, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    have hexpand : (∑ i, ∑ j, (rationalMatrix a r i j : ℝ) * c i * c j) =
        (∑ i, ∑ j, ((if i = j then 1 else 0 : ℝ) * c i * c j)) -
        (∑ i, ∑ j, (a i : ℝ) * c i * c j) -
        (∑ i, ∑ j, (a j : ℝ) * c i * c j) +
        (∑ i, ∑ j, ((∑ k, (a k : ℝ) ^ 2) - (r : ℝ) ^ 2) * c i * c j) := by
      first
      | simp only [rationalMatrix, Rat.cast_sub, Rat.cast_add, Rat.cast_sum, Rat.cast_pow,
          apply_ite, Rat.cast_one, Rat.cast_zero]
        simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        ring
    rw [hexpand, hdiag, hleft, hright, hconst]
    ring

/--
An explicit countable sequence of rational forms. Nonadmitted indices and unused
natural-number codes produce the zero form. Its rational descriptors are computed
by `enumeratedCertificate`; the `MvPolynomial` representation uses Mathlib's
noncomputable polynomial implementation.
-/
noncomputable def enumeratedForm [Encodable ι] (M : Model ι) (k : ℕ) : MvPolynomial ι ℚ :=
  match Encodable.decode (α := CertificateIndex ι) k with
  | none => 0
  | some (a, r, m) => if M.Admitted a r m then rationalForm a r else 0

theorem enumeratedForm_isHomogeneous [Encodable ι] (M : Model ι) (k : ℕ) :
    (enumeratedForm M k).IsHomogeneous 2 := by
  first
  | unfold enumeratedForm
    split
    · exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℚ) 2
    · split
      · exact rationalForm_isHomogeneous _ _
      · exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℚ) 2

/-- Enumerating all natural-number codes loses no admitted inequality. -/
theorem forall_enumerated_iff [Encodable ι] (M : Model ι) (c : Space ι) :
    (∀ k, 0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k)) ↔
      ∀ (a : ι → ℚ) (r : ℚ) (m : ℕ), M.Admitted a r m → 0 ≤ quadratic a r c := by
  first
  | constructor
    · intro h a r m ha
      have hk := h (Encodable.encode (a, r, m))
      simpa [enumeratedForm, Encodable.encodek, ha, eval_rationalForm] using hk
    · intro h k
      unfold enumeratedForm
      split
      · simp
      · split
        · rw [eval_rationalForm]
          exact h _ _ _ ‹_›
        · simp

/-- A nonzero nonnegative coefficient vector has a strictly positive total. -/
theorem total_pos {c : Space ι} (hn : ∀ i, 0 ≤ c i) (hc : c ≠ 0) : 0 < total c := by
  first
  | have hnonneg : 0 ≤ total c := Finset.sum_nonneg (fun i _ => hn i)
    refine lt_of_le_of_ne hnonneg ?_
    intro heq
    apply hc
    ext i
    have hzero : ∀ i, c i = 0 := by
      first
      | simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp heq.symm
    exact hzero i

/--
The full abstract homogenized characterization.

The four hypotheses explicitly connect the target set to the intended coefficient
locus; none is silently treated as an axiom about convex geometry.
-/
theorem coefficient_characterization (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) :
    c ∈ V ↔ (∀ i, 0 ≤ c i) ∧
      ∀ (a : ι → ℚ) (r : ℚ) (m : ℕ), M.Admitted a r m → 0 ≤ quadratic a r c := by
  first
  | constructor
    · intro hc
      refine ⟨hnonneg c hc, ?_⟩
      intro a r m ha
      by_cases hz : c = 0
      · simp [hz]
      have hs := total_pos (hnonneg c hc) hz
      rw [quadratic_eq_normalized _ _ _ hs.ne']
      apply mul_nonneg (sq_nonneg _)
      exact sub_nonneg.mpr ((M.mem_iff_admitted_balls _).mp (hnormalize c hc hz) a r m ha)
    · rintro ⟨hn, hq⟩
      by_cases hz : c = 0
      · simpa [hz] using hzero
      have hs := total_pos hn hz
      apply hrealize c hs
      apply (M.mem_iff_admitted_balls _).mpr
      intro a r m ha
      have hquad := hq a r m ha
      rw [quadratic_eq_normalized _ _ _ hs.ne'] at hquad
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (sq_pos_of_pos hs)).mp hquad)

/-- Countably indexed rational homogeneous quadratic forms give the same exact criterion. -/
theorem countable_coefficient_characterization [Encodable ι]
    (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) :
    c ∈ V ↔ (∀ i, 0 ≤ c i) ∧
      ∀ k, 0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k) := by
  first
  | rw [forall_enumerated_iff]
    exact coefficient_characterization M V hzero hnonneg hnormalize hrealize c

/-- Every vector outside the intended locus has one strictly violated finite certificate. -/
theorem exists_strict_certificate [Encodable ι]
    (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) (hc : c ∉ V) :
    (∃ i, c i < 0) ∨ ∃ k,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k) < 0 := by
  first
  | have h := (countable_coefficient_characterization M V hzero hnonneg hnormalize hrealize c).not.mp hc
    push_neg at h
    by_cases hn : ∀ i, 0 ≤ c i
    · exact Or.inr (h hn)
    · exact Or.inl (by simpa only [not_forall, not_le] using hn)

end VolumePolynomials.QuadraticSeparation
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/QuadraticSeparation.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalCoefficientNets.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Certified computable finite nets of actual volume-polynomial coefficients

The finite list of rational hull tuples is evaluated by the terminating
rational box-volume algorithm. Exact interpolation gives rational coefficient
centers. The explicit Hausdorff coefficient modulus supplies the uniform
covering bound, while every center is close to an actual bounded realization.
This constructs the geometric/computational Model required by Section 8.
-/

open Set Filter Metric
open scoped BigOperators Topology

namespace VolumePolynomials.RationalCoefficientNets

open RationalHulls

def samplingTolerance (k : ℕ) : ℚ := 1 / ((k : ℚ) + 1)

theorem samplingTolerance_pos (k : ℕ) : 0 < samplingTolerance k := by
  first
  | unfold samplingTolerance
    positivity

def gridMultiplier (n d : ℕ) : ℕ := ⌈interpolationWeightBound n d⌉₊ + 1

def resolution (n d k : ℕ) : ℕ := gridMultiplier n d * (k + 1)

theorem gridMultiplier_pos (n d : ℕ) : 0 < gridMultiplier n d := by
  first
  | unfold gridMultiplier
    omega

theorem weightBound_le_gridMultiplier (n d : ℕ) :
    interpolationWeightBound n d ≤ (gridMultiplier n d : ℚ) := by
  first
  | exact (Nat.le_ceil _).trans (by simp [gridMultiplier])

theorem resolution_bounds (n d k : ℕ) :
    1 / ((resolution n d k : ℝ) + 1) ≤ (samplingTolerance k : ℝ) ∧
      (1 / ((resolution n d k : ℝ) + 1)) * (interpolationWeightBound n d : ℝ) ≤ 1 := by
  first
  | have hA : (1 : ℝ) ≤ gridMultiplier n d := by exact_mod_cast gridMultiplier_pos n d
    have hT : (interpolationWeightBound n d : ℝ) ≤ gridMultiplier n d := by
      exact_mod_cast weightBound_le_gridMultiplier n d
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
    have hres : (resolution n d k : ℝ) + 1 =
        (gridMultiplier n d : ℝ) * ((k : ℝ) + 1) + 1 := by simp [resolution]
    have hd : 0 < (resolution n d k : ℝ) + 1 := by positivity
    constructor
    · simp only [samplingTolerance, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast]
      apply one_div_le_one_div_of_le (by positivity)
      rw [hres]
      nlinarith
    · rw [one_div, inv_mul_eq_div, div_le_one hd]
      rw [hres]
      nlinarith

def coordinateBudget (n d R : ℕ) : ℚ :=
  coefficientExtractionBound n d + coefficientModulus n d (R : ℚ) + 1

theorem coefficientModulus_nonneg (n d R : ℕ) : 0 ≤ coefficientModulus n d (R : ℚ) := by
  first
  | have hT : 0 ≤ interpolationWeightBound n d := (interpolationWeightBound_pos n d).le
    unfold coefficientModulus
    exact mul_nonneg (mul_nonneg (coefficientExtractionBound_nonneg n d)
      (interpolationWeightBound_pos n d).le) (by positivity)

theorem coordinateBudget_pos (n d R : ℕ) : 0 < coordinateBudget n d R := by
  first
  | have hE := coefficientExtractionBound_nonneg n d
    have hC := coefficientModulus_nonneg n d R
    unfold coordinateBudget
    linarith

def netError (n d R k : ℕ) : ℚ :=
  (Fintype.card (MultiIndex n d) + 1) * coordinateBudget n d R * samplingTolerance k

def coefficientNet (n d R k : ℕ) : Finset (MultiIndex n d → ℚ) :=
  ((candidateTuples n d R (resolution n d k)).map
    (fun L => approximateCoefficients L (samplingTolerance k) (samplingTolerance_pos k))).toFinset

def boundedTarget (n d R : ℕ) : Set (QuadraticSeparation.Space (MultiIndex n d)) :=
  WithLp.toLp 2 '' boundedVolumeLocus n d
    (Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))

theorem isCompact_boundedTarget (n d R : ℕ) : IsCompact (boundedTarget n d R) := by
  first
  | apply (isCompact_boundedVolumeLocus n d isCompact_Icc).image
    exact PiLp.continuous_toLp 2 _

theorem norm_le_sum_abs {ι : Type*} [Fintype ι] (x : QuadraticSeparation.Space ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  first
  | apply (sq_le_sq₀ (norm_nonneg x) (Finset.sum_nonneg fun i _ => abs_nonneg (x i))).mp
    rw [QuadraticSeparation.real_norm_sq_eq]
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |x i|)
        (fun i _ => abs_nonneg (x i)))

theorem dist_le_card_mul {ι : Type*} [Fintype ι] (x y : QuadraticSeparation.Space ι)
    {δ : ℝ} (h : ∀ i, |x i - y i| ≤ δ) : dist x y ≤ Fintype.card ι * δ := by
  first
  | rw [dist_eq_norm]
    apply (norm_le_sum_abs (x - y)).trans
    calc
      _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum (fun i _ => h i)
      _ = Fintype.card ι * δ := by simp

theorem budget_to_netError {n d R k : ℕ}
    {x y : QuadraticSeparation.Space (MultiIndex n d)}
    (h : ∀ α, |x α - y α| ≤ (coordinateBudget n d R : ℝ) * (samplingTolerance k : ℝ)) :
    dist x y ≤ (netError n d R k : ℝ) := by
  first
  | apply (dist_le_card_mul x y h).trans
    simp only [netError, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
    have hB : 0 ≤ (coordinateBudget n d R : ℝ) := by
      exact_mod_cast (coordinateBudget_pos n d R).le
    have he : 0 ≤ (samplingTolerance k : ℝ) := by exact_mod_cast (samplingTolerance_pos k).le
    nlinarith

theorem coefficientNet_near (n d R k : ℕ) (q : MultiIndex n d → ℚ)
    (hq : q ∈ coefficientNet n d R k) :
    ∃ c ∈ boundedTarget n d R,
      dist (QuadraticSeparation.ofRat q) c ≤ (netError n d R k : ℝ) := by
  first
  | obtain ⟨L, hL, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have hLi := (mem_candidateTuples L).mp hL
    have hL0 : ∀ i, 0 ∈ L i := fun i => ((mem_candidates (L i)).mp (hLi i)).2
    let K : Fin n → Body d := fun i => body (L i) (hL0 i)
    obtain ⟨c, hc⟩ := exists_volume_polynomial K
    refine ⟨WithLp.toLp 2 c, ⟨c, ⟨K, ?_, hc⟩, rfl⟩, ?_⟩
    · intro i
      exact ⟨zero_mem_body (L i) (hL0 i), candidate_bounded (L i) (hLi i)⟩
    · apply budget_to_netError
      intro α
      have ha := approximateCoefficients_correct L hL0 hc (samplingTolerance k)
        (samplingTolerance_pos k) α
      apply ha.trans
      apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast (samplingTolerance_pos k).le)
      have hC : 0 ≤ (coefficientModulus n d (R : ℚ) : ℝ) := by
        exact_mod_cast coefficientModulus_nonneg n d R
      simp only [coordinateBudget, Rat.cast_add, Rat.cast_one]
      linarith

theorem coefficientNet_covers (n d R k : ℕ)
    (c : QuadraticSeparation.Space (MultiIndex n d)) (hc : c ∈ boundedTarget n d R) :
    ∃ q ∈ coefficientNet n d R k, dist c (QuadraticSeparation.ofRat q) ≤ (netError n d R k : ℝ) := by
  first
  | classical
    obtain ⟨c', ⟨K, hK, hc'⟩, rfl⟩ := hc
    choose L hL hdist using fun i => exists_candidate_near (R := R)
      (k := resolution n d k) (K i) (hK i).1 (hK i).2
    have hL0 : ∀ i, 0 ∈ L i := fun i => ((mem_candidates (L i)).mp (hL i)).2
    let P : Fin n → Body d := fun i => body (L i) (hL0 i)
    obtain ⟨cP, hcP⟩ := exists_volume_polynomial P
    let q := approximateCoefficients L (samplingTolerance k) (samplingTolerance_pos k)
    refine ⟨q, List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨L, (mem_candidateTuples L).mpr hL, rfl⟩), ?_⟩
    apply budget_to_netError
    intro α
    have hgeom := hc'.coefficient_sub_le_of_dist_le hcP (R : ℚ) (by positivity)
      (fun i => (hK i).2) (fun i => candidate_bounded (L i) (hL i))
      (by positivity : 0 ≤ 1 / ((resolution n d k : ℝ) + 1))
      (resolution_bounds n d k).2 hdist α
    have happ := approximateCoefficients_correct L hL0 hcP (samplingTolerance k)
      (samplingTolerance_pos k) α
    have hC : 0 ≤ (coefficientModulus n d (R : ℚ) : ℝ) := by
      exact_mod_cast coefficientModulus_nonneg n d R
    have hgeom' : |c' α - cP α| ≤
        (samplingTolerance k : ℝ) * (coefficientModulus n d (R : ℚ) : ℝ) :=
      hgeom.trans (mul_le_mul_of_nonneg_right (resolution_bounds n d k).1 hC)
    have htri := abs_sub_le (c' α) (cP α) (q α : ℝ)
    rw [abs_sub_comm (cP α) (q α : ℝ)] at htri
    change |c' α - (q α : ℝ)| ≤ _
    have he : 0 ≤ (samplingTolerance k : ℝ) := by exact_mod_cast (samplingTolerance_pos k).le
    simp only [coordinateBudget, Rat.cast_add, Rat.cast_one]
    dsimp [q] at htri ⊢
    nlinarith

/-- The complete finite-net input, with its rational data executable and its
geometric meaning proved for actual compact convex bodies. -/
def model (n d R : ℕ) : QuadraticSeparation.Model (MultiIndex n d) where
  target := boundedTarget n d R
  closed := (isCompact_boundedTarget n d R).isClosed
  net := coefficientNet n d R
  error := netError n d R
  error_nonneg := by
    first
    | intro k
      exact mul_nonneg (mul_nonneg (by positivity) (coordinateBudget_pos n d R).le)
        (samplingTolerance_pos k).le
  error_tendsto := by
    first
    | have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (((Fintype.card (MultiIndex n d) : ℝ) + 1) * (coordinateBudget n d R : ℝ))
      simpa only [netError, samplingTolerance, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_one, mul_zero] using h
  net_near := coefficientNet_near n d R
  covers := coefficientNet_covers n d R

end VolumePolynomials.RationalCoefficientNets
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/RationalCoefficientNets.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodyNormalization.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# Uniform normalization of actual realizing tuples

This is a geometric compactness normalization. Its radius depends only on the
ambient dimension. It is deliberately distinct from the explicit numerical
radius needed by the paper's computable grid construction.
-/

noncomputable section
open Set MeasureTheory Finset Metric
open scoped Pointwise BigOperators

namespace VolumePolynomials

theorem affine_image_eq_translate_linear_image {d : ℕ}
    (T : Space d ≃ᵃ[ℝ] Space d) (K : Body d) :
    T '' (K : Set (Space d)) =
      (translateBody (T 0) (mapBody T.linear.toContinuousLinearEquiv.toContinuousLinearMap K) :
        Set (Space d)) := by
  first
  | ext y
    simp only [coe_translateBody, coe_mapBody, Set.mem_vadd_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨T.linear x, ⟨x, hx, rfl⟩, ?_⟩
      simpa only [vadd_eq_add, add_zero, add_comm] using (T.map_vadd 0 x).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      change T x = T 0 + T.linear x
      simpa only [vadd_eq_add, add_zero, add_comm] using T.map_vadd 0 x

theorem bodyVolume_affine_image {d : ℕ} (T : Space d ≃ᵃ[ℝ] Space d) (K : Body d) :
    volume.real (T '' (K : Set (Space d))) =
      |LinearMap.det T.linear.toLinearMap| * bodyVolume K := by
  first
  | rw [affine_image_eq_translate_linear_image]
    change bodyVolume (translateBody _ (mapBody _ K)) = _
    rw [bodyVolume_translate, bodyVolume_map]
    rfl

/-- Every total-volume-one realization admits independently translated bodies
and a common linear volume normalization inside a fixed ball. No coefficient
positivity or polynomial-existence assertion is used as an assumption. -/
theorem exists_uniform_normalization (d : ℕ) (hd : 0 < d) :
    ∃ R > 0, ∀ (n : ℕ) (K : Fin n → Body d) (c : Coefficients n d),
      Realizes K c → (∑ α, c α) = 1 →
      ∃ L : Fin n → Body d, Realizes L c ∧
        ∀ i, (0 : Space d) ∈ L i ∧ (L i : Set (Space d)) ⊆ closedBall 0 R := by
  first
  | classical
    obtain ⟨r, hr, hnormal⟩ :=
      TauCeti.exists_affineEquiv_ball_subset_image_subset_ball (Space d)
    let m : ℝ := volume.real (ball (0 : Space d) r)
    have hm : 0 < m := ENNReal.toReal_pos (measure_ball_pos volume 0 hr).ne' measure_ball_ne_top
    let q : ℝ := m ^ (-((d : ℝ)⁻¹))
    have hq : 0 < q := Real.rpow_pos_of_pos hm _
    refine ⟨2 * q, mul_pos zero_lt_two hq, ?_⟩
    intro n K c hK hc
    let S : Body d := ∑ i, K i
    have hSvol : bodyVolume S = 1 := hK.sum_coefficients.symm.trans hc
    have hSpos : 0 < volume (S : Set (Space d)) := by
      first
      | have ht : 0 < (volume (S : Set (Space d))).toReal := by
          change 0 < bodyVolume S
          rw [hSvol]
          exact zero_lt_one
        exact (ENNReal.toReal_pos_iff.mp ht).1
    obtain ⟨T, hsmall, hlarge⟩ := hnormal (S : Set (Space d)) S.convex S.isBounded
      ((S.convex.addHaar_pos_iff_interior_nonempty (μ := volume)).mp hSpos)
    let f : Space d →L[ℝ] Space d := T.linear.toContinuousLinearEquiv.toContinuousLinearMap
    let D : ℝ := |LinearMap.det f.toLinearMap|
    have hTD : volume.real (T '' (S : Set (Space d))) = D := by
      first
      | rw [bodyVolume_affine_image, hSvol, mul_one]
        rfl
    have hmD : m ≤ D := by
      first
      | rw [← hTD]
        exact measureReal_mono hsmall (by
          rw [affine_image_eq_translate_linear_image]
          exact (translateBody (T 0) (mapBody f S)).isCompact.measure_lt_top.ne)
    have hD : 0 < D := hm.trans_le hmD
    let a : ℝ := D ^ (-((d : ℝ)⁻¹))
    have ha : 0 < a := Real.rpow_pos_of_pos hD _
    have haq : a ≤ q := Real.rpow_le_rpow_of_nonpos hm hmD
      (neg_nonpos.mpr (inv_nonneg.mpr (Nat.cast_nonneg d)))
    have hapow : a ^ d = D⁻¹ := by
      first
      | dsimp [a]
        rw [Real.rpow_neg hD.le, inv_pow, Real.rpow_inv_natCast_pow hD.le hd.ne']
    choose p hp using fun i => (K i).nonempty
    let P : Fin n → Body d := fun i => translateBody (-p i) (K i)
    have hP0 : ∀ i, (0 : Space d) ∈ P i := by
      first
      | intro i
        simpa [P, mem_translateBody] using hp i
    have hpsum : (∑ i, p i) ∈ S := by
      first
      | exact (mem_sum_body K _).mpr ⟨p, hp, rfl⟩
    have hPsum : ∑ i, P i = translateBody (-(∑ i, p i)) S := by
      first
      | simpa only [weightedSum_one, one_smul, Finset.sum_neg_distrib, P, S] using
          weightedSum_translate K (fun i => -p i) (fun _ => 1)
    have hfnorm : ∀ u ∈ (∑ i, P i : Body d), ‖f u‖ < 2 := by
      first
      | intro u hu
        rw [hPsum, mem_translateBody, sub_neg_eq_add] at hu
        have h₁ := hlarge (Set.mem_image_of_mem T hu)
        have h₂ := hlarge (Set.mem_image_of_mem T hpsum)
        rw [mem_ball_zero_iff] at h₁ h₂
        have hfu : f u = T (u + ∑ i, p i) - T (∑ i, p i) := by
          apply eq_sub_iff_add_eq.mpr
          change T.linear u + T (∑ i, p i) = T (u + ∑ i, p i)
          simpa only [vadd_eq_add] using (T.map_vadd (∑ i, p i) u).symm
        rw [hfu]
        exact (norm_sub_le _ _).trans_lt (by linarith)
    let L : Fin n → Body d := fun i => a • mapBody f (P i)
    have hreal : Realizes L c := by
      first
      | have h := ((hK.translate (fun i => -p i)).map f).dilate ha.le
        have hscale : a ^ d • (D • c) = c := by
          rw [smul_smul, hapow, inv_mul_cancel₀ hD.ne', one_smul]
        change Realizes L (a ^ d • (D • c)) at h
        rwa [hscale] at h
    refine ⟨L, hreal, fun i => ⟨?_, ?_⟩⟩
    · change (0 : Space d) ∈ a • (mapBody f (P i) : Set (Space d))
      exact ⟨0, ⟨0, hP0 i, map_zero f⟩, smul_zero _⟩
    · rintro y ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ha.le]
      have huS := body_le_sum_of_zero_mem P hP0 i hu
      have hbound := hfnorm u huS
      calc
        a * ‖f u‖ ≤ a * 2 := mul_le_mul_of_nonneg_left hbound.le ha.le
        _ ≤ q * 2 := mul_le_mul_of_nonneg_right haq zero_le_two
        _ = 2 * q := mul_comm _ _

end VolumePolynomials
end -- original EOF section
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/BodyNormalization.lean -/

/- BEGIN SOURCE: VolumePolynomials/ExplicitNormalization.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# The explicit normalization box

The maximal-simplex coordinates bound the image by the unit cube. The coordinate
simplex contains the cube of side `1/d`; its elementary product volume suffices
to obtain the paper's final radius `d`, without needing a simplex-volume formula.
-/

noncomputable section
open Set MeasureTheory Finset Metric
open scoped Pointwise BigOperators ENNReal

namespace VolumePolynomials

def droppedCoordinateMap {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) :
    Space d →ᵃ[ℝ] Space d := AffineMap.pi (fun i => b.coord i.succ)

@[simp] theorem droppedCoordinateMap_apply {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) (x : Space d) (i : Fin d) :
    droppedCoordinateMap b x i = b.coord i.succ x := rfl

theorem droppedCoordinateMap_bijective {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) :
    Function.Bijective (droppedCoordinateMap b) := by
  first
  | constructor
    · intro x y hxy
      apply b.ext_elem
      intro i
      cases i using Fin.cases with
      | zero =>
          have hx := b.sum_coord_apply_eq_one x
          have hy := b.sum_coord_apply_eq_one y
          rw [Fin.sum_univ_succ] at hx hy
          have hh : (∑ j : Fin d, b.coord j.succ x) = ∑ j : Fin d, b.coord j.succ y := by
            first
            | apply Finset.sum_congr rfl
              intro j _
              exact congrFun hxy j
          linarith
      | succ j => exact congrFun hxy j
    · intro y
      let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, y i) y
      have hw : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_succ]
      refine ⟨Finset.univ.affineCombination ℝ b w, ?_⟩
      funext i
      exact (b.coord_apply_combination_of_mem (Finset.mem_univ i.succ) hw).trans
        (by simp [w])

def droppedCoordinateEquiv {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) :
    Space d ≃ᵃ[ℝ] Space d := AffineEquiv.ofBijective (droppedCoordinateMap_bijective b)

@[simp] theorem droppedCoordinateEquiv_apply {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) (x : Space d) (i : Fin d) :
    droppedCoordinateEquiv b x i = b.coord i.succ x := rfl

@[simp] theorem droppedCoordinateEquiv_zero_vertex {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) : droppedCoordinateEquiv b (b 0) = 0 := by
  first
  | funext i
    simp [b.coord_apply_ne i.succ_ne_zero]

theorem smallCube_subset_coordinate_image {d : ℕ} (hd : 0 < d) (K : Body d)
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) (hb : ∀ i, b i ∈ K) :
    Icc (0 : Space d) (fun _ => (d : ℝ)⁻¹) ⊆ droppedCoordinateEquiv b '' (K : Set (Space d)) := by
  first
  | classical
    intro y hy
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hsum : ∑ i, y i ≤ 1 := by
      first
      | calc
          ∑ i, y i ≤ ∑ _i : Fin d, (d : ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => hy.2 i)
          _ = 1 := by simp [hdpos.ne']
    let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, y i) y
    have hw : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_succ]
    have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))), 0 ≤ w i := by
      first
      | intro i _
        cases i using Fin.cases with
        | zero => exact sub_nonneg.mpr hsum
        | succ i => exact hy.1 i
    let x := Finset.univ.affineCombination ℝ b w
    have hx : x ∈ K := (convexHull_min (Set.range_subset_iff.mpr hb) K.convex)
      (affineCombination_mem_convexHull hw0 hw)
    refine ⟨x, hx, ?_⟩
    funext i
    exact (b.coord_apply_combination_of_mem (Finset.mem_univ i.succ) hw).trans
      (by simp [w])

/-- Lemma 2.3's actual affine normalization, including its common determinant-one
linear map and the bound on the whole Minkowski sum. -/
theorem explicit_normalization {n d : ℕ} (hd : 0 < d) (K : Fin n → Body d)
    (hvol : bodyVolume (∑ i, K i) = 1) :
    ∃ (g : Space d →L[ℝ] Space d) (p : Fin n → Space d),
      |LinearMap.det g.toLinearMap| = 1 ∧ (∀ i, p i ∈ K i) ∧
      let L : Fin n → Body d := fun i => mapBody g (translateBody (-p i) (K i))
      (∀ i, (0 : Space d) ∈ L i) ∧
        ((∑ i, L i : Body d) : Set (Space d)) ⊆
          Icc (fun _ => -(d : ℝ)) (fun _ => (d : ℝ)) := by
  first
  | classical
    let S : Body d := ∑ i, K i
    have hSpos : 0 < volume (S : Set (Space d)) := by
      first
      | have ht : 0 < (volume (S : Set (Space d))).toReal := by
          first
          | change 0 < bodyVolume S
            rw [show bodyVolume S = 1 from hvol]
            exact zero_lt_one
        exact (ENNReal.toReal_pos_iff.mp ht).1
    have hspan : affineSpan ℝ (S : Set (Space d)) = ⊤ :=
      (S.convex.addHaar_pos_iff_affineSpan_eq_top (μ := volume)).mp hSpos
    obtain ⟨b, hb, hcoord⟩ := S.isCompact.exists_affineBasis_abs_coord_le_one
      (ι := Fin (d + 1)) hspan (by simp [Space])
    let T : Space d ≃ᵃ[ℝ] Space d := droppedCoordinateEquiv b
    let f : Space d →L[ℝ] Space d := T.linear.toContinuousLinearEquiv.toContinuousLinearMap
    let D : ℝ := |LinearMap.det f.toLinearMap|
    have hTD : volume.real (T '' (S : Set (Space d))) = D := by
      first
      | rw [bodyVolume_affine_image, show bodyVolume S = 1 from hvol, mul_one]
        rfl
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hlow : ((d : ℝ)⁻¹) ^ d ≤ D := by
      first
      | rw [← hTD]
        have h := measureReal_mono (smallCube_subset_coordinate_image hd S b hb)
          (show volume (T '' (S : Set (Space d))) ≠ ∞ from by
            rw [affine_image_eq_translate_linear_image]
            exact (translateBody (T 0) (mapBody f S)).isCompact.measure_lt_top.ne)
        have hcube : volume.real (Icc (0 : Space d) (fun _ => (d : ℝ)⁻¹)) =
            ((d : ℝ)⁻¹) ^ d := by
          first
          | rw [measureReal_def, Real.volume_Icc_pi_toReal
              (show (0 : Space d) ≤ (fun _ => (d : ℝ)⁻¹) from
                fun _ => inv_nonneg.mpr hdpos.le)]
            simp
        rwa [hcube] at h
    have hD : 0 < D := (pow_pos (inv_pos.mpr hdpos) d).trans_le hlow
    let a : ℝ := D ^ (-((d : ℝ)⁻¹))
    have ha : 0 < a := Real.rpow_pos_of_pos hD _
    have hapow : a ^ d = D⁻¹ := by
      first
      | dsimp [a]
        rw [Real.rpow_neg hD.le, inv_pow, Real.rpow_inv_natCast_pow hD.le hd.ne']
    have had : a ≤ d := by
      first
      | apply (pow_le_pow_iff_left₀ ha.le hdpos.le hd.ne').mp
        rw [hapow]
        have hinv := (inv_le_inv₀ hD (pow_pos (inv_pos.mpr hdpos) d)).mpr hlow
        simpa only [inv_pow, inv_inv] using hinv
    let g : Space d →L[ℝ] Space d := a • f
    have hg : |LinearMap.det g.toLinearMap| = 1 := by
      first
      | change |LinearMap.det (a • f.toLinearMap)| = 1
        rw [LinearMap.det_smul, abs_mul, abs_pow, abs_of_pos ha]
        have hdim : Module.finrank ℝ (Space d) = d := by simp [Space]
        rw [hdim]
        change a ^ d * D = 1
        rw [hapow, inv_mul_cancel₀ hD.ne']
    obtain ⟨p, hp, hpsum⟩ := (mem_sum_body K (b 0)).mp (hb 0)
    let P : Fin n → Body d := fun i => translateBody (-p i) (K i)
    have hP0 : ∀ i, (0 : Space d) ∈ P i := by
      first
      | intro i
        simpa [P, mem_translateBody] using hp i
    have hPsum : ∑ i, P i = translateBody (-(b 0)) S := by
      first
      | simpa only [weightedSum_one, one_smul, Finset.sum_neg_distrib, hpsum, P, S] using
          weightedSum_translate K (fun i => -p i) (fun _ => 1)
    refine ⟨g, p, hg, hp, ?_⟩
    constructor
    · intro i
      exact ⟨0, hP0 i, map_zero g⟩
    · intro y hy
      have hmapsum : (∑ i, mapBody g (P i)) = mapBody g (∑ i, P i) :=
        (map_sum (mapBodyHom g) P Finset.univ).symm
      change y ∈ ∑ i, mapBody g (P i) at hy
      rw [hmapsum] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hPsum] at hu
      change u ∈ translateBody (-(b 0)) S at hu
      rw [mem_translateBody, sub_neg_eq_add] at hu
      have hfu : f u = T (u + b 0) := by
        first
        | change T.linear u = T (u + b 0)
          have h := T.map_vadd (b 0) u
          simpa only [vadd_eq_add, T, droppedCoordinateEquiv_zero_vertex, add_zero] using h.symm
      have hbound : ∀ j, |g u j| ≤ d := by
        first
        | intro j
          have hc : |f u j| ≤ 1 := by
            first
            | rw [hfu]
              exact hcoord (u + b 0) hu j.succ
          change |a * f u j| ≤ d
          rw [abs_mul, abs_of_pos ha]
          exact (mul_le_of_le_one_right ha.le hc).trans had
      exact ⟨fun j => (abs_le.mp (hbound j)).1, fun j => (abs_le.mp (hbound j)).2⟩

end VolumePolynomials
end -- original EOF section
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/ExplicitNormalization.lean -/

/- BEGIN SOURCE: VolumePolynomials/EnumeratedQuadraticMatrices.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# Executable coefficients of the enumerated quadratic forms

The enumerator returns a rational matrix, using only rational arithmetic and
the finite rational admission test. Its specification is proved equal to the
semantic polynomial enumerator. Thus no polynomial implementation is needed
to compute the actual coefficients of the certificates.
-/

open scoped BigOperators

namespace VolumePolynomials.QuadraticSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Encodable ι]

def enumeratedRationalMatrix (M : Model ι) (k : ℕ) : ι → ι → ℚ :=
  match enumeratedCertificate M k with
  | none => fun _ _ => 0
  | some (a, r, _) => rationalMatrix a r

/-- Exact agreement of the executable rational coefficients and the
homogeneous polynomial used in the mathematical characterization. -/
theorem enumeratedRationalMatrix_eval (M : Model ι) (k : ℕ) (c : Space ι) :
    (∑ i, ∑ j, (enumeratedRationalMatrix M k i j : ℝ) * c i * c j) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k) := by
  first
  | cases hd : Encodable.decode (α := CertificateIndex ι) k with
    | none => simp [enumeratedRationalMatrix, enumeratedCertificate, enumeratedForm, hd]
    | some z =>
        obtain ⟨a, r, m⟩ := z
        by_cases ha : M.Admitted a r m
        · simp only [enumeratedRationalMatrix, enumeratedCertificate, enumeratedForm,
            hd, if_pos ha, eval_rationalForm]
          exact (quadratic_eq_matrix a r c).symm
        · simp [enumeratedRationalMatrix, enumeratedCertificate, enumeratedForm, hd, ha]

theorem enumeratedRationalMatrix_encode (M : Model ι)
    (a : ι → ℚ) (r : ℚ) (m : ℕ) (h : M.Admitted a r m) :
    enumeratedRationalMatrix M (Encodable.encode (a, r, m)) = rationalMatrix a r := by
  first
  | rw [enumeratedRationalMatrix, enumeratedCertificate_encode M a r m h]

/-- The complete abstract criterion with a literally executable rational
matrix at every natural-number index. Geometry must supply the model and the
four stated identifications before this is applied to a volume locus. -/
theorem countable_matrix_characterization
    (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) :
    c ∈ V ↔ (∀ i, 0 ≤ c i) ∧ ∀ k : ℕ,
      0 ≤ ∑ i, ∑ j, (enumeratedRationalMatrix M k i j : ℝ) * c i * c j := by
  first
  | simp only [enumeratedRationalMatrix_eval]
    exact countable_coefficient_characterization M V hzero hnonneg hnormalize hrealize c

end VolumePolynomials.QuadraticSeparation
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/EnumeratedQuadraticMatrices.lean -/

/- BEGIN SOURCE: VolumePolynomials/MainQuadraticCharacterization.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# The rational quadratic characterization

This file connects the certified executable finite nets to the literal
volume-polynomial realization locus. The normalization is the proved affine
normalization of actual convex bodies, and nonnegativity comes from the full
volume-polynomial existence theorem. No geometric or computational premise
is added to the final characterization.
-/

open Set
open scoped BigOperators Pointwise

namespace VolumePolynomials

theorem normalized_mem_explicit_boundedLocus {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} (hc : c ∈ VolumeLocus n d) (hs : 0 < ∑ α, c α) :
    (∑ α, c α)⁻¹ • c ∈ boundedVolumeLocus n d
      (Icc (fun _ => -(d : ℝ)) (fun _ => (d : ℝ))) := by
  first
  | have hn := smul_mem_volumeLocus hd hc (inv_nonneg.mpr hs.le)
    obtain ⟨K, hK⟩ := hn
    have hsum : ∑ α, ((∑ β, c β)⁻¹ • c) α = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀ hs.ne']
    have hvol : bodyVolume (∑ i, K i) = 1 := hK.sum_coefficients.symm.trans hsum
    obtain ⟨g, p, hg, hp, h0, hbox⟩ := explicit_normalization hd K hvol
    let L : Fin n → Body d := fun i => mapBody g (translateBody (-p i) (K i))
    have hL : Realizes L ((∑ α, c α)⁻¹ • c) :=
      (hK.translate (fun i => -p i)).map_of_abs_det_one g hg
    refine ⟨L, ?_, hL⟩
    intro i
    exact ⟨h0 i, fun x hx => hbox (body_le_sum_of_zero_mem L h0 i hx)⟩

namespace Main

open QuadraticSeparation

/-- At every natural-number index this returns the actual rational
coefficients of a homogeneous quadratic form. -/
def volumeInequalityMatrix (n d k : ℕ) : MultiIndex n d → MultiIndex n d → ℚ :=
  enumeratedRationalMatrix (RationalCoefficientNets.model n d d) k

/-- The equivalent semantic multivariate polynomial. Its matrix coefficients
are given by the executable definition above. -/
noncomputable def volumeInequalityPolynomial (n d k : ℕ) : MvPolynomial (MultiIndex n d) ℚ :=
  enumeratedForm (RationalCoefficientNets.model n d d) k

theorem volumeInequalityPolynomial_homogeneous (n d k : ℕ) :
    (volumeInequalityPolynomial n d k).IsHomogeneous 2 :=
  enumeratedForm_isHomogeneous _ _

theorem volumeInequalityMatrix_eval (n d k : ℕ) (c : Coefficients n d) :
    (∑ α, ∑ β, (volumeInequalityMatrix n d k α β : ℝ) * c α * c β) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) :=
  enumeratedRationalMatrix_eval _ _ (WithLp.toLp 2 c)

/-- Theorem 1.3, in executable rational-matrix form, for every number of
bodies and every positive ambient dimension. Every coefficient, every real
nonnegative Minkowski weight, and every realization is retained. -/
theorem volumeLocus_iff_countableQuadratics (n d : ℕ) (hd : 0 < d)
    (c : Coefficients n d) :
    c ∈ VolumeLocus n d ↔
      (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
        0 ≤ ∑ α, ∑ β, (volumeInequalityMatrix n d k α β : ℝ) * c α * c β := by
  first
  | let V : Set (QuadraticSeparation.Space (MultiIndex n d)) :=
      {x | WithLp.ofLp x ∈ VolumeLocus n d}
    have hzero : (0 : QuadraticSeparation.Space (MultiIndex n d)) ∈ V :=
      zero_mem_volumeLocus hd
    have hnonneg : ∀ x ∈ V, ∀ α, 0 ≤ x α := by
      intro x hx α
      obtain ⟨K, hK⟩ := hx
      exact hK.coefficients_nonnegative α
    have hnormalize : ∀ x ∈ V, x ≠ 0 →
        normalize x ∈ (RationalCoefficientNets.model n d d).target := by
      intro x hx hx0
      have hs : 0 < total x := total_pos (hnonneg x hx) hx0
      have h := normalized_mem_explicit_boundedLocus hd hx hs
      exact ⟨(total x)⁻¹ • WithLp.ofLp x, h, rfl⟩
    have hrealize : ∀ x, 0 < total x →
        normalize x ∈ (RationalCoefficientNets.model n d d).target → x ∈ V := by
      intro x hs hx
      obtain ⟨y, hy, hyeq⟩ := hx
      have hnorm : WithLp.ofLp (normalize x) ∈ VolumeLocus n d := by
        rw [← hyeq]
        exact boundedVolumeLocus_subset n d _ hy
      have h := smul_mem_volumeLocus hd hnorm hs.le
      change (total x) • ((total x)⁻¹ • WithLp.ofLp x) ∈ VolumeLocus n d at h
      change WithLp.ofLp x ∈ VolumeLocus n d
      simpa only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] using h
    exact countable_matrix_characterization (RationalCoefficientNets.model n d d)
      V hzero hnonneg hnormalize hrealize (WithLp.toLp 2 c)

/-- The original polynomial formulation of the same exact characterization. -/
theorem volumeLocus_iff_enumeratedPolynomials (n d : ℕ) (hd : 0 < d)
    (c : Coefficients n d) :
    c ∈ VolumeLocus n d ↔
      (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
        0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) := by
  first
  | rw [volumeLocus_iff_countableQuadratics n d hd]
    simp only [volumeInequalityMatrix_eval]

/-- The complete countable homogeneous rational quadratic family in Theorem 1.3.
Its actual rational coefficients are computed by `volumeInequalityMatrix`. -/
theorem countable_characterization (n d : ℕ) (hd : 0 < d) :
    (∀ k, (volumeInequalityPolynomial n d k).IsHomogeneous 2) ∧
      ∀ c : Coefficients n d, c ∈ VolumeLocus n d ↔
        (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) :=
  ⟨volumeInequalityPolynomial_homogeneous n d,
    volumeLocus_iff_enumeratedPolynomials n d hd⟩

end Main
end VolumePolynomials
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/MainQuadraticCharacterization.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalRejection.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Finite rational certificates for computable inputs

An input is supplied by rational approximations with a certified error bound.
The finite certificate predicate uses rational arithmetic only. Its soundness
is an interval bound proved for every real vector, and completeness follows
from the strict inequality furnished by the exact volume-locus criterion.
The executable enumeration never tests equality of a real coefficient sum.
-/

open Filter
open scoped BigOperators Topology

namespace VolumePolynomials.RationalCertificates

variable {ι : Type*} [Fintype ι]

def quadraticValue (M : ι → ι → ℚ) (q : ι → ℚ) : ℚ :=
  ∑ i, ∑ j, M i j * q i * q j

def realQuadratic (M : ι → ι → ℚ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j : ℝ) * c i * c j

def quadraticError (M : ι → ι → ℚ) (q : ι → ℚ) (δ : ℚ) : ℚ :=
  ∑ i, ∑ j, |M i j| * δ * (|q i| + |q j| + δ)

theorem product_error {x y a b δ : ℝ} (hδ : 0 ≤ δ)
    (hx : |x - a| ≤ δ) (hy : |y - b| ≤ δ) :
    |x * y - a * b| ≤ δ * (|a| + |b| + δ) := by
  first
  | have hid : x * y - a * b = (x - a) * (y - b) + a * (y - b) + b * (x - a) := by ring
    rw [hid]
    calc
      _ ≤ |(x - a) * (y - b)| + |a * (y - b)| + |b * (x - a)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |x - a| * |y - b| + |a| * |y - b| + |b| * |x - a| := by simp only [abs_mul]
      _ ≤ δ * δ + |a| * δ + |b| * δ := by gcongr
      _ = δ * (|a| + |b| + δ) := by ring

theorem quadratic_interval_bound (M : ι → ι → ℚ) (c : ι → ℝ) (q : ι → ℚ)
    (δ : ℚ) (hδ : 0 ≤ δ) (hq : ∀ i, |c i - (q i : ℝ)| ≤ (δ : ℝ)) :
    |realQuadratic M c - (quadraticValue M q : ℝ)| ≤ (quadraticError M q δ : ℝ) := by
  first
  | simp only [realQuadratic, quadraticValue, quadraticError, Rat.cast_sum, Rat.cast_mul,
      Rat.cast_add, Rat.cast_abs, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [show (M i j : ℝ) * c i * c j - (M i j : ℝ) * (q i : ℝ) * (q j : ℝ) =
      (M i j : ℝ) * (c i * c j - (q i : ℝ) * (q j : ℝ)) by ring, abs_mul]
    have hp := product_error (by exact_mod_cast hδ) (hq i) (hq j)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (abs_nonneg (M i j : ℝ))

def precision (h : ℕ) : ℚ := 1 / ((h : ℚ) + 1)

theorem precision_pos (h : ℕ) : 0 < precision h := by unfold precision; positivity

def IsName (c : ι → ℝ) (a : ℕ → ι → ℚ) : Prop :=
  ∀ h i, |c i - (a h i : ℝ)| ≤ (precision h : ℝ)

theorem precision_tendsto : Tendsto (fun h => (precision h : ℝ)) atTop (𝓝 0) := by
  first
  | simpa only [precision, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem name_tendsto {c : ι → ℝ} {a : ℕ → ι → ℚ} (ha : IsName c a) :
    Tendsto (fun h i => (a h i : ℝ)) atTop (𝓝 c) := by
  first
  | apply tendsto_pi_nhds.mpr
    intro i
    apply (tendsto_iff_dist_tendsto_zero).mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ precision_tendsto
    intro h
    simpa only [Real.dist_eq, abs_sub_comm] using ha h i

theorem quadraticUpper_tendsto (M : ι → ι → ℚ)
    {c : ι → ℝ} {a : ℕ → ι → ℚ} (ha : IsName c a) :
    Tendsto (fun h => ((quadraticValue M (a h) + quadraticError M (a h) (precision h) : ℚ) : ℝ))
      atTop (𝓝 (realQuadratic M c)) := by
  first
  | have hq : Continuous (realQuadratic M) := by unfold realQuadratic; fun_prop
    have he : Continuous (fun z : (ι → ℝ) × ℝ =>
        ∑ i, ∑ j, |(M i j : ℝ)| * z.2 * (|z.1 i| + |z.1 j| + z.2)) := by fun_prop
    have hv := (hq.tendsto c).comp (name_tendsto ha)
    have he' := (he.tendsto (c, 0)).comp ((name_tendsto ha).prodMk_nhds precision_tendsto)
    have h := hv.add he'
    simpa [quadraticValue, quadraticError, realQuadratic] using h

/-- A certificate specifies a negative coordinate or a violated enumerated
quadratic, together with one finite rational input precision. -/
abbrev Certificate (ι : Type*) := (ι × ℕ) ⊕ (ℕ × ℕ)

def Valid (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ) : Certificate ι → Prop
  | .inl (i, h) => a h i + precision h < 0
  | .inr (k, h) => quadraticValue (matrices k) (a h) +
      quadraticError (matrices k) (a h) (precision h) < 0

instance validDecidable (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    (cert : Certificate ι) : Decidable (Valid matrices a cert) := by
  first
  | cases cert <;> unfold Valid <;> infer_instance

theorem valid_sound (matrices : ℕ → ι → ι → ℚ) {c : ι → ℝ} {a : ℕ → ι → ℚ}
    (ha : IsName c a) (cert : Certificate ι) (hcert : Valid matrices a cert) :
    (∃ i, c i < 0) ∨ ∃ k, realQuadratic (matrices k) c < 0 := by
  first
  | cases cert with
    | inl z =>
        obtain ⟨i, h⟩ := z
        apply Or.inl
        refine ⟨i, ?_⟩
        have hq := (abs_le.mp (ha h i)).2
        have hv : (a h i : ℝ) + (precision h : ℝ) < 0 := by exact_mod_cast hcert
        linarith
    | inr z =>
        obtain ⟨k, h⟩ := z
        apply Or.inr
        refine ⟨k, ?_⟩
        have hb := (abs_le.mp (quadratic_interval_bound (matrices k) c (a h) (precision h)
          (precision_pos h).le (ha h))).2
        have hv : (quadraticValue (matrices k) (a h) : ℝ) +
            (quadraticError (matrices k) (a h) (precision h) : ℝ) < 0 := by exact_mod_cast hcert
        linarith

theorem exists_valid_of_strict (matrices : ℕ → ι → ι → ℚ)
    {c : ι → ℝ} {a : ℕ → ι → ℚ} (ha : IsName c a)
    (hbad : (∃ i, c i < 0) ∨ ∃ k, realQuadratic (matrices k) c < 0) :
    ∃ cert, Valid matrices a cert := by
  first
  | rcases hbad with ⟨i, hi⟩ | ⟨k, hk⟩
    · have hlim := ((continuous_apply i).tendsto c |>.comp (name_tendsto ha)).add precision_tendsto
      rw [add_zero] at hlim
      obtain ⟨h, hh⟩ := (hlim.eventually (gt_mem_nhds hi)).exists
      refine ⟨.inl (i, h), ?_⟩
      change a h i + precision h < 0
      change (a h i : ℝ) + (precision h : ℝ) < 0 at hh
      exact_mod_cast hh
    · obtain ⟨h, hh⟩ := ((quadraticUpper_tendsto (matrices k) ha).eventually (gt_mem_nhds hk)).exists
      refine ⟨.inr (k, h), ?_⟩
      change quadraticValue (matrices k) (a h) +
        quadraticError (matrices k) (a h) (precision h) < 0
      exact_mod_cast hh

/-- Exhaustive executable enumeration of all valid finite rational certificates. -/
def enumerate [Encodable ι] (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    (j : ℕ) : Option (Certificate ι) :=
  match Encodable.decode j with
  | none => none
  | some cert => if Valid matrices a cert then some cert else none

theorem enumerate_sound [Encodable ι] (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    {j : ℕ} {cert : Certificate ι} (h : enumerate matrices a j = some cert) :
    Valid matrices a cert := by
  first
  | unfold enumerate at h
    split at h
    · contradiction
    · split at h
      · cases h
        assumption
      · contradiction

theorem enumerate_complete [Encodable ι] (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    {cert : Certificate ι} (h : Valid matrices a cert) :
    enumerate matrices a (Encodable.encode cert) = some cert := by
  first
  | simp [enumerate, Encodable.encodek, h]

end RationalCertificates

namespace Main

/-- Every nonrealizable vector has a strict violated inequality, without
assuming positivity or nonzero total coefficient sum. -/
theorem nonrealizable_strict_inequality (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (hc : c ∉ VolumeLocus n d) :
    (∃ α, c α < 0) ∨ ∃ k, RationalCertificates.realQuadratic (volumeInequalityMatrix n d k) c < 0 := by
  first
  | have h := Iff.mp (not_congr (volumeLocus_iff_countableQuadratics n d hd c)) hc
    by_cases hn : ∀ α, 0 ≤ c α
    · right
      push_neg at h
      exact h hn
    · left
      simpa only [not_forall, not_le] using hn

/-- Rational input names permit a finite rational certificate exactly when
the actual real coefficient vector is nonrealizable. -/
theorem finite_rational_certificate (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (a : ℕ → MultiIndex n d → ℚ) (ha : RationalCertificates.IsName c a) :
    c ∉ VolumeLocus n d ↔
      ∃ cert, RationalCertificates.Valid (volumeInequalityMatrix n d) a cert := by
  first
  | constructor
    · intro hc
      exact RationalCertificates.exists_valid_of_strict _ ha
        (nonrealizable_strict_inequality n d hd c hc)
    · rintro ⟨cert, hcert⟩ hc
      have hgood := Iff.mp (volumeLocus_iff_countableQuadratics n d hd c) hc
      rcases RationalCertificates.valid_sound _ ha cert hcert with ⟨α, hα⟩ | ⟨k, hk⟩
      · exact (not_lt_of_ge (hgood.1 α)) hα
      · exact (not_lt_of_ge (hgood.2 k)) hk

/-- Dovetailing the finite codes rejects every nonrealizable named input at
some finite index and accepts no false certificate. -/
theorem rational_rejection_terminates (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (a : ℕ → MultiIndex n d → ℚ) (ha : RationalCertificates.IsName c a) :
    c ∉ VolumeLocus n d ↔ ∃ j cert,
      RationalCertificates.enumerate (volumeInequalityMatrix n d) a j = some cert := by
  first
  | rw [finite_rational_certificate n d hd c a ha]
    constructor
    · rintro ⟨cert, hc⟩
      exact ⟨Encodable.encode cert, cert, RationalCertificates.enumerate_complete _ _ hc⟩
    · rintro ⟨j, cert, hc⟩
      exact ⟨cert, RationalCertificates.enumerate_sound _ _ hc⟩

end Main
end VolumePolynomials
end -- original EOF section
end -- component scope
/- END SOURCE: VolumePolynomials/RationalRejection.lean -/

end -- former unit scope
/- END FORMER UNIT: MixedVolume.General.RejectionSeparation -/

/- BEGIN FORMER UNIT: MixedVolume.Computability.DecisionPrograms -/
section

/-! Standby source partition. Generation is not a proof certificate.
Exact copied proof ranges are recorded in the adjacent manifest. -/

/- BEGIN SOURCE: MixedVolume/Computability/EffectiveSigns.lean -/
section
/- Decidable coefficient-sign branches with exact primitive-recursive semantics. -/


set_option autoImplicit false

@[expose] public section

namespace MixedVolume.EffectiveSigns
open RationalCode

/-- Sign detection uses integer comparisons on a denominator-positive code. -/
def Nonnegative (c : Code) : Prop := c.2.1 ≤ c.1

instance (c : Code) : Decidable (Nonnegative c) := inferInstanceAs (Decidable (c.2.1 ≤ c.1))

theorem nonnegative_iff (c : Code) : Nonnegative c ↔ 0 ≤ eval c := by
  have hd : 0 < (denominator c : ℚ) := by exact_mod_cast denominator_pos c
  rw [eval,le_div_iff₀ hd,zero_mul,sub_nonneg]
  exact_mod_cast (Iff.rfl : c.2.1 ≤ c.1 ↔ c.2.1 ≤ c.1)

theorem nonnegative_primrec : PrimrecPred Nonnegative :=
  Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) Primrec.fst

def AllNonnegative {n : ℕ} (c : Fin n → Code) : Prop := ∀ i, Nonnegative (c i)

instance {n : ℕ} (c : Fin n → Code) : Decidable (AllNonnegative c) :=
  inferInstanceAs (Decidable (∀ i, Nonnegative (c i)))

theorem allNonnegative_iff {n : ℕ} (c : Fin n → Code) :
    AllNonnegative c ↔ ∀ i, 0 ≤ eval (c i) := by
  simp only [AllNonnegative,nonnegative_iff]

theorem allNonnegative_primrec (n : ℕ) :
    PrimrecPred (AllNonnegative (n := n)) := by
  have hlist : Primrec (fun c : Fin n → Code => List.ofFn c) :=
    Primrec.list_ofFn (fun i => Primrec.fin_app.comp Primrec.id (Primrec.const i))
  have h := (PrimrecPred.forall_mem_list nonnegative_primrec).comp hlist
  exact h.of_eq (fun c => by simp [AllNonnegative])

/-- Replace any array with a negative coefficient by one fixed fallback array. -/
def nonnegativeBranch {n : ℕ} (fallback c : Fin n → Code) : Fin n → Code :=
  if AllNonnegative c then c else fallback

theorem branch_primrec {α : Type*} [Primcodable α] {n : ℕ}
    (fallback : Fin n → Code) {f : α → Fin n → Code} (hf : Primrec f) :
    Primrec (fun x => nonnegativeBranch fallback (f x)) :=
  Primrec.ite ((allNonnegative_primrec n).comp hf) hf (Primrec.const fallback)

def decode {n : ℕ} (c : Fin n → Code) : Fin n → ℚ := fun i => eval (c i)

theorem branch_nonnegative {n : ℕ} (fallback c : Fin n → Code)
    (hfall : ∀ i, 0 ≤ eval (fallback i)) :
    ∀ i, 0 ≤ decode (nonnegativeBranch fallback c) i := by
  by_cases h : AllNonnegative c
  · simpa only [nonnegativeBranch,if_pos h,decode] using (allNonnegative_iff c).1 h
  · simpa only [nonnegativeBranch,if_neg h,decode] using hfall

/-- Exact semantic preservation for a locus whose realizable arrays have
nonnegative coefficients. The fallback must actually be outside that locus. -/
theorem branch_preserves {n : ℕ} (R : (Fin n → ℚ) → Prop)
    (hR : ∀ a, R a → ∀ i, 0 ≤ a i)
    (fallback c : Fin n → Code) (hbad : ¬ R (decode fallback)) :
    R (decode (nonnegativeBranch fallback c)) ↔ R (decode c) := by
  by_cases h : AllNonnegative c
  · simp only [nonnegativeBranch,if_pos h]
  · rw [nonnegativeBranch,if_neg h]
    constructor
    · intro hfalse
      exact False.elim (hbad hfalse)
    · intro hc
      exact False.elim (h ((allNonnegative_iff c).2 (hR (decode c) hc)))

end MixedVolume.EffectiveSigns
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/Computability/EffectiveSigns.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/CoefficientCoding.lean -/
section


/-!
# Exact rational inputs

A coefficient array is encoded by a fixed finite vector of triples of natural
numbers. A triple `(a,b,c)` denotes `(a-b)/(c+1)`. Every rational coefficient
array has such a code, and membership depends only on the decoded array.
This is the input representation for the computability statements.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.CoefficientCoding

open VolumePolynomials RationalCode

/-- The array contains every ordinary monomial of total degree `d`. -/
def coordinateCount (n d : ℕ) : ℕ := Fintype.card (MultiIndex n d)

def coordinateEquiv (n d : ℕ) : MultiIndex n d ≃ Fin (coordinateCount n d) :=
  Fintype.equivFin _

abbrev ArrayCode (n d : ℕ) := Fin (coordinateCount n d) → RationalCode.Code
abbrev RationalArray (n d : ℕ) := MultiIndex n d → ℚ

def rationalDecode {n d : ℕ} (c : ArrayCode n d) : RationalArray n d :=
  fun a => RationalCode.eval (c (coordinateEquiv n d a))

def realDecode {n d : ℕ} (c : ArrayCode n d) : Coefficients n d :=
  fun a => (rationalDecode c a : ℝ)

def Realizable {n d : ℕ} (c : ArrayCode n d) : Prop :=
  realDecode c ∈ VolumeLocus n d

def Nonnegative {n d : ℕ} (c : ArrayCode n d) : Prop :=
  EffectiveSigns.AllNonnegative c

instance {n d : ℕ} : DecidablePred (Nonnegative (n := n) (d := d)) :=
  fun c => inferInstanceAs (Decidable (EffectiveSigns.AllNonnegative c))

theorem nonnegative_primrec (n d : ℕ) :
    PrimrecPred (Nonnegative (n := n) (d := d)) :=
  EffectiveSigns.allNonnegative_primrec (coordinateCount n d)

/-- The restricted decision problem genuinely has only nonnegative inputs. -/
abbrev NonnegativeArray (n d : ℕ) := {c : ArrayCode n d // Nonnegative c}

instance (n d : ℕ) : Primcodable (NonnegativeArray n d) :=
  Primcodable.subtype (nonnegative_primrec n d)

theorem nonnegative_val_primrec (n d : ℕ) :
    Primrec (Subtype.val : NonnegativeArray n d → ArrayCode n d) :=
  Primrec.subtype_val (hp := nonnegative_primrec n d)

/-- There is no restriction on the rational arrays represented by the input. -/
theorem rationalDecode_surjective (n d : ℕ) :
    Function.Surjective (rationalDecode (n := n) (d := d)) := by
  intro a
  choose c hc using (fun i => RationalCode.eval_surjective (a i))
  refine ⟨fun i => c ((coordinateEquiv n d).symm i),?_⟩
  funext i
  simpa only [rationalDecode,Equiv.symm_apply_apply] using hc i

theorem nonnegative_iff {n d : ℕ} (c : ArrayCode n d) :
    Nonnegative c ↔ ∀ a, 0 ≤ rationalDecode c a := by
  rw [Nonnegative,EffectiveSigns.allNonnegative_iff]
  constructor
  · intro h a; exact h _
  · intro h i
    simpa only [rationalDecode,Equiv.apply_symm_apply] using h ((coordinateEquiv n d).symm i)

/-- The restricted input type represents every coefficientwise nonnegative
rational array, without a bound on entries or denominators. -/
theorem nonnegative_input_coverage {n d : ℕ} (a : RationalArray n d)
    (ha : ∀ i, 0 ≤ a i) :
    ∃ c : NonnegativeArray n d, rationalDecode c.val = a := by
  obtain ⟨c,hc⟩ := rationalDecode_surjective n d a
  refine ⟨⟨c,(nonnegative_iff c).mpr ?_⟩,hc⟩
  simpa only [hc] using ha

theorem realizable_nonnegative {n d : ℕ} {c : ArrayCode n d}
    (hc : Realizable c) : Nonnegative c := by
  rw [nonnegative_iff]
  intro a
  have h := volumeLocus_coefficients_nonnegative hc a
  change (0 : ℝ) ≤ (rationalDecode c a : ℝ) at h
  exact_mod_cast h

theorem membership_ext {n d : ℕ} {c e : ArrayCode n d}
    (h : rationalDecode c = rationalDecode e) : Realizable c ↔ Realizable e := by
  have hh : realDecode c = realDecode e := by ext i; simp [realDecode,h]
  simp only [Realizable,hh]

/-- Pointwise effective rational values assemble into one program emitting the
entire ordinary coefficient array, with its full decoding theorem. -/
theorem output_program {α : Type*} [Primcodable α] {n d : ℕ}
    {f : α → RationalArray n d}
    (hf : ∀ i, RationalPrimrec (fun x => f x i)) :
    ∃ emit : α → ArrayCode n d, Primrec emit ∧ ∀ x, rationalDecode (emit x) = f x := by
  obtain ⟨emit,he,hd⟩ := RationalPrimrec.finite_output
    (fun i : Fin (coordinateCount n d) => hf ((coordinateEquiv n d).symm i))
  refine ⟨emit,he,?_⟩
  intro x
  funext i
  simpa only [rationalDecode,Equiv.symm_apply_apply] using hd x (coordinateEquiv n d i)

end MixedVolume.CoefficientCoding

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/Computability/CoefficientCoding.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/EffectiveMoments.lean -/
section
/- Exact primitive-recursive algorithms for all finite moment resolvents. -/


set_option autoImplicit false

@[expose] public section
open Matrix
open scoped BigOperators

namespace MixedVolume.RationalPrimrec

variable {α ι : Type*} [Primcodable α] [Fintype ι] [DecidableEq ι]

theorem adjugate {M : α → Matrix ι ι ℚ}
    (hM : ∀ i j, RationalPrimrec (fun x => M x i j)) (i j : ι) :
    RationalPrimrec (fun x => (M x).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply RationalPrimrec.det
  intro k l
  by_cases hk : k = j
  · subst k
    simpa only [Matrix.updateRow_self] using
      (RationalPrimrec.const (α := α) ((Pi.single i (1 : ℚ) : ι → ℚ) l))
  · simpa only [Matrix.updateRow_ne hk] using hM k l

theorem rationalSolution {M : α → Matrix ι ι ℚ} {b : α → ι → ℚ}
    (hM : ∀ i j, RationalPrimrec (fun x => M x i j))
    (hb : ∀ i, RationalPrimrec (fun x => b x i)) (i : ι) :
    RationalPrimrec (fun x => RationalSystems.rationalSolution (M x) (b x) i) := by
  have hA (j k : ι) : RationalPrimrec (fun x => (1 - M x) j k) :=
    (RationalPrimrec.const ((1 : Matrix ι ι ℚ) j k)).sub (hM j k)
  exact (RationalPrimrec.det hA).inv.mul
    (finite_sum (fun j => (RationalPrimrec.adjugate hA i j).mul (hb j)))

end MixedVolume.RationalPrimrec

namespace MixedVolume.EffectiveMoments

open RationalPrimrec AutomatonMoments QuadraticMoments ReferenceMoments
variable {α : Type*} [Primcodable α] {s m : ℕ}
variable (D : α → RationalData s m)
variable (hP : ∀ a j k, RationalPrimrec (fun x => (D x).P a j k))
variable (hf : ∀ j, RationalPrimrec (fun x => (D x).f j))

include hP hf

theorem mass_effective (j : Fin m) : RationalPrimrec (fun x => massQ (D x) j) := by
  apply RationalPrimrec.rationalSolution
  · intro j k
    exact (RationalPrimrec.const _).mul (finite_sum (fun a => hP a j k))
  · intro j
    exact (RationalPrimrec.const 1).add (hf j)

theorem first_effective (j : Fin m) : RationalPrimrec (fun x => firstQ (D x) j) := by
  apply RationalPrimrec.rationalSolution
  · intro j k
    exact (RationalPrimrec.const _).mul (finite_sum (fun a => hP a j k))
  · intro j
    exact (RationalPrimrec.const _).mul (finite_sum (fun a => finite_sum (fun k =>
      ((hP a j k).mul (RationalPrimrec.const _)).mul (mass_effective D hP hf k))))

theorem cross_effective (a b : Fin s) (j k : Fin m) :
    RationalPrimrec (fun x => crossMomentQ (D x) a b j k) := by
  unfold crossMomentQ
  split_ifs
  · exact (RationalPrimrec.const _).mul
      (((((RationalPrimrec.const _).mul (mass_effective D hP hf j)).mul
        (mass_effective D hP hf k)).add
        ((mass_effective D hP hf j).mul (first_effective D hP hf k))).sub
        ((first_effective D hP hf j).mul (mass_effective D hP hf k)))
  · exact (RationalPrimrec.const _).mul
      (((((RationalPrimrec.const _).mul (mass_effective D hP hf k)).mul
        (mass_effective D hP hf j)).add
        ((mass_effective D hP hf k).mul (first_effective D hP hf j))).sub
        ((first_effective D hP hf k).mul (mass_effective D hP hf j)))
  · exact RationalPrimrec.const 0

theorem areaSource_effective (p : Fin m × Fin m) :
    RationalPrimrec (fun x => areaSourceQ (D x) p) := by
  exact (((RationalPrimrec.const 1).add (hf p.1)).mul (first_effective D hP hf p.2)).add
    (finite_sum (fun a => finite_sum (fun l => (hP a p.1 l).mul
      ((((RationalPrimrec.const 1).add (hf p.2)).mul
        ((RationalPrimrec.const _).mul ((first_effective D hP hf l).add
          ((RationalPrimrec.const _).mul (mass_effective D hP hf l))))).add
        (finite_sum (fun b => finite_sum (fun r =>
          (hP b p.2 r).mul (cross_effective D hP hf a b l r))))))))

theorem pair_effective (p : Fin m × Fin m) :
    RationalPrimrec (fun x => pairMomentQ (D x) p) := by
  apply RationalPrimrec.rationalSolution
  · intro p q
    exact (RationalPrimrec.const _).mul
      (finite_sum (fun a => (hP a p.1 q.1).mul (hP a p.2 q.2)))
  · exact areaSource_effective D hP hf

theorem offHead_effective (a b : Fin s) (k : Fin m) :
    RationalPrimrec (fun x => offHeadMomentQ (D x) a b k) := by
  unfold offHeadMomentQ
  split_ifs
  · exact ((RationalPrimrec.const _).mul (mass_effective D hP hf k)).sub
      ((RationalPrimrec.const _).mul (first_effective D hP hf k))
  · exact ((RationalPrimrec.const _).mul (first_effective D hP hf k)).sub
      ((RationalPrimrec.const _).mul (mass_effective D hP hf k))
  · exact RationalPrimrec.const 0

theorem thresholdSource_effective (a : Fin s) (j : Fin m) :
    RationalPrimrec (fun x => thresholdSourceQ (D x) a j) := by
  exact ((RationalPrimrec.const _).mul ((RationalPrimrec.const 1).add (hf j))).add
    ((RationalPrimrec.const _).mul (finite_sum (fun b => finite_sum (fun k =>
      (hP b j k).mul (offHead_effective D hP hf a b k)))))

theorem threshold_effective (a : Fin s) (j : Fin m) :
    RationalPrimrec (fun x => thresholdMomentQ (D x) a j) := by
  apply RationalPrimrec.rationalSolution
  · intro j k
    exact (RationalPrimrec.const _).mul (hP a j k)
  · exact thresholdSource_effective D hP hf a

end MixedVolume.EffectiveMoments
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/Computability/EffectiveMoments.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/EffectiveArithmetic.lean -/
section


/-!
# Effective computation of the complete cubic

Every entry of the finite volume calculation has an exact primitive-recursive
rational representation. The input automaton is allowed to vary; no geometric
oracle or bound on the size of a rational input occurs in this statement.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.EffectiveArithmetic

open RationalPrimrec AutomatonMoments QuadraticMoments ReferenceMoments
open PlanarRational GeneralWidths WidthAlgebra CanonicalArithmetic
open GeneralProjections GeneralLabels ReferenceRecursion EffectiveMoments
open scoped BigOperators

variable {α : Type*} [Primcodable α] {s m : ℕ}
variable (D : α → RationalData s m)
variable (hP : ∀ a j k, RationalPrimrec (fun x => (D x).P a j k))
variable (hf : ∀ j, RationalPrimrec (fun x => (D x).f j))

include hP hf in
theorem imageWidth_effective (a : Fin s) (j : Fin m) :
    RationalPrimrec (fun x => imageWidthQ (D x) a j) :=
  (RationalPrimrec.const _).mul
    ((first_effective D hP hf j).add
      ((RationalPrimrec.const _).mul (mass_effective D hP hf j)))

include hP hf in
theorem imageMixed_effective (a b : Fin s) (j k : Fin m) :
    RationalPrimrec (fun x => imageMixedQ (D x) a b j k) := by
  unfold imageMixedQ
  by_cases h : a = b
  · simp only [if_pos h]
    exact ((RationalPrimrec.const _).mul (pair_effective D hP hf (j,k))).add
      (cross_effective D hP hf a b j k)
  · simp only [if_neg h,zero_add]
    exact cross_effective D hP hf a b j k

include hP hf in
theorem stateImage_effective (j : Fin m) (a : Fin s) (k : Fin m) :
    RationalPrimrec (fun x => stateImageQ (D x) j a k) := by
  exact (((RationalPrimrec.const 1).add (hf j)).mul
    (imageWidth_effective D hP hf a k)).add
    (finite_sum fun b => finite_sum fun l =>
      (hP b j l).mul (imageMixed_effective D hP hf b a l k))

include hP hf in
theorem heightQ_effective (i : Primitive s m) :
    RationalPrimrec (fun x => heightQ (D x) i) := by
  rcases i with j | ⟨a,j⟩
  · exact mass_effective D hP hf j
  · exact (RationalPrimrec.const _).mul (mass_effective D hP hf j)

include hP hf in
theorem widthQ_effective (i : Primitive s m) :
    RationalPrimrec (fun x => widthQ (D x) i) := by
  rcases i with j | ⟨a,j⟩
  · exact first_effective D hP hf j
  · exact imageWidth_effective D hP hf a j

include hP hf in
theorem mixedQ_effective (i j : Primitive s m) :
    RationalPrimrec (fun x => mixedQ (D x) i j) := by
  rcases i with i | ⟨a,i⟩ <;> rcases j with j | ⟨b,j⟩
  · exact pair_effective D hP hf (i,j)
  · exact stateImage_effective D hP hf i b j
  · exact stateImage_effective D hP hf j a i
  · exact imageMixed_effective D hP hf a b i j

include hP hf in
theorem head_effective (a b : Fin s) (j : Fin m) :
    RationalPrimrec (fun x => headMomentQ (D x) a b j) := by
  unfold headMomentQ
  by_cases h : b = a
  · simp only [if_pos h]
    exact threshold_effective D hP hf a j
  · simp only [if_neg h]
    exact offHead_effective D hP hf a b j

include hP hf in
theorem statePoint_effective (j : Fin m) (i : Fin 3) :
    RationalPrimrec (fun x => statePointQ (D x) j i) := by
  fin_cases i
  · exact first_effective D hP hf j
  · exact RationalPrimrec.const 0
  · exact mass_effective D hP hf j

include hP hf in
theorem imagePoint_effective (a : Fin s) (j : Fin m) (i : Fin 3) :
    RationalPrimrec (fun x => imagePointQ (D x) a j i) := by
  fin_cases i
  · exact imageWidth_effective D hP hf a j
  · exact (RationalPrimrec.const _).mul (mass_effective D hP hf j)
  · exact RationalPrimrec.const 0

theorem det_effective {u v w : α → Fin 3 → ℚ}
    (hu : ∀ i, RationalPrimrec (fun x => u x i))
    (hv : ∀ i, RationalPrimrec (fun x => v x i))
    (hw : ∀ i, RationalPrimrec (fun x => w x i)) :
    RationalPrimrec (fun x => detQ (u x) (v x) (w x)) := by
  exact (((hu 0).mul (((hv 1).mul (hw 2)).sub ((hv 2).mul (hw 1)))).sub
    ((hu 1).mul (((hv 0).mul (hw 2)).sub ((hv 2).mul (hw 0))))).add
    ((hu 2).mul (((hv 0).mul (hw 1)).sub ((hv 1).mul (hw 0))))

include hP hf in
theorem statePair_effective (k : Fin m) (i j : Reference s) :
    RationalPrimrec (fun x => statePairQ (D x) k i j) := by
  have hdet (i j : Reference s) := (det_effective
    (fun k => RationalPrimrec.const (α := α) (directionQ i k))
    (fun k => RationalPrimrec.const (α := α) (directionQ j k))
    (statePoint_effective D hP hf k)).abs
  rcases i with i | a | u <;> rcases j with j | b | v
  · exact hdet _ _
  · exact hdet _ _
  · exact hdet _ _
  · exact hdet _ _
  · exact hdet _ _
  · exact threshold_effective D hP hf a k
  · exact hdet _ _
  · exact threshold_effective D hP hf b k
  · exact hdet _ _

include hP hf in
theorem imagePair_effective (b : Fin s) (k : Fin m) (i j : Reference s) :
    RationalPrimrec (fun x => imagePairQ (D x) b k i j) := by
  have hdet (i j : Reference s) := (det_effective
    (fun k => RationalPrimrec.const (α := α) (directionQ i k))
    (fun k => RationalPrimrec.const (α := α) (directionQ j k))
    (imagePoint_effective D hP hf b k)).abs
  rcases i with i | a | u <;> rcases j with j | a' | v
  · exact hdet _ _
  · exact hdet _ _
  · exact hdet _ _
  · exact hdet _ _
  · exact hdet _ _
  · exact (RationalPrimrec.const _).mul (head_effective D hP hf a b k)
  · exact hdet _ _
  · exact (RationalPrimrec.const _).mul (head_effective D hP hf a' b k)
  · exact hdet _ _

theorem linear_effective {ι : Type*} [Fintype ι] {c b : α → ι → ℚ}
    (hc : ∀ i, RationalPrimrec (fun x => c x i))
    (hb : ∀ i, RationalPrimrec (fun x => b x i)) :
    RationalPrimrec (fun x => linear (c x) (b x)) := by
  exact finite_sum (fun i => (hb i).mul (hc i))

include hP hf in
theorem area_effective {b : α → Primitive s m → ℚ}
    (hb : ∀ i, RationalPrimrec (fun x => b x i)) :
    RationalPrimrec (fun x => area (D x) (b x)) := by
  exact (RationalPrimrec.const _).mul
    (finite_sum fun i => finite_sum fun j =>
      ((hb i).mul (hb j)).mul (mixedQ_effective D hP hf i j))

include hP hf in
theorem height_effective {b : α → Primitive s m → ℚ}
    (hb : ∀ i, RationalPrimrec (fun x => b x i)) :
    RationalPrimrec (fun x => height (D x) (b x)) :=
  linear_effective (heightQ_effective D hP hf) hb

include hP hf in
theorem width_effective {b : α → Primitive s m → ℚ}
    (hb : ∀ i, RationalPrimrec (fun x => b x i)) :
    RationalPrimrec (fun x => width (D x) (b x)) :=
  linear_effective (widthQ_effective D hP hf) hb

/-- Each of the finite update registers has a primitive-recursive exact value. -/
structure EffectiveStats (z : α → Stats ℚ s) : Prop where
  volume : RationalPrimrec (fun x => (z x).volume)
  area : ∀ i, RationalPrimrec (fun x => (z x).area i)
  width : ∀ i j, RationalPrimrec (fun x => (z x).width i j)

include hP hf in
theorem initialStats_effective {b : α → Fin m → ℚ} {c : α → Fin s × Fin m → ℚ}
    (hb : ∀ i, RationalPrimrec (fun x => b x i))
    (hc : ∀ i, RationalPrimrec (fun x => c x i)) :
    EffectiveStats (fun x => initialStats (D x) (b x) (c x)) := by
  have hs : ∀ i, RationalPrimrec (fun x => stateWeights (s := s) (b x) i) := by
    rintro (i | i)
    · exact hb i
    · exact RationalPrimrec.const 0
  have hi : ∀ i, RationalPrimrec (fun x => imageWeights (c x) i) := by
    rintro (i | i)
    · exact RationalPrimrec.const 0
    · exact hc i
  have ht : ∀ i, RationalPrimrec (fun x => totalWeights (b x) (c x) i) := by
    rintro (i | i)
    · exact hb i
    · exact hc i
  have hl (a : Fin s) : ∀ i, RationalPrimrec (fun x =>
      letterWeights (baseQ s/rhoQ s) a (b x) (c x) i) := by
    rintro (i | ⟨d,i⟩)
    · exact RationalPrimrec.const 0
    · unfold letterWeights
      by_cases h : d = a
      · simp only [if_pos h]
        exact (hc (d,i)).add ((RationalPrimrec.const _).mul (hb i))
      · simp only [if_neg h,add_zero]
        exact hc (d,i)
  constructor
  · exact ((area_effective D hP hf hs).mul (height_effective D hP hf hi)).add
      ((height_effective D hP hf hs).mul (area_effective D hP hf hi))
  · intro r
    rcases r with i | a | u
    · fin_cases i
      · exact (height_effective D hP hf hs).mul (height_effective D hP hf hi)
      · exact (area_effective D hP hf hs).add
          ((width_effective D hP hf hi).mul (height_effective D hP hf hs))
      · exact (area_effective D hP hf hi).add
          ((width_effective D hP hf hs).mul (height_effective D hP hf hi))
    · exact area_effective D hP hf (hl a)
    · exact area_effective D hP hf ht
  · intro i j
    exact (linear_effective (fun k => statePair_effective D hP hf k i j) hb).add
      (linear_effective (fun aj => imagePair_effective D hP hf aj.1 aj.2 i j) hc)

theorem step_effective {z : α → Stats ℚ s} (hz : EffectiveStats z)
    {u : α → ℚ} (hu : RationalPrimrec u) (j : Reference s) :
    EffectiveStats (fun x => step tripleQ (u x) j (z x)) := by
  constructor
  · exact hz.volume.add (hu.mul (hz.area j))
  · intro i; exact (hz.area i).add (hu.mul (hz.width j i))
  · intro i k; exact (hz.width i k).add (hu.mul (RationalPrimrec.const _))

theorem run_effective {u : α → Reference s → ℚ}
    (hu : ∀ j, RationalPrimrec (fun x => u x j)) (refs : List (Reference s))
    {z : α → Stats ℚ s} (hz : EffectiveStats z) :
    EffectiveStats (fun x => run tripleQ (u x) (z x) refs) := by
  induction refs generalizing z with
  | nil => exact hz
  | cons j refs ih => exact ih (step_effective hz (hu j) j)

include hP hf in
theorem formula_effective {w : α → Label s m → ℚ}
    (hw : ∀ i, RationalPrimrec (fun x => w x i)) :
    RationalPrimrec (fun x => formula (D x) (w x)) := by
  exact (run_effective (fun r => hw (ref r)) (references s)
    (initialStats_effective D hP hf
      (fun j => hw (stateLabel j)) (fun aj => hw (imageLabel aj.1 aj.2)))).volume

end MixedVolume.EffectiveArithmetic

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/Computability/EffectiveArithmetic.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/EffectiveReduction.lean -/
section


/-! Primitive-recursive emission of every prescribed rational coefficient. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.EffectiveReduction

open RationalPrimrec AutomatonMoments GeneralLabels GeneralLocus RationalReduction
open CanonicalArithmetic EffectiveArithmetic
open scoped BigOperators

variable {α : Type*} [Primcodable α] {s m : ℕ}
variable (D : α → RationalData s m)
variable (hP : ∀ a j k, RationalPrimrec (fun x => (D x).P a j k))
variable (hf : ∀ j, RationalPrimrec (fun x => (D x).f j))
variable (hstationary : ∀ j, RationalPrimrec (fun x => (D x).stationary j))

include hf hstationary in
theorem gamma_effective : RationalPrimrec (fun x => gammaQ (D x)) :=
  finite_sum (fun j => (hstationary j).mul (hf j))

include hf hstationary in
theorem delta_effective {p : α → Fin m → ℚ} {theta : α → ℚ}
    (hp : ∀ j, RationalPrimrec (fun x => p x j)) (hθ : RationalPrimrec theta) (j : Fin m) :
    RationalPrimrec (fun x => deltaQ (D x) (p x) (theta x) j) := by
  exact (((((RationalPrimrec.const 1).add hθ).div
    ((RationalPrimrec.const 1).add (gamma_effective D hf hstationary))).mul
      (hstationary j))).sub (hp j)

include hP hf hstationary in
/-- The full finite array is effectively emitted for varying transition data,
initial probability rows and cutpoints. Validity is used in the geometric
semantics; the arithmetic computation itself needs no oracle for validity. -/
theorem rationalArray_effective {p : α → Fin m → ℚ} {theta : α → ℚ}
    (hp : ∀ j, RationalPrimrec (fun x => p x j)) (hθ : RationalPrimrec theta)
    (a : VolumePolynomials.MultiIndex (numberOfBodies s m) 3) :
    RationalPrimrec (fun x => rationalArray (D x) (p x) (theta x) a) := by
  apply finite_sum
  intro k
  apply (RationalPrimrec.const _).mul
  apply formula_effective D hP hf
  intro i
  rcases i with r | j | aj | u
  · exact RationalPrimrec.const _
  · exact (RationalPrimrec.const _).add
      ((delta_effective D hf hstationary hp hθ j).mul (RationalPrimrec.const _))
  · exact RationalPrimrec.const _
  · exact RationalPrimrec.const _

end MixedVolume.EffectiveReduction

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/Computability/EffectiveReduction.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/EffectiveSource.lean -/
section
/- Exact finite output programs for the universal prefix automaton source. -/


set_option autoImplicit false

@[expose] public section
noncomputable section

namespace MixedVolume.EffectiveSource
open MatrixMortality MatrixMortality.Undecidability MixedVolume.Computability PrefixPFA

private theorem problem_equiv_primrec : Primrec binaryGPCP4Equiv := Primrec.of_equiv

theorem upper_primrec (a : Fin 4) : Primrec (fun q : BinaryGPCP4 => q.upper a) :=
  Primrec.fin_app.comp (Primrec.fst.comp problem_equiv_primrec) (Primrec.const a)

theorem lower_primrec (a : Fin 4) : Primrec (fun q : BinaryGPCP4 => q.lower a) :=
  Primrec.fin_app.comp ((Primrec.fst.comp Primrec.snd).comp problem_equiv_primrec)
    (Primrec.const a)

theorem upperLeft_primrec : Primrec (fun q : BinaryGPCP4 => q.upperLeft) :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp problem_equiv_primrec

theorem lowerLeft_primrec : Primrec (fun q : BinaryGPCP4 => q.lowerLeft) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    problem_equiv_primrec

abbrev source (index : Nat.Partrec.Code) : BinaryGPCP4 := prefixReduction.emit index

def matrix (index : Nat.Partrec.Code) (a : Fin 4) : Matrix (Fin 7) (Fin 7) ℚ :=
  let q := source index
  relabelMatrix (P q.upper q.lower q.upperLeft q.lowerLeft a)

def initial (index : Nat.Partrec.Code) : Fin 7 → ℚ :=
  let q := source index
  relabelRow (PrefixPFA.initial q.upper q.lower q.upperLeft q.lowerLeft)

theorem matrix_effective (a : Fin 4) (i j : Fin 7) :
    RationalPrimrec (fun index => matrix index a i j) :=
  EffectivePFA.relabel_P_effective
    (upperLeft_primrec.comp prefixReduction.emit_primrec)
    (lowerLeft_primrec.comp prefixReduction.emit_primrec)
    (fun a => (upper_primrec a).comp prefixReduction.emit_primrec)
    (fun a => (lower_primrec a).comp prefixReduction.emit_primrec) a i j

theorem initial_effective (j : Fin 7) : RationalPrimrec (fun index => initial index j) :=
  EffectivePFA.relabel_initial_effective
    (upperLeft_primrec.comp prefixReduction.emit_primrec)
    (lowerLeft_primrec.comp prefixReduction.emit_primrec)
    (fun a => (upper_primrec a).comp prefixReduction.emit_primrec)
    (fun a => (lower_primrec a).comp prefixReduction.emit_primrec) j

/-- A single primitive-recursive program emits every transition coefficient and
every initial probability. Decoding its output gives the exact previously
verified automaton, without real-number comparisons or numerical approximations. -/
theorem output_program :
    ∃ emit : Nat.Partrec.Code →
        (Fin 4 → Fin 7 → Fin 7 → RationalCode.Code) × (Fin 7 → RationalCode.Code),
      Primrec emit ∧
      (∀ index a i j, RationalCode.eval ((emit index).1 a i j) = matrix index a i j) ∧
      (∀ index j, RationalCode.eval ((emit index).2 j) = initial index j) := by
  classical
  choose M hM heM using matrix_effective
  choose p hp hep using initial_effective
  refine ⟨fun index => ((fun a i j => M a i j index),fun j => p j index), ?_, ?_, ?_⟩
  · exact Primrec.pair
      (MatrixMortality.Primrec.fin_function (fun a =>
        MatrixMortality.Primrec.fin_function (fun i =>
          MatrixMortality.Primrec.fin_function (fun j => hM a i j))))
      (MatrixMortality.Primrec.fin_function hp)
  · exact fun index a i j => heM a i j index
  · exact fun index j => hep j index

end MixedVolume.EffectiveSource
end -- original EOF section
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/Computability/EffectiveSource.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/AutomatonCoding.lean -/
section


/-!
# The input and output programs in Theorem 4.3

The input consists of exact rational codes for every transition, output, and
stationary probability. Validity is a primitive-recursive predicate. The
initial row and cutpoint are coded separately and need not be valid for the
coefficient program to terminate. Probability and cutpoint hypotheses enter
only the geometric equivalence.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.AutomatonCoding

open AutomatonMoments RationalPrimrec CoefficientCoding
open scoped BigOperators

variable {α : Type*} [Primcodable α]

theorem finite_forall {ι : Type*} [Fintype ι] {P : ι → α → Prop}
    (hP : ∀ i, PrimrecPred (P i)) : PrimrecPred (fun x => ∀ i, P i x) := by
  classical
  have h : ∀ s : Finset ι, PrimrecPred (fun x => ∀ i ∈ s, P i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact (show PrimrecPred (fun _ : α => True) from
          (Primrec.const true).primrecPred).of_eq (fun _ => by simp)
    | @insert a s ha ih =>
        exact ((hP a).and ih).of_eq (fun _ => by simp)
  exact (h Finset.univ).of_eq (fun _ => by simp)

theorem rational_nonnegative {f : α → ℚ} (hf : RationalPrimrec f) :
    PrimrecPred (fun x => 0 ≤ f x) := by
  obtain ⟨c,hc,he⟩ := hf
  exact (EffectiveSigns.nonnegative_primrec.comp hc).of_eq
    (fun x => by rw [EffectiveSigns.nonnegative_iff,he x])

theorem rational_le {f g : α → ℚ}
    (hf : RationalPrimrec f) (hg : RationalPrimrec g) :
    PrimrecPred (fun x => f x ≤ g x) :=
  (rational_nonnegative (hg.sub hf)).of_eq (fun _ => sub_nonneg)

theorem rational_eq {f g : α → ℚ}
    (hf : RationalPrimrec f) (hg : RationalPrimrec g) :
    PrimrecPred (fun x => f x = g x) :=
  ((rational_le hf hg).and (rational_le hg hf)).of_eq
    (fun _ => le_antisymm_iff.symm)

abbrev RawCode (s m : ℕ) :=
  (Fin s → Fin m → Fin m → RationalCode.Code) ×
    (Fin m → RationalCode.Code) × (Fin m → RationalCode.Code)

def transitions {s m : ℕ} (c : RawCode s m) (a : Fin s) (i j : Fin m) : ℚ :=
  RationalCode.eval (c.1 a i j)

def output {s m : ℕ} (c : RawCode s m) (j : Fin m) : ℚ :=
  RationalCode.eval (c.2.1 j)

def stationary {s m : ℕ} (c : RawCode s m) (j : Fin m) : ℚ :=
  RationalCode.eval (c.2.2 j)

theorem transitions_effective {s m : ℕ} (a : Fin s) (i j : Fin m) :
    RationalPrimrec (fun c : RawCode s m => transitions c a i j) := by
  refine ⟨fun c => c.1 a i j,?_,fun _ => rfl⟩
  exact Primrec.fin_app.comp
    (Primrec.fin_app.comp (Primrec.fin_app.comp Primrec.fst (Primrec.const a))
      (Primrec.const i)) (Primrec.const j)

theorem output_effective {s m : ℕ} (j : Fin m) :
    RationalPrimrec (fun c : RawCode s m => output c j) := by
  refine ⟨fun c => c.2.1 j,?_,fun _ => rfl⟩
  exact Primrec.fin_app.comp (Primrec.fst.comp Primrec.snd) (Primrec.const j)

theorem stationary_effective {s m : ℕ} (j : Fin m) :
    RationalPrimrec (fun c : RawCode s m => stationary c j) := by
  refine ⟨fun c => c.2.2 j,?_,fun _ => rfl⟩
  exact Primrec.fin_app.comp (Primrec.snd.comp Primrec.snd) (Primrec.const j)

def Valid {s m : ℕ} (c : RawCode s m) : Prop :=
  (∀ a i j, 0 ≤ transitions c a i j) ∧
  (∀ a i, ∑ j, transitions c a i j = 1) ∧
  (∀ j, 0 ≤ output c j ∧ output c j ≤ 1) ∧
  (∀ j, 0 ≤ stationary c j) ∧
  (∑ j, stationary c j) = 1 ∧
  (∀ a j, ∑ i, stationary c i * transitions c a i j = stationary c j)

instance {s m : ℕ} : DecidablePred (Valid (s := s) (m := m)) :=
  fun c => inferInstanceAs (Decidable
    ((∀ a i j, 0 ≤ transitions c a i j) ∧
     (∀ a i, ∑ j, transitions c a i j = 1) ∧
     (∀ j, 0 ≤ output c j ∧ output c j ≤ 1) ∧
     (∀ j, 0 ≤ stationary c j) ∧
     (∑ j, stationary c j) = 1 ∧
     (∀ a j, ∑ i, stationary c i * transitions c a i j = stationary c j)))

theorem valid_primrec (s m : ℕ) : PrimrecPred (Valid (s := s) (m := m)) := by
  apply PrimrecPred.and
  · exact finite_forall (fun a => finite_forall (fun i => finite_forall
      (fun j => rational_nonnegative (transitions_effective a i j))))
  apply PrimrecPred.and
  · exact finite_forall (fun a => finite_forall (fun i => rational_eq
      (finite_sum (fun j => transitions_effective a i j)) (RationalPrimrec.const 1)))
  apply PrimrecPred.and
  · exact finite_forall (fun j => (rational_nonnegative (output_effective j)).and
      (rational_le (output_effective j) (RationalPrimrec.const 1)))
  apply PrimrecPred.and
  · exact finite_forall (fun j => rational_nonnegative (stationary_effective j))
  apply PrimrecPred.and
  · exact rational_eq (finite_sum stationary_effective) (RationalPrimrec.const 1)
  · exact finite_forall (fun a => finite_forall (fun j => rational_eq
      (finite_sum (fun i => (stationary_effective i).mul (transitions_effective a i j)))
      (stationary_effective j)))

abbrev DataCode (s m : ℕ) := {c : RawCode s m // Valid c}

instance (s m : ℕ) : Primcodable (DataCode s m) :=
  Primcodable.subtype (valid_primrec s m)

def data {s m : ℕ} (c : DataCode s m) : RationalData s m where
  P := transitions c.val
  P_nonneg := c.property.1
  P_sum := c.property.2.1
  f := output c.val
  f_nonneg j := (c.property.2.2.1 j).1
  f_le_one j := (c.property.2.2.1 j).2
  stationary := stationary c.val
  stationary_nonneg := c.property.2.2.2.1
  stationary_sum := c.property.2.2.2.2.1
  stationary_fixed a := by
    funext j
    exact c.property.2.2.2.2.2 a j

theorem data_ext {s m : ℕ} {A B : RationalData s m}
    (hP : A.P = B.P) (hf : A.f = B.f) (hl : A.stationary = B.stationary) : A = B := by
  cases A
  cases B
  cases hP
  cases hf
  cases hl
  rfl

/-- Every rational automaton satisfying the paper's hypotheses has an input
code. The coded input type imposes exactly those hypotheses. -/
theorem data_surjective (s m : ℕ) : Function.Surjective (data (s := s) (m := m)) := by
  intro A
  choose P hP using (fun a i j => RationalCode.eval_surjective (A.P a i j))
  choose f hf using (fun j => RationalCode.eval_surjective (A.f j))
  choose l hl using (fun j => RationalCode.eval_surjective (A.stationary j))
  let c : RawCode s m := (P,f,l)
  have hp : transitions c = A.P := by funext a i j; exact hP a i j
  have ho : output c = A.f := by funext j; exact hf j
  have hs : stationary c = A.stationary := by funext j; exact hl j
  have hc : Valid c := by
    unfold Valid
    rw [hp,ho,hs]
    refine ⟨A.P_nonneg,A.P_sum,fun j => ⟨A.f_nonneg j,A.f_le_one j⟩,
      A.stationary_nonneg,A.stationary_sum,?_⟩
    intro a j
    exact congrFun (A.stationary_fixed a) j
  refine ⟨⟨c,hc⟩,data_ext hp ho hs⟩

abbrev InputCode (s m : ℕ) := DataCode s m × (Fin m → RationalCode.Code) × RationalCode.Code

def initial {s m : ℕ} (x : InputCode s m) (j : Fin m) : ℚ :=
  RationalCode.eval (x.2.1 j)

def cutpoint {s m : ℕ} (x : InputCode s m) : ℚ := RationalCode.eval x.2.2

theorem input_coverage {s m : ℕ} (A : RationalData s m)
    (p : Fin m → ℚ) (theta : ℚ) :
    ∃ x : InputCode s m, data x.1 = A ∧ initial x = p ∧ cutpoint x = theta := by
  obtain ⟨c,hc⟩ := data_surjective s m A
  choose row hrow using (fun j => RationalCode.eval_surjective (p j))
  obtain ⟨t,ht⟩ := RationalCode.eval_surjective theta
  refine ⟨(c,row,t),hc,?_,ht⟩
  funext j
  exact hrow j

theorem input_raw_effective (s m : ℕ) :
    Primrec (fun x : InputCode s m => x.1.val) :=
  (Primrec.subtype_val (hp := valid_primrec s m)).comp Primrec.fst

theorem initial_effective {s m : ℕ} (j : Fin m) :
    RationalPrimrec (fun x : InputCode s m => initial x j) := by
  refine ⟨fun x => x.2.1 j,?_,fun _ => rfl⟩
  exact Primrec.fin_app.comp (Primrec.fst.comp Primrec.snd) (Primrec.const j)

theorem cutpoint_effective (s m : ℕ) : RationalPrimrec (cutpoint (s := s) (m := m)) :=
  ⟨fun x => x.2.2,Primrec.snd.comp Primrec.snd,fun _ => rfl⟩

/-- One primitive-recursive program computes the complete rational array from
all of the paper's varying rational data. -/
theorem theorem_4_3_algorithm (s m : ℕ) :
    ∃ emit : InputCode s m → ArrayCode (GeneralLocus.numberOfBodies s m) 3,
      Primrec emit ∧ ∀ x, rationalDecode (emit x) =
        RationalReduction.rationalArray (data x.1) (initial x) (cutpoint x) := by
  apply CoefficientCoding.output_program
  intro a
  apply EffectiveReduction.rationalArray_effective (fun x : InputCode s m => data x.1)
  · intro a i j
    exact (transitions_effective a i j).comp (input_raw_effective s m)
  · intro j
    exact (output_effective j).comp (input_raw_effective s m)
  · intro j
    exact (stationary_effective j).comp (input_raw_effective s m)
  · exact initial_effective
  · exact cutpoint_effective s m

end MixedVolume.AutomatonCoding

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/Computability/AutomatonCoding.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/EffectivePadding.lean -/
section


/-! Adding point bodies is a primitive-recursive operation on exact rational
complete coefficient arrays. Its semantic equivalence applies to arbitrary
compact convex realizations of the padded array. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.EffectivePadding

open VolumePolynomials CoefficientCoding MvPolynomial
open scoped BigOperators

def rationalPad {m d : ℕ} (k : ℕ) (c : RationalArray m d) : RationalArray (m+k) d :=
  fun b => ∑ a : MultiIndex m d,
    if Finsupp.mapDomain (Fin.castAdd k) (exponent a) = exponent b then c a else 0

theorem rationalPad_cast {m d : ℕ} (k : ℕ) (c : RationalArray m d) :
    (fun b => (rationalPad k c b : ℝ)) = extraVariables k (fun a => (c a : ℝ)) := by
  funext b
  rw [← extraVariableCoordinate_eval]
  simp only [rationalPad,Rat.cast_sum,extraVariableCoordinate,MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

theorem decode_effective {m d : ℕ} (a : MultiIndex m d) :
    RationalPrimrec (fun c : ArrayCode m d => rationalDecode c a) :=
  RationalPrimrec.eval.comp (Primrec.fin_app.comp Primrec.id (Primrec.const _))

theorem rationalPad_effective {m d : ℕ} (k : ℕ) (b : MultiIndex (m+k) d) :
    RationalPrimrec (fun c : ArrayCode m d => rationalPad k (rationalDecode c) b) := by
  apply RationalPrimrec.finite_sum
  intro a
  by_cases h : Finsupp.mapDomain (Fin.castAdd k) (exponent a) = exponent b
  · simpa only [if_pos h] using decode_effective a
  · simpa only [if_neg h] using (RationalPrimrec.const (α := ArrayCode m d) 0)

theorem exists_padding_program (m d k : ℕ) :
    ∃ pad : ArrayCode m d → ArrayCode (m+k) d, Primrec pad ∧
      ∀ c, rationalDecode (pad c) = rationalPad k (rationalDecode c) :=
  CoefficientCoding.output_program (rationalPad_effective k)

def pad {m d : ℕ} (k : ℕ) : ArrayCode m d → ArrayCode (m+k) d :=
  Classical.choose (exists_padding_program m d k)

theorem pad_primrec {m d : ℕ} (k : ℕ) : Primrec (pad (m := m) (d := d) k) :=
  (Classical.choose_spec (exists_padding_program m d k)).1

theorem pad_decode {m d : ℕ} (k : ℕ) (c : ArrayCode m d) :
    rationalDecode (pad k c) = rationalPad k (rationalDecode c) :=
  (Classical.choose_spec (exists_padding_program m d k)).2 c

theorem pad_realDecode {m d : ℕ} (k : ℕ) (c : ArrayCode m d) :
    realDecode (pad k c) = extraVariables k (realDecode c) := by
  change (fun b => (rationalDecode (pad k c) b : ℝ)) = _
  rw [pad_decode]
  exact rationalPad_cast k (rationalDecode c)

theorem pad_membership {m d : ℕ} (k : ℕ) (c : ArrayCode m d) :
    Realizable (pad k c) ↔ Realizable c := by
  simp only [Realizable,pad_realDecode,extraVariables_mem_iff]

theorem padding_reduction (m d k : ℕ) :
    (Realizable : ArrayCode m d → Prop) ≤₀ (Realizable : ArrayCode (m+k) d → Prop) :=
  ⟨pad k,(pad_primrec k).to_comp,fun c => (pad_membership k c).symm⟩

theorem pad_nonnegative {m d : ℕ} (k : ℕ) {c : ArrayCode m d}
    (hc : Nonnegative c) : Nonnegative (pad k c) := by
  rw [nonnegative_iff,pad_decode]
  intro b
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact (nonnegative_iff c).1 hc a
  · exact le_rfl

def padNonnegative {m d : ℕ} (k : ℕ) (c : NonnegativeArray m d) :
    NonnegativeArray (m+k) d := ⟨pad k c.val,pad_nonnegative k c.property⟩

theorem padNonnegative_primrec {m d : ℕ} (k : ℕ) :
    Primrec (padNonnegative (m := m) (d := d) k) :=
  Primrec.subtype_mk (hp := nonnegative_primrec (m+k) d)
    ((pad_primrec k).comp (nonnegative_val_primrec m d))

theorem padding_reduction_nonnegative (m d k : ℕ) :
    (fun c : NonnegativeArray m d => Realizable c.val) ≤₀
      (fun c : NonnegativeArray (m+k) d => Realizable c.val) :=
  ⟨padNonnegative k,(padNonnegative_primrec k).to_comp,
    fun c => (pad_membership k c.val).symm⟩

end MixedVolume.EffectivePadding

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/Computability/EffectivePadding.lean -/

/- BEGIN SOURCE: MixedVolume/General/HaltingGeometry.lean -/
section


/-! The actual forty-four-body rational coefficient array corresponding to a
halting-code input.  This file proves its exact geometric semantics; the
separate computability layer proves that the array is effectively emitted. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.HaltingGeometry

open VolumePolynomials AutomatonWords AutomatonMoments AutomatonBridge RationalReduction GeneralLocus
open MatrixMortality MatrixMortality.Undecidability

abbrev SourceCode := Nat.Partrec.Code

def codeAutomaton (index : SourceCode) : RationalData 4 7 :=
  let q := MixedVolume.Computability.prefixReduction.emit index
  automaton q.upper q.lower q.upperLeft q.lowerLeft

def codeInitial (index : SourceCode) : Fin 7 → ℚ :=
  let q := MixedVolume.Computability.prefixReduction.emit index
  initialQ q.upper q.lower q.upperLeft q.lowerLeft

def emittedArray (index : SourceCode) : MultiIndex 44 3 → ℚ :=
  rationalArray (codeAutomaton index) (codeInitial index) (1/7)

theorem emittedArray_membership (index : SourceCode) :
    (fun α => (emittedArray index α : ℝ)) ∈ VolumeLocus 44 3 ↔ ¬ CodeHalts index := by
  change (fun α => (rationalArray (codeAutomaton index) (codeInitial index) (1/7) α : ℝ)) ∈
      VolumeLocus (numberOfBodies 4 7) 3 ↔ _
  rw [rationalArray_cast (codeAutomaton index) (by decide)]
  rw [GeneralLocus.coefficientArray_mem_iff (codeAutomaton index).toReal (by decide)
    (fun j => (codeInitial index j : ℝ)) (by
      dsimp [codeInitial]
      exact initialReal_probability _ _ _ _)
    ((1/7 : ℚ) : ℝ) (by norm_num) (by norm_num)]
  have hi : (fun j => (codeInitial index j : ℝ)) =
      initialReal (MixedVolume.Computability.prefixReduction.emit index).upper
        (MixedVolume.Computability.prefixReduction.emit index).lower
        (MixedVolume.Computability.prefixReduction.emit index).upperLeft
        (MixedVolume.Computability.prefixReduction.emit index).lowerLeft := by
    funext j
    rfl
  rw [hi]
  simpa only [codeAutomaton,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
    prefix_halting_equivalence index

end MixedVolume.HaltingGeometry

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/HaltingGeometry.lean -/

/- BEGIN SOURCE: MixedVolume/General/NonnegativeObstruction.lean -/
section


/-! A fixed, explicit, nonnegative rational cubic outside the realization
locus.  It supplies the negative branch when restricting an effective
reduction to coefficientwise nonnegative input arrays. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.NonnegativeObstruction

open VolumePolynomials GeneralLabels MeasureTheory Set MvPolynomial
open scoped BigOperators Pointwise

theorem cube_root_minkowski (A B : Body 3) :
    bodyVolume A ^ (1/3 : ℝ) + bodyVolume B ^ (1/3 : ℝ) ≤ bodyVolume (A+B) ^ (1/3 : ℝ) := by
  let T : Space 3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Space])
  let C := mapBody T.toContinuousLinearMap A
  let D := mapBody T.toContinuousLinearMap B
  let c : ℝ := LinearFrame.volumeFactor T
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have hscale (K : Body 3) : bodyVolume K = c * volume.real
      (mapBody T.toContinuousLinearMap K : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [bodyVolume,coe_mapBody,ContinuousLinearEquiv.coe_coe]
    exact LinearFrame.realVolume_eq_factor_mul_image T (K : Set (Space 3))
  have h := TauCeti.volume_real_rpow_add_volume_real_rpow_le
    (E := EuclideanSpace ℝ (Fin 3)) (by simp) C.nonempty
    C.isCompact.measurableSet.nullMeasurableSet D.nonempty
    D.isCompact.measurableSet.nullMeasurableSet (C+D).isCompact.measure_ne_top
  have he : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ)⁻¹ = 1/3 := by norm_num
  rw [he] at h
  rw [hscale A,hscale B,hscale (A+B),mapBody_add]
  simp only [Real.mul_rpow hc measureReal_nonneg]
  simpa only [mul_add,C,D,ConvexBody.coe_add] using mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hc _)

def badPolynomial : MvPolynomial (Fin 44) ℚ := X 0^3+X 1^3

def badArray (α : MultiIndex 44 3) : ℚ := badPolynomial.coeff (exponent α)

theorem badArray_nonneg (α : MultiIndex 44 3) : 0 ≤ badArray α := by
  simp only [badArray,badPolynomial,MvPolynomial.coeff_add,MvPolynomial.coeff_X_pow]
  split_ifs <;> norm_num

theorem bad_homogeneous : (MvPolynomial.map (algebraMap ℚ ℝ) badPolynomial).IsHomogeneous 3 := by
  simp only [badPolynomial,map_add,map_pow,MvPolynomial.map_X]
  exact (isHomogeneous_X_pow (R := ℝ) 0 3).add (isHomogeneous_X_pow (R := ℝ) 1 3)

theorem evaluate_bad (w : Fin 44 → ℝ) : evaluate (fun α => (badArray α : ℝ)) w = w 0^3+w 1^3 := by
  have hc : (fun α => (badArray α : ℝ)) =
      coefficientsOfPolynomial (d := 3) (MvPolynomial.map (algebraMap ℚ ℝ) badPolynomial) := by
    ext α
    simp [coefficientsOfPolynomial,badArray,MvPolynomial.coeff_map]
  rw [hc,evaluate_eq_polynomial_eval,coefficientPolynomial_coefficientsOfPolynomial _ bad_homogeneous]
  simp [badPolynomial]

theorem badArray_not_realizable : (fun α => (badArray α : ℝ)) ∉ VolumeLocus 44 3 := by
  rintro ⟨K,hK⟩
  have h₀ := hK (unitWeight 0) (unitWeight_nonneg 0)
  have h₁ := hK (unitWeight 1) (unitWeight_nonneg 1)
  have h₂ := hK (unitWeight 0+unitWeight 1) (fun i => add_nonneg (unitWeight_nonneg 0 i) (unitWeight_nonneg 1 i))
  have hv₀ : bodyVolume (K 0) = 1 := by
    rw [evaluate_bad] at h₀
    change _ = bodyVolume (sumBody K (unitWeight 0)) at h₀
    rw [sumBody_unit] at h₀
    norm_num [unitWeight,Pi.single_apply] at h₀
    exact h₀.symm
  have hv₁ : bodyVolume (K 1) = 1 := by
    rw [evaluate_bad] at h₁
    change _ = bodyVolume (sumBody K (unitWeight 1)) at h₁
    rw [sumBody_unit] at h₁
    norm_num [unitWeight,Pi.single_apply] at h₁
    exact h₁.symm
  have hv₂ : bodyVolume (K 0+K 1) = 2 := by
    rw [evaluate_bad] at h₂
    change _ = bodyVolume (sumBody K (unitWeight 0+unitWeight 1)) at h₂
    rw [sumBody_add K _ _ (unitWeight_nonneg 0) (unitWeight_nonneg 1),sumBody_unit,sumBody_unit] at h₂
    norm_num [unitWeight,Pi.single_apply] at h₂
    exact h₂.symm
  have h := cube_root_minkowski (K 0) (K 1)
  rw [hv₀,hv₁,hv₂,Real.one_rpow] at h
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1+1) h 3
  have he : ((2 : ℝ)^(1/3 : ℝ))^3 = 2 := by
    convert Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 3) (by norm_num) (by decide) using 1 <;> norm_num
  rw [he] at hp
  norm_num at hp

end MixedVolume.NonnegativeObstruction

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/General/NonnegativeObstruction.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/HaltingEncoding.lean -/
section


/-!
# A computable reduction to forty-four-body realization

The output is an actual exact rational complete coefficient array. The
nonnegative variant has a primitive-coded subtype as its target, so the
restriction concerns the input domain itself.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.HaltingEncoding

open VolumePolynomials AutomatonMoments AutomatonBridge HaltingGeometry
open EffectiveReduction CoefficientCoding Completeness
open MatrixMortality.Undecidability

/-- Effective emission of a scalar entry of the array from a universal code. -/
theorem emittedArray_effective (a : MultiIndex 44 3) :
    RationalPrimrec (fun index => emittedArray index a) := by
  apply rationalArray_effective codeAutomaton
  · intro letter i j; exact EffectiveSource.matrix_effective letter i j
  · intro j; exact RationalPrimrec.const _
  · intro j; exact RationalPrimrec.const _
  · intro j; exact EffectiveSource.initial_effective j
  · exact RationalPrimrec.const (1/7)

/-- One primitive-recursive program emits the entire array at once. -/
theorem exists_emitter :
    ∃ emit : Nat.Partrec.Code → ArrayCode 44 3,
      Primrec emit ∧ ∀ index, Realizable (emit index) ↔ ¬ CodeHalts index := by
  obtain ⟨emit,he,hd⟩ := CoefficientCoding.output_program emittedArray_effective
  refine ⟨emit,he,?_⟩
  intro index
  change (fun a => (rationalDecode (emit index) a : ℝ)) ∈ VolumeLocus 44 3 ↔ _
  rw [hd index]
  exact emittedArray_membership index

noncomputable def emit : Nat.Partrec.Code → ArrayCode 44 3 :=
  Classical.choose exists_emitter

theorem emit_primrec : Primrec emit := (Classical.choose_spec exists_emitter).1

theorem emit_membership (index : Nat.Partrec.Code) :
    Realizable (emit index) ↔ ¬ CodeHalts index :=
  (Classical.choose_spec exists_emitter).2 index

theorem nonhalting_reduction :
    (fun index => ¬ CodeHalts index) ≤₀ (Realizable : ArrayCode 44 3 → Prop) :=
  ⟨emit,emit_primrec.to_comp,fun index => (emit_membership index).symm⟩

/-- A fixed exact code for x₀³+x₁³, with every other ordinary coefficient zero. -/
noncomputable def fallback : ArrayCode 44 3 :=
  Classical.choose (rationalDecode_surjective 44 3 NonnegativeObstruction.badArray)

theorem fallback_decode : rationalDecode fallback = NonnegativeObstruction.badArray :=
  Classical.choose_spec (rationalDecode_surjective 44 3 NonnegativeObstruction.badArray)

theorem fallback_nonnegative : Nonnegative fallback := by
  rw [nonnegative_iff,fallback_decode]
  exact NonnegativeObstruction.badArray_nonneg

theorem fallback_not_realizable : ¬ Realizable fallback := by
  change ¬ (fun a => (rationalDecode fallback a : ℝ)) ∈ VolumeLocus 44 3
  rw [fallback_decode]
  exact NonnegativeObstruction.badArray_not_realizable

def nonnegativeEmit (index : Nat.Partrec.Code) : ArrayCode 44 3 :=
  EffectiveSigns.nonnegativeBranch fallback (emit index)

theorem nonnegativeEmit_primrec : Primrec nonnegativeEmit :=
  EffectiveSigns.branch_primrec fallback emit_primrec

theorem nonnegativeEmit_nonnegative (index : Nat.Partrec.Code) :
    Nonnegative (nonnegativeEmit index) := by
  unfold nonnegativeEmit Nonnegative EffectiveSigns.nonnegativeBranch
  split_ifs with h
  · exact h
  · exact fallback_nonnegative

theorem nonnegativeEmit_membership (index : Nat.Partrec.Code) :
    Realizable (nonnegativeEmit index) ↔ ¬ CodeHalts index := by
  by_cases h : Nonnegative (emit index)
  · simpa only [nonnegativeEmit,EffectiveSigns.nonnegativeBranch,
      show EffectiveSigns.AllNonnegative (emit index) from h,if_true] using emit_membership index
  · have hh : ¬¬ CodeHalts index := by
      intro hn
      exact h (realizable_nonnegative ((emit_membership index).2 hn))
    have hp : CodeHalts index := not_not.mp hh
    simp only [nonnegativeEmit,EffectiveSigns.nonnegativeBranch,
      show ¬ EffectiveSigns.AllNonnegative (emit index) from h,if_false,
      fallback_not_realizable,hp,not_true]

def emitNonnegative (index : Nat.Partrec.Code) : NonnegativeArray 44 3 :=
  ⟨nonnegativeEmit index,nonnegativeEmit_nonnegative index⟩

theorem emitNonnegative_primrec : Primrec emitNonnegative :=
  Primrec.subtype_mk (hp := nonnegative_primrec 44 3) nonnegativeEmit_primrec

theorem nonhalting_reduction_nonnegative :
    (fun index => ¬ CodeHalts index) ≤₀
      (fun c : NonnegativeArray 44 3 => Realizable c.val) := by
  refine ⟨emitNonnegative,emitNonnegative_primrec.to_comp,?_⟩
  intro index
  simpa only [emitNonnegative] using (nonnegativeEmit_membership index).symm

/-- Undecidability on all rational complete arrays. -/
theorem undecidable : ¬ ComputablePred (Realizable : ArrayCode 44 3 → Prop) :=
  not_computable_of_nonhalting_reduction nonhalting_reduction

/-- Undecidability still holds when every input coefficient is nonnegative. -/
theorem undecidable_nonnegative :
    ¬ ComputablePred (fun c : NonnegativeArray 44 3 => Realizable c.val) :=
  not_computable_of_nonhalting_reduction nonhalting_reduction_nonnegative

/-- No effective verifier has sound, complete finite certificates of realizability. -/
theorem no_realizability_certificates :
    ¬ ∃ verify : ArrayCode 44 3 × ℕ → Prop, ComputablePred verify ∧
      ∀ c, Realizable c ↔ ∃ n, verify (c,n) :=
  no_finite_certificates nonhalting_reduction

end MixedVolume.HaltingEncoding

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/Computability/HaltingEncoding.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/EliminationCorrectness.lean -/
section


/-! Equality of the uniform list program and the geometric halfspace algorithm.
These are equalities of the actual rational lists, including all degenerate,
inconsistent and empty inputs, rather than a restriction to generic polytopes.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MixedVolume.EliminationCorrectness
open VolumePolynomials

def pack {n : ℕ} (p : RationalElimination.Inequality n) : EffectiveElimination.Inequality :=
  (List.ofFn p.coefficient,p.bound)

theorem range_map {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

@[simp] theorem coefficient_pack {n : ℕ} (p : RationalElimination.Inequality n) (i : Fin n) :
    EffectiveElimination.coefficient (pack p) i = p.coefficient i := by
  simp [EffectiveElimination.coefficient,pack,List.getD_eq_getElem?_getD,i.isLt]

@[simp] theorem tail_pack {n : ℕ} (p : RationalElimination.Inequality (n+1)) :
    EffectiveElimination.tail n (pack p) = pack p.tail := by
  apply Prod.ext
  · change (List.ofFn p.coefficient).take n = List.ofFn (fun i : Fin n => p.coefficient i.castSucc)
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_take, List.getElem_ofFn]
      exact congrArg p.coefficient (Fin.ext rfl)
  · rfl

@[simp] theorem combine_pack {n : ℕ} (l u : RationalElimination.Inequality (n+1)) :
    EffectiveElimination.combine n (pack l) (pack u) = pack (RationalElimination.Inequality.combine l u) := by
  have hlast (p : RationalElimination.Inequality (n+1)) :
      EffectiveElimination.coefficient (pack p) n = p.last :=
    coefficient_pack p (Fin.last n)
  apply Prod.ext
  · change (List.range n).map (fun i =>
      EffectiveElimination.coefficient (pack u) n * EffectiveElimination.coefficient (pack l) i -
      EffectiveElimination.coefficient (pack l) n * EffectiveElimination.coefficient (pack u) i) =
        List.ofFn (fun i : Fin n => u.last * l.coefficient i.castSucc - l.last * u.coefficient i.castSucc)
    rw [range_map]
    congr 1
    funext i
    have hli : EffectiveElimination.coefficient (pack l) (i : ℕ) = l.coefficient i.castSucc :=
      coefficient_pack l i.castSucc
    have hui : EffectiveElimination.coefficient (pack u) (i : ℕ) = u.coefficient i.castSucc :=
      coefficient_pack u i.castSucc
    rw [hlast u, hlast l, hli, hui]
  · change EffectiveElimination.coefficient (pack u) n * l.bound -
      EffectiveElimination.coefficient (pack l) n * u.bound = u.last * l.bound - l.last * u.bound
    rw [hlast u, hlast l]

@[simp] theorem negative_pack {n : ℕ} (p : RationalElimination.Inequality n) :
    EffectiveElimination.negative (pack p) = pack (RationalElimination.negative p) := by
  simp [EffectiveElimination.negative,pack,RationalElimination.negative,List.map_ofFn,Function.comp_def]

theorem equality_pack {n : ℕ} (a : Fin n → ℚ) (b : ℚ) :
    EffectiveElimination.equality (List.ofFn a) b = (RationalElimination.equality a b).map pack := by
  simp [EffectiveElimination.equality, RationalElimination.equality,
    EffectiveElimination.negative, RationalElimination.negative, pack,
    List.map_ofFn, Function.comp_def]

theorem eliminate_pack {n : ℕ} (S : List (RationalElimination.Inequality (n+1))) :
    EffectiveElimination.eliminate n (S.map pack) = (RationalElimination.eliminate S).map pack := by
  have hlast (p : RationalElimination.Inequality (n+1)) :
      EffectiveElimination.coefficient (pack p) n=p.last := coefficient_pack p (Fin.last n)
  have hz : (S.map pack).filter (fun p => EffectiveElimination.coefficient p n=0) =
      (S.filter (fun p => p.last=0)).map pack := by
    simp only [List.filter_map,Function.comp_def,hlast]
  have hn : (S.map pack).filter (fun p => EffectiveElimination.coefficient p n<0) =
      (S.filter (fun p => p.last<0)).map pack := by
    simp only [List.filter_map,Function.comp_def,hlast]
  have hp : (S.map pack).filter (fun p => 0<EffectiveElimination.coefficient p n) =
      (S.filter (fun p => 0<p.last)).map pack := by
    simp only [List.filter_map,Function.comp_def,hlast]
  simp only [EffectiveElimination.eliminate,hz,hn,hp,RationalElimination.eliminate,List.map_append,List.map_map,
    List.map_flatMap,List.flatMap_map,Function.comp_def]
  congr 1
  · congr 1
    exact funext fun p => tail_pack p
  · apply List.flatMap_congr
    intro l hl
    congr 1
    exact funext fun u => combine_pack l u

theorem eliminateSuffix_pack (n m : ℕ) (S : List (RationalElimination.Inequality (n+m))) :
    EffectiveElimination.eliminateSuffix n m (S.map pack) = (RationalElimination.eliminateSuffix n m S).map pack := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [EffectiveElimination.eliminateSuffix,eliminate_pack,RationalElimination.eliminateSuffix]
    exact ih (RationalElimination.eliminate S)

theorem ofFn_append {α : Type} {n m : ℕ} (a : Fin n → α) (b : Fin m → α) :
    List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b := by
  rw [List.ofFn_add]
  simp

private theorem nonnegative_coefficients (n m : ℕ) (j : Fin m) :
    (List.range (n+m)).map (fun i => if i=n+j then (-1 : ℚ) else 0) =
      List.ofFn (RationalElimination.nonnegativeConstraint n j).coefficient := by
  rw [range_map]
  congr 1
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [RationalElimination.nonnegativeConstraint,Fin.append_left]
    have h : (a : ℕ) ≠ n+j := by omega
    simp [h]
  · simp only [RationalElimination.nonnegativeConstraint,Fin.append_right]
    by_cases h : b = j
    · subst b
      simp
    · have hval : (b : ℕ) ≠ (j : ℕ) := fun he => h (Fin.ext he)
      simp [h,hval]

private theorem sum_coefficients (n m : ℕ) :
    (List.range (n+m)).map (fun i => if i<n then (0 : ℚ) else 1) =
      List.ofFn (Fin.append (fun _ : Fin n => (0 : ℚ)) (fun _ : Fin m => 1)) := by
  rw [range_map]
  congr 1
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp [a.isLt]
  · simp

theorem barycentricSystem_pack (n : ℕ) (L : List (Fin n → ℚ)) :
    EffectiveElimination.barycentricSystem n L = (RationalElimination.barycentricSystem L.get).map pack := by
  have hfirst :
      (List.range L.length).map (fun j =>
        ((List.range (n+L.length)).map (fun i => if i=n+j then (-1 : ℚ) else 0),0)) =
      (List.ofFn (RationalElimination.nonnegativeConstraint n (m := L.length))).map pack := by
    rw [range_map,List.map_ofFn]
    congr 1
    funext j
    exact Prod.ext (nonnegative_coefficients n L.length j) rfl
  have hlast (i : Fin n) :
      EffectiveElimination.equality ((List.ofFn (fun k : Fin n => if k=i then (1 : ℚ) else 0)) ++
        L.map (fun v => -v i)) 0 =
      (RationalElimination.equality (Fin.append (fun k => if k=i then 1 else 0)
        (fun j => -L.get j i)) 0).map pack := by
    rw [←equality_pack,ofFn_append]
    congr 2
    simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map L (fun v => -v i)).symm
  have hcoordinates :
      (List.ofFn (fun i : Fin n =>
        EffectiveElimination.equality
          ((List.ofFn (fun k : Fin n => if k=i then (1 : ℚ) else 0)) ++
            L.map (fun v => -v i)) 0)).flatten =
      ((List.ofFn (fun i : Fin n =>
        RationalElimination.equality
          (Fin.append (fun k => if k=i then 1 else 0)
            (fun j => -L.get j i)) 0)).flatten).map pack := by
    rw [List.map_flatten,List.map_ofFn]
    exact congrArg List.flatten (congrArg List.ofFn (funext hlast))
  simp only [EffectiveElimination.barycentricSystem,RationalElimination.barycentricSystem,
    List.map_append,hfirst,sum_coefficients,equality_pack,hcoordinates]

theorem hullHalfspaces_pack (n : ℕ) (L : List (Fin n → ℚ)) :
    EffectiveElimination.hullHalfspaces n L = (RationalElimination.hullHalfspaces L.get).map pack := by
  rw [EffectiveElimination.hullHalfspaces,barycentricSystem_pack,eliminateSuffix_pack,RationalElimination.hullHalfspaces]

end MixedVolume.EliminationCorrectness

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/EliminationCorrectness.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/GridCorrectness.lean -/
section


@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace MixedVolume.GridCorrectness
open VolumePolynomials EliminationCorrectness

theorem selections_eq {α : Type} {n : ℕ} (L : Fin n → List α) :
    EffectiveGrids.selections L = RationalHulls.selections L := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [EffectiveGrids.selections,RationalHulls.selections,ih]

theorem nodup_selections {α : Type} {n : ℕ} (L : Fin n → List α)
    (hL : ∀ i, (L i).Nodup) : (EffectiveGrids.selections L).Nodup := by
  induction n with
  | zero => simp [EffectiveGrids.selections]
  | succ n ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro a ha
      apply (ih (Fin.tail L) (fun i => hL i.succ)).map
      intro f g hfg
      funext i
      exact congrFun hfg i.succ
    · apply (hL 0).imp
      intro a b hab x hx hy
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hx
      obtain ⟨g,hg,hfg⟩ := List.mem_map.mp hy
      exact hab (congrFun hfg 0).symm

theorem coordinateGrid_eq (R k : ℕ) :
    EffectiveGrids.coordinateGrid R k = RationalHulls.coordinateGrid R k := by
  rw [EffectiveGrids.coordinateGrid,range_map]
  simp only [RationalHulls.coordinateGrid,Nat.cast_add,Nat.cast_one]

theorem candidateTuples_eq (n d R k : ℕ) :
    EffectiveGrids.candidateTuples n d R k = RationalHulls.candidateTuples n d R k := by
  simp only [EffectiveGrids.candidateTuples,EffectiveGrids.candidates,
    EffectiveGrids.vertexGrid,selections_eq,coordinateGrid_eq,
    RationalHulls.candidateTuples,RationalHulls.candidates,RationalHulls.vertexGrid]

def integerIndex {d : ℕ} (R k : ℕ) (v : Fin d → ℕ) : Fin d → ℤ :=
  fun i => (v i : ℤ)-((R+1)*(k+1) : ℕ)

theorem integerIndex_injective (d R k : ℕ) :
    Function.Injective (integerIndex (d := d) R k) := by
  intro a b h
  funext i
  have hi := congrFun h i
  dsimp [integerIndex] at hi
  have he : (a i : ℤ) = (b i : ℤ) := sub_left_inj.mp hi
  exact_mod_cast he

theorem integerIndex_cast {d : ℕ} (R k : ℕ) (v : Fin d → ℕ) (i : Fin d) :
    (integerIndex R k v i : ℚ) = (v i : ℚ)-((R+1)*(k+1) : ℕ) := by
  simp [integerIndex]

theorem indexList_nodup (d R k : ℕ) : (EffectiveGrids.indexList d R k).Nodup :=
  nodup_selections _ (fun _ => List.nodup_range)

theorem mem_indexList_iff {d R k : ℕ} (v : Fin d → ℕ) :
    v ∈ EffectiveGrids.indexList d R k ↔ ∀ i, v i<2*(R+1)*(k+1) := by
  rw [EffectiveGrids.indexList,selections_eq,RationalHulls.mem_selections]
  simp

theorem integerIndex_grid {d R k : ℕ} (v : Fin d → ℕ)
    (hv : v ∈ EffectiveGrids.indexList d R k) :
    integerIndex R k v ∈ RationalElimination.gridIndices d R k := by
  rw [RationalElimination.gridIndices,Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Ico]
  have hi := (mem_indexList_iff v).mp hv i
  have hi' : (v i : ℤ)<2*((R : ℤ)+1)*((k : ℤ)+1) := by exact_mod_cast hi
  have hn : (0 : ℤ)≤v i := Int.natCast_nonneg _
  simp only [integerIndex,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  constructor <;> nlinarith

theorem exists_integerIndex {d R k : ℕ} (ν : Fin d → ℤ)
    (hν : ν ∈ RationalElimination.gridIndices d R k) :
    ∃ v ∈ EffectiveGrids.indexList d R k, integerIndex R k v=ν := by
  rw [RationalElimination.gridIndices,Fintype.mem_piFinset] at hν
  let v : Fin d → ℕ := fun i => (ν i + ((R+1)*(k+1) : ℕ)).toNat
  have hn (i : Fin d) : (0 : ℤ)≤ν i+((R+1)*(k+1) : ℕ) := by
    have hi := (Finset.mem_Ico.mp (hν i)).1
    push_cast
    nlinarith
  have he (i : Fin d) : (v i : ℤ)=ν i+((R+1)*(k+1) : ℕ) := Int.toNat_of_nonneg (hn i)
  refine ⟨v,(mem_indexList_iff v).mpr ?_,?_⟩
  · intro i
    have hi := (Finset.mem_Ico.mp (hν i)).2
    have h : (v i : ℤ)<(2*(R+1)*(k+1) : ℕ) := by
      rw [he]
      push_cast
      nlinarith
    exact_mod_cast h
  · funext i
    simp only [integerIndex,he,add_sub_cancel_right]

theorem value_pack {d : ℕ} (p : RationalElimination.Inequality d) (x : Fin d → ℚ) :
    EffectiveGrids.value d (pack p) x=p.rationalValue x := by
  simp only [EffectiveGrids.value,coefficient_pack,RationalElimination.Inequality.rationalValue]

theorem corner_pack {d : ℕ} (outer : Bool) (p : RationalElimination.Inequality d)
    (R k : ℕ) (v : Fin d → ℕ) :
    EffectiveGrids.corner d outer (pack p) R k v =
      if outer then p.lowerCorner k (integerIndex R k v)
      else p.upperCorner k (integerIndex R k v) := by
  cases outer <;> funext i
  · simp only [EffectiveGrids.corner,Bool.false_eq_true,if_false,coefficient_pack,
      RationalElimination.Inequality.upperCorner,integerIndex_cast]
    split_ifs <;> simp
  · simp only [EffectiveGrids.corner,if_true,coefficient_pack,
      RationalElimination.Inequality.lowerCorner,RationalElimination.Inequality.upperCorner,
      RationalElimination.negative,neg_nonneg,integerIndex_cast]
    split_ifs <;> simp

theorem test_pack {d : ℕ} (outer : Bool) (S : List (RationalElimination.Inequality d))
    (R k : ℕ) (v : Fin d → ℕ) :
    EffectiveGrids.Test d outer (S.map pack) R k v ↔
      if outer then RationalElimination.outerTest S k (integerIndex R k v)
      else RationalElimination.innerTest S k (integerIndex R k v) := by
  have hbound (p : RationalElimination.Inequality d) : (pack p).2 = p.bound := rfl
  cases outer <;>
    simp only [EffectiveGrids.Test,List.mem_map,forall_exists_index,and_imp,
      forall_apply_eq_imp_iff₂,corner_pack,Bool.false_eq_true,if_false,if_true,value_pack,
      hbound,RationalElimination.innerTest,RationalElimination.outerTest]

theorem boxVolume_pack {d : ℕ} (outer : Bool) (S : List (RationalElimination.Inequality d))
    (R k : ℕ) :
    EffectiveGrids.boxVolume d outer (S.map pack) R k =
      if outer then RationalElimination.upperVolume S R k else RationalElimination.lowerVolume S R k := by
  let P : (Fin d → ℕ) → Prop := fun v => EffectiveGrids.Test d outer (S.map pack) R k v
  let Q : (Fin d → ℤ) → Prop := fun ν =>
    if outer then RationalElimination.outerTest S k ν else RationalElimination.innerTest S k ν
  have hP (v) : P v ↔ Q (integerIndex R k v) := test_pack outer S R k v
  let A := (EffectiveGrids.indexList d R k).filter P
  let B := (RationalElimination.gridIndices d R k).filter Q
  have hcard : A.toFinset.card = B.card := by
    apply Finset.card_bij (fun v _ => integerIndex R k v)
    · intro v hv
      have hv' : v∈EffectiveGrids.indexList d R k ∧ P v := by simpa [A] using hv
      exact Finset.mem_filter.mpr ⟨integerIndex_grid v hv'.1,(hP v).mp hv'.2⟩
    · intro a ha b hb h
      exact integerIndex_injective d R k h
    · intro ν hν
      obtain ⟨hνg,hνq⟩ := Finset.mem_filter.mp hν
      obtain ⟨v,hv,he⟩ := exists_integerIndex ν hνg
      refine ⟨v,?_,he⟩
      have hp : P v := (hP v).mpr (by rwa [he])
      simpa [A] using And.intro hv hp
  have hnodup : A.Nodup := (indexList_nodup d R k).filter _
  rw [List.toFinset_card_of_nodup hnodup] at hcard
  cases outer <;>
    simp only [EffectiveGrids.boxVolume,RationalElimination.upperVolume,
      RationalElimination.lowerVolume,RationalElimination.innerIndices,
      RationalElimination.outerIndices,if_true,Bool.false_eq_true,if_false] <;>
    exact congrArg (fun a : ℕ => (a : ℚ)/((k : ℚ)+1)^d) hcard

end MixedVolume.GridCorrectness

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/GridCorrectness.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/EffectiveNets.lean -/
section


/-! Actual computability of the finite rational coefficient nets.

The terminating sample search is the same `Nat.find` used in the geometric
construction. The equalities in the preceding modules identify every finite
list operation with its dimension-indexed geometric counterpart. The result
therefore computes the existing model, without a replacement assumption.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace MixedVolume.Represented.Effective

theorem ceil : Effective (Nat.ceil : ℚ → ℕ) := by
  have hp : EffectivePred (fun p : ℚ × ℕ => p.1 ≤ (p.2 : ℚ)) :=
    EffectivePred.le fst snd.nat
  have he (q : ℚ) : ∃ k : ℕ, q ≤ (k : ℚ) := ⟨⌈q⌉₊,Nat.le_ceil q⟩
  apply (find hp he).of_eq
  intro q
  apply Nat.le_antisymm
  · exact Nat.find_min' (he q) (Nat.le_ceil q)
  · exact Nat.ceil_le.mpr (Nat.find_spec (he q))

end MixedVolume.Represented.Effective

namespace MixedVolume.EffectiveNets
open VolumePolynomials Represented CoefficientCoding

theorem radiusBound_primitive (d : ℕ) : Primitive (@RationalHulls.radiusBound d) := by
  apply Primitive.list_sum
  apply Primitive.list_map
    (g := fun p : List (Fin d → ℚ) × (Fin d → ℚ) => ∑ i, |p.2 i|) Primitive.id
  apply Primitive.finite_sum
  intro i
  exact (Primitive.fin_app.comp (Primitive.snd.pair (Primitive.const i))).abs

theorem integerRadius_effective (d : ℕ) : Effective (@RationalHulls.integerRadius d) :=
  Effective.ceil.comp (radiusBound_primitive d).effective

theorem hullBoxVolume_effective (d : ℕ) (outer : Bool) :
    Effective (fun p : List (Fin d → ℚ) × ℕ =>
      if outer then RationalElimination.upperVolume (RationalElimination.hullHalfspaces p.1.get)
        (RationalHulls.integerRadius p.1) p.2
      else RationalElimination.lowerVolume (RationalElimination.hullHalfspaces p.1.get)
        (RationalHulls.integerRadius p.1) p.2) := by
  have hh : Effective (fun p : List (Fin d → ℚ) × ℕ =>
      EffectiveElimination.hullHalfspaces d p.1) :=
    (EffectiveElimination.hullHalfspaces_primitive d).effective.comp Effective.fst
  have hr : Effective (fun p : List (Fin d → ℚ) × ℕ =>
      RationalHulls.integerRadius p.1) := (integerRadius_effective d).comp Effective.fst
  have h := (EffectiveGrids.boxVolume_primitive d outer).effective.comp
    (hh.pair (hr.pair Effective.snd))
  exact h.of_eq fun p => by
    rw [EliminationCorrectness.hullHalfspaces_pack,GridCorrectness.boxVolume_pack]

theorem tolerance_primitive : Primitive RationalCoefficientNets.samplingTolerance :=
  (Primitive.const (1 : ℚ)).div (Primitive.id.nat.add (Primitive.const 1))

set_option maxHeartbeats 1000000 in
theorem sample_effective (d : ℕ) :
    Effective (fun p : List (Fin d → ℚ) × ℕ =>
      RationalHulls.approximateHullVolume p.1 (RationalCoefficientNets.samplingTolerance p.2)
        (RationalCoefficientNets.samplingTolerance_pos p.2)) := by
  let P : (List (Fin d → ℚ) × ℕ) × ℕ → Prop := fun p =>
    RationalElimination.upperVolume (RationalElimination.hullHalfspaces p.1.1.get)
      (RationalHulls.integerRadius p.1.1) p.2 -
    RationalElimination.lowerVolume (RationalElimination.hullHalfspaces p.1.1.get)
      (RationalHulls.integerRadius p.1.1) p.2 <
      RationalCoefficientNets.samplingTolerance p.1.2
  have hupper := (hullBoxVolume_effective d true).of_eq
    (g := fun p : List (Fin d → ℚ) × ℕ =>
      RationalElimination.upperVolume (RationalElimination.hullHalfspaces p.1.get)
        (RationalHulls.integerRadius p.1) p.2)
    (fun _ => if_pos rfl)
  have hlower := (hullBoxVolume_effective d false).of_eq
    (g := fun p : List (Fin d → ℚ) × ℕ =>
      RationalElimination.lowerVolume (RationalElimination.hullHalfspaces p.1.get)
        (RationalHulls.integerRadius p.1) p.2)
    (fun _ => if_neg (by decide))
  have hargs : Effective (fun x : (List (Fin d → ℚ) × ℕ) × ℕ =>
      (x.1.1,x.2)) :=
    ((Effective.fst (α := List (Fin d → ℚ)) (β := ℕ)).comp
      (Effective.fst (α := List (Fin d → ℚ) × ℕ) (β := ℕ))).pair Effective.snd
  have hgap := (hupper.comp hargs).sub (hlower.comp hargs)
  have htolerance := tolerance_primitive.effective.comp
    ((Effective.snd (α := List (Fin d → ℚ)) (β := ℕ)).comp
      (Effective.fst (α := List (Fin d → ℚ) × ℕ) (β := ℕ)))
  have hP : EffectivePred P :=
    (EffectivePred.lt hgap htolerance).of_eq (q := P) (fun _ => Iff.rfl)
  have he (p : List (Fin d → ℚ) × ℕ) : ∃ j, P (p,j) :=
    RationalElimination.exists_gap_lt (RationalElimination.hullHalfspaces p.1.get)
      (RationalHulls.integerRadius p.1)
      (by rw [RationalHulls.halfspaces_solution_eq_hull]; exact RationalHulls.hull_subset_ambient p.1)
      (RationalCoefficientNets.samplingTolerance p.2) (RationalCoefficientNets.samplingTolerance_pos p.2)
  have hj := Effective.find hP he
  have h := hlower.comp (Effective.fst.pair hj)
  exact h.of_eq fun p => rfl

theorem weightedVertices_primitive (n d : ℕ) (t : Fin n → ℚ) :
    Primitive (fun L : Fin n → List (Fin d → ℚ) => RationalHulls.weightedVertices L t) := by
  have h : Primitive (fun L : Fin n → List (Fin d → ℚ) =>
      (EffectiveGrids.selections L).map (fun f => ∑ i, t i • f i)) := by
    apply Primitive.list_map
      (g := fun p : (Fin n → List (Fin d → ℚ)) × (Fin n → Fin d → ℚ) =>
        ∑ i, t i • p.2 i) (EffectiveGrids.selections_primitive n)
    apply Primitive.fin_function
    intro j
    apply (Primitive.finite_sum (fun i =>
      (Primitive.const (t i)).mul
        (Primitive.fin_app.comp
          ((Primitive.fin_app.comp (Primitive.snd.pair (Primitive.const i))).pair
            (Primitive.const j))))).of_eq
    intro x
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact h.of_eq fun _ => by rw [GridCorrectness.selections_eq]; rfl

set_option maxHeartbeats 1000000 in
theorem coefficient_effective (n d : ℕ) (a : MultiIndex n d) :
    Effective (fun p : (Fin n → List (Fin d → ℚ)) × ℕ =>
      RationalHulls.approximateCoefficients p.1 (RationalCoefficientNets.samplingTolerance p.2)
        (RationalCoefficientNets.samplingTolerance_pos p.2) a) := by
  have hweights (j : Fin (interpolationSize n d)) :=
    (weightedVertices_primitive n d (interpolationWeight j)).effective.comp
      (Effective.fst (α := Fin n → List (Fin d → ℚ)) (β := ℕ))
  have hsamples (j : Fin (interpolationSize n d)) :=
    (sample_effective d).comp ((hweights j).pair
      (Effective.snd (α := Fin n → List (Fin d → ℚ)) (β := ℕ)))
  have hsum := Effective.finite_sum (fun j : Fin (interpolationSize n d) =>
    (Effective.const (coefficientExtractionWeight a j)).mul (hsamples j))
  exact hsum.of_eq
    (g := fun p : (Fin n → List (Fin d → ℚ)) × ℕ =>
      RationalHulls.approximateCoefficients p.1 (RationalCoefficientNets.samplingTolerance p.2)
        (RationalCoefficientNets.samplingTolerance_pos p.2) a)
    (fun _ => rfl)

noncomputable def netList (n d R k : ℕ) : List (Fin (coordinateCount n d) → ℚ) :=
  (RationalHulls.candidateTuples n d R (RationalCoefficientNets.resolution n d k)).map
    (fun L i => RationalHulls.approximateCoefficients L (RationalCoefficientNets.samplingTolerance k)
      (RationalCoefficientNets.samplingTolerance_pos k) ((coordinateEquiv n d).symm i))

set_option maxHeartbeats 1000000 in
theorem netList_effective (n d R : ℕ) : Effective (netList n d R) := by
  have hres : Primitive (RationalCoefficientNets.resolution n d) :=
    Primitive.nat_mul (Primitive.const (RationalCoefficientNets.gridMultiplier n d))
      (Primitive.nat_add Primitive.id (Primitive.const 1))
  have hc : Primitive (fun k =>
      RationalHulls.candidateTuples n d R (RationalCoefficientNets.resolution n d k)) :=
    ((EffectiveGrids.candidateTuples_primitive n d R).comp hres).of_eq
      (fun k => GridCorrectness.candidateTuples_eq n d R _)
  have hswap := (Effective.snd (α := ℕ) (β := Fin n → List (Fin d → ℚ))).pair
    (Effective.fst (α := ℕ) (β := Fin n → List (Fin d → ℚ)))
  have heach (i : Fin (coordinateCount n d)) :=
    (coefficient_effective n d ((coordinateEquiv n d).symm i)).comp hswap
  have hg := Effective.fin_function heach
  have hmap := Effective.list_map hc.effective hg
  exact hmap.of_eq (g := netList n d R) (fun _ => rfl)

theorem mem_netList_iff (n d R k : ℕ) (q : Fin (coordinateCount n d) → ℚ) :
    q ∈ netList n d R k ↔
      (fun a => q (coordinateEquiv n d a)) ∈ RationalCoefficientNets.coefficientNet n d R k := by
  simp only [netList,RationalCoefficientNets.coefficientNet,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨L,hL,rfl⟩
    exact ⟨L,hL,by funext a; simp⟩
  · rintro ⟨L,hL,hq⟩
    refine ⟨L,hL,?_⟩
    funext i
    simpa only [Equiv.apply_symm_apply] using congrFun hq ((coordinateEquiv n d).symm i)

theorem netError_primitive (n d R : ℕ) : Primitive (RationalCoefficientNets.netError n d R) :=
  ((Primitive.const (((Fintype.card (MultiIndex n d) : ℚ)+1) *
    RationalCoefficientNets.coordinateBudget n d R))).mul tolerance_primitive

end MixedVolume.EffectiveNets

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/EffectiveNets.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/CoRE.lean -/
section


/-! The co-r.e. upper bound on all exact rational coefficient inputs.

A certificate is a rational center, a rational radius and a natural net scale.
Its verifier uses only the programs proved computable in this dependency chain.
The geometric separation theorem proves both soundness and completeness.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Pointwise

namespace MixedVolume.CoRE
open VolumePolynomials Represented CoefficientCoding EffectiveNets QuadraticSeparation

abbrev Vector (n d : ℕ) := Fin (coordinateCount n d) → ℚ
abbrev Certificate (n d : ℕ) := Vector n d × ℚ × ℕ

noncomputable def expand {n d : ℕ} (v : Vector n d) : MultiIndex n d → ℚ :=
  fun a => v (coordinateEquiv n d a)

def Nonnegative {n d : ℕ} (v : Vector n d) : Prop := ∀ i, 0≤v i

def Admission (n d : ℕ) (p : Certificate n d) : Prop :=
  0<p.2.1 ∧ ∀ q∈netList n d d p.2.2,
    (p.2.1+RationalCoefficientNets.netError n d d p.2.2)^2 < ∑ i, (p.1 i-q i)^2

noncomputable def quadraticValue {n d : ℕ} (a : Vector n d) (r : ℚ) (v : Vector n d) : ℚ :=
  (∑ i, (v i-(∑ j, v j)*a i)^2) - r^2*(∑ i, v i)^2

def Reject (n d : ℕ) (p : Vector n d × Certificate n d) : Prop :=
  ¬Nonnegative p.1 ∨ (Admission n d p.2 ∧ quadraticValue p.2.1 p.2.2.1 p.1<0)

theorem nonnegative_primitive (n d : ℕ) : PrimitivePred (@Nonnegative n d) := by
  have h : PrimitivePred (fun v : Vector n d => ∀ q ∈ List.ofFn v, 0≤q) :=
    PrimitivePred.forall_mem (PrimitivePred.le (Primitive.const 0) Primitive.snd)
    (Primitive.list_ofFn (fun i : Fin (coordinateCount n d) =>
      Primitive.fin_app.comp (Primitive.id.pair (Primitive.const i))))
  exact h.of_eq (fun v => by simp [Nonnegative])

theorem admission_effective (n d : ℕ) : EffectivePred (Admission n d) := by
  have hr : Primitive (fun p : Certificate n d => p.2.1) := Primitive.fst.comp Primitive.snd
  have hm : Primitive (fun p : Certificate n d => p.2.2) := Primitive.snd.comp Primitive.snd
  apply EffectivePred.and (PrimitivePred.lt (Primitive.const 0) hr).effective
  apply EffectivePred.forall_mem
    (p := fun p : Certificate n d × Vector n d =>
      (p.1.2.1+RationalCoefficientNets.netError n d d p.1.2.2)^2 <
        ∑ i, (p.1.1 i-p.2 i)^2)
    (f := fun p => netList n d d p.2.2)
  · apply PrimitivePred.lt
    · exact (((hr.add ((netError_primitive n d d).comp hm)).pow 2).comp Primitive.fst)
    · apply Primitive.finite_sum
      intro i
      exact ((Primitive.fin_app.comp
        ((Primitive.fst.comp Primitive.fst).pair (Primitive.const i))).sub
        (Primitive.fin_app.comp (Primitive.snd.pair (Primitive.const i)))).pow 2
  · exact (netList_effective n d d).comp hm.effective

theorem quadraticValue_primitive (n d : ℕ) :
    Primitive (fun p : Vector n d × Certificate n d => quadraticValue p.2.1 p.2.2.1 p.1) := by
  have hv (i : Fin (coordinateCount n d)) :
      Primitive (fun p : Vector n d × Certificate n d => p.1 i) :=
    Primitive.fin_app.comp (Primitive.fst.pair (Primitive.const i))
  have ht := Primitive.finite_sum hv
  apply Primitive.sub
  · apply Primitive.finite_sum
    intro i
    exact ((hv i).sub (ht.mul (Primitive.fin_app.comp
      ((Primitive.fst.comp Primitive.snd).pair (Primitive.const i))))).pow 2
  · exact ((Primitive.fst.comp (Primitive.snd.comp Primitive.snd)).pow 2).mul (ht.pow 2)

theorem reject_effective (n d : ℕ) : EffectivePred (Reject n d) :=
  ((nonnegative_primitive n d).comp Primitive.fst).not.effective.or
    (((admission_effective n d).comp Effective.snd).and
      (PrimitivePred.lt (quadraticValue_primitive n d) (Primitive.const 0)).effective)

theorem admission_iff (n d : ℕ) (p : Certificate n d) :
    Admission n d p ↔ (RationalCoefficientNets.model n d d).Admitted (expand p.1) p.2.1 p.2.2 := by
  change (0 < p.2.1 ∧ ∀ q ∈ netList n d d p.2.2,
      (p.2.1 + RationalCoefficientNets.netError n d d p.2.2)^2 <
        ∑ i, (p.1 i - q i)^2) ↔
    (0 < p.2.1 ∧ ∀ q ∈ RationalCoefficientNets.coefficientNet n d d p.2.2,
      (p.2.1 + RationalCoefficientNets.netError n d d p.2.2)^2 <
        ∑ i, (expand p.1 i - q i)^2)
  apply and_congr_right
  intro hr
  constructor
  · intro h q hq
    let qv : Vector n d := fun i => q ((coordinateEquiv n d).symm i)
    have hmem : qv∈netList n d d p.2.2 := by
      apply (mem_netList_iff n d d p.2.2 qv).mpr
      simpa [qv] using hq
    have hh := h qv hmem
    rw [←(coordinateEquiv n d).sum_comp (fun i => (p.1 i-qv i)^2)] at hh
    simpa only [qv,expand,Equiv.symm_apply_apply] using hh
  · intro h q hq
    have hh := h (expand q) ((mem_netList_iff n d d p.2.2 q).mp hq)
    simpa only [expand,
      (coordinateEquiv n d).sum_comp (fun i => (p.1 i - q i)^2)] using hh

theorem quadraticValue_cast {n d : ℕ} (a v : Vector n d) (r : ℚ) :
    quadratic (expand a) r (WithLp.toLp 2 (fun i => (expand v i : ℝ))) =
      (quadraticValue a r v : ℝ) := by
  have ht : total (WithLp.toLp 2 (fun i => (expand v i : ℝ))) = ((∑ i, v i : ℚ) : ℝ) := by
    change (∑ i, (v (coordinateEquiv n d i) : ℝ)) = _
    simpa only [Rat.cast_sum] using
      (coordinateEquiv n d).sum_comp (fun i => (v i : ℝ))
  rw [quadratic_eq_sum,ht]
  change (∑ i, ((v (coordinateEquiv n d i) : ℝ)-((∑ j,v j : ℚ) : ℝ)*
    (a (coordinateEquiv n d i) : ℝ))^2) - (r : ℝ)^2*((∑ j,v j : ℚ) : ℝ)^2 = _
  rw [(coordinateEquiv n d).sum_comp (fun i =>
    ((v i : ℝ) - ((∑ j, v j : ℚ) : ℝ) * (a i : ℝ))^2)]
  simp only [quadraticValue,Rat.cast_sub,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow]

theorem volumeLocus_iff_admitted (n d : ℕ) (hd : 0<d) (c : Coefficients n d) :
    c∈VolumeLocus n d ↔ (∀ i,0≤c i) ∧
      ∀ (a : MultiIndex n d → ℚ) (r : ℚ) (m : ℕ),
        (RationalCoefficientNets.model n d d).Admitted a r m →
          0≤quadratic a r (WithLp.toLp 2 c) := by
  let V : Set (QuadraticSeparation.Space (MultiIndex n d)) :=
    {x | WithLp.ofLp x∈VolumeLocus n d}
  have hz : (0 : QuadraticSeparation.Space (MultiIndex n d))∈V := zero_mem_volumeLocus hd
  have hn : ∀ x∈V, ∀ i,0≤x i := by
    intro x hx i
    obtain ⟨K,hK⟩ := hx
    exact hK.coefficients_nonnegative i
  have hnorm : ∀ x∈V, x≠0 → normalize x∈(RationalCoefficientNets.model n d d).target := by
    intro x hx hne
    have hs := total_pos (hn x hx) hne
    exact ⟨(total x)⁻¹ • WithLp.ofLp x,normalized_mem_explicit_boundedLocus hd hx hs,rfl⟩
  have hreal : ∀ x,0<total x → normalize x∈(RationalCoefficientNets.model n d d).target → x∈V := by
    intro x hs hx
    obtain ⟨y,hy,he⟩ := hx
    have hnormal : WithLp.ofLp (normalize x)∈VolumeLocus n d := by
      rw [←he]
      exact boundedVolumeLocus_subset n d _ hy
    have h := smul_mem_volumeLocus hd hnormal hs.le
    change total x • ((total x)⁻¹ • WithLp.ofLp x)∈VolumeLocus n d at h
    change WithLp.ofLp x∈VolumeLocus n d
    simpa only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using h
  exact coefficient_characterization (RationalCoefficientNets.model n d d) V hz hn hnorm hreal
    (WithLp.toLp 2 c)

theorem rejection_iff (n d : ℕ) (hd : 0<d) (v : Vector n d) :
    (fun i => (expand v i : ℝ))∉VolumeLocus n d ↔ ∃ p : Certificate n d, Reject n d (v,p) := by
  classical
  rw [volumeLocus_iff_admitted n d hd]
  constructor
  · intro h
    by_cases hv : Nonnegative v
    · have hn : ∀ i, (0 : ℝ)≤expand v i := fun i => by exact_mod_cast hv _
      have hfail : ¬∀ (a : MultiIndex n d → ℚ) (r : ℚ) (m : ℕ),
          (RationalCoefficientNets.model n d d).Admitted a r m →
            0≤quadratic a r (WithLp.toLp 2 (fun i => (expand v i : ℝ))) := fun hh => h ⟨hn,hh⟩
      push_neg at hfail
      obtain ⟨a,r,m,ha,hq⟩ := hfail
      let av : Vector n d := fun i => a ((coordinateEquiv n d).symm i)
      have hea : expand av=a := by funext i; simp [expand,av]
      refine ⟨(av,r,m),Or.inr ⟨(admission_iff n d _).mpr (by simpa only [hea] using ha),?_⟩⟩
      have hh : (quadraticValue av r v : ℝ)<0 := by
        rw [←quadraticValue_cast,hea]
        exact hq
      exact_mod_cast hh
    · exact ⟨(0,0,0),Or.inl hv⟩
  · rintro ⟨p,hp⟩ ⟨hn,hq⟩
    rcases hp with hneg | ⟨ha,hnq⟩
    · apply hneg
      intro i
      have hi : (0 : ℝ) ≤ (v i : ℝ) := by
        simpa only [expand,Equiv.apply_symm_apply] using hn ((coordinateEquiv n d).symm i)
      exact_mod_cast hi
    · have hh := hq (expand p.1) p.2.1 p.2.2 ((admission_iff n d p).mp ha)
      rw [quadraticValue_cast] at hh
      have hh' : (0 : ℚ)≤quadraticValue p.1 p.2.1 v := by exact_mod_cast hh
      exact (not_lt_of_ge hh') hnq

/-- Rejection of arbitrary rational arrays is recursively enumerable, with all
dimensions and all coefficient entries retained. -/
theorem realization_complement_re (n d : ℕ) (hd : 0<d) :
    REPred (fun c : ArrayCode n d => ¬CoefficientCoding.Realizable c) := by
  have h := effective_exists_re (reject_effective n d)
  apply h.of_eq
  intro c
  exact (rejection_iff n d hd (decode c)).symm

/-- The same rejection machine applies to the explicitly nonnegative input
type used in the restricted form of Theorem 1.1. -/
theorem nonnegative_realization_complement_re (n d : ℕ) (hd : 0<d) :
    REPred (fun c : CoefficientCoding.NonnegativeArray n d =>
      ¬CoefficientCoding.Realizable c.val) :=
  (show Partrec _ from realization_complement_re n d hd).comp
    (CoefficientCoding.nonnegative_val_primrec n d).to_comp

end MixedVolume.CoRE

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/CoRE.lean -/

end -- former unit scope
/- END FORMER UNIT: MixedVolume.Computability.DecisionPrograms -/

/- BEGIN FORMER UNIT: MixedVolume.General.UniformFoundations -/
section

/-! Standby source partition. Generation is not a proof certificate.
Exact copied proof ranges are recorded in the adjacent manifest. -/

/- BEGIN SOURCE: MixedVolume/General/FixedAutomatonBridge.lean -/
section


/-! The fixed universal stochastic automaton as the exact geometric input data.
There are two transition matrices and twenty-eight states. Both matrices,
the accepting column, the stationary row, and the cutpoint are fixed rational
data. Only the initial probability row varies with a source program.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.FixedAutomatonBridge

open Matrix MatrixMortality AutomatonMoments AutomatonWords
open scoped BigOperators

def stateEquiv : Fin 28 ≃ FixedUniversal.BlockState :=
  (Fintype.equivFinOfCardEq (by
    simp [FixedUniversal.BlockState,BinarySelector.BlockState,FixedUniversal.State,SevenState.State])).symm

def letterEquiv : Fin 2 ≃ Bool where
  toFun a := if a = 0 then false else true
  invFun b := if b then 1 else 0
  left_inv a := by fin_cases a <;> rfl
  right_inv b := by cases b <;> rfl

def fixedData : RationalData 2 28 where
  P a := (FixedUniversal.matrices (letterEquiv a)).submatrix stateEquiv stateEquiv
  P_nonneg a i j := FixedUniversal.matrices_nonneg _ _ _
  P_sum a i := by
    rw [show (∑ j : Fin 28,
        (FixedUniversal.matrices (letterEquiv a)).submatrix stateEquiv stateEquiv i j) =
        ∑ j, FixedUniversal.matrices (letterEquiv a) (stateEquiv i) j from
      stateEquiv.sum_comp _]
    exact FixedUniversal.matrices_row_sum _ _
  f j := FixedUniversal.output (stateEquiv j)
  f_nonneg j := (FixedUniversal.output_bounds _).1.le
  f_le_one j := (FixedUniversal.output_bounds _).2.le
  stationary _ := 1/28
  stationary_nonneg _ := by norm_num
  stationary_sum := by norm_num
  stationary_fixed a := by
    funext j
    change (∑ i : Fin 28, (1/28 : ℚ) *
      FixedUniversal.matrices (letterEquiv a) (stateEquiv i) (stateEquiv j)) = 1/28
    rw [← Finset.mul_sum]
    rw [show (∑ i : Fin 28,
        FixedUniversal.matrices (letterEquiv a) (stateEquiv i) (stateEquiv j)) =
        ∑ i : FixedUniversal.BlockState,
          FixedUniversal.matrices (letterEquiv a) i (stateEquiv j) from
      stateEquiv.sum_comp (fun i : FixedUniversal.BlockState =>
        FixedUniversal.matrices (letterEquiv a) i (stateEquiv j))]
    rw [FixedUniversal.matrices_column_sum,mul_one]

def fixedInitialQ (index : Nat.Partrec.Code) (j : Fin 28) : ℚ :=
  FixedUniversal.initial index (stateEquiv j)

def fixedInitialReal (index : Nat.Partrec.Code) (j : Fin 28) : ℝ :=
  fixedInitialQ index j

theorem fixedInitialQ_effective (j : Fin 28) :
    RationalPrimrec (fun index => fixedInitialQ index j) :=
  FixedUniversal.initial_effective _

theorem fixedInitialReal_probability (index : Nat.Partrec.Code) :
    ProbabilityRow (fixedInitialReal index) := by
  constructor
  · intro j
    change 0 ≤ (FixedUniversal.initial index (stateEquiv j) : ℝ)
    exact_mod_cast FixedUniversal.initial_nonneg index (stateEquiv j)
  · have h : (∑ j : Fin 28, fixedInitialQ index j) = 1 := by
      rw [show (∑ j : Fin 28, fixedInitialQ index j) =
        ∑ j, FixedUniversal.initial index j from stateEquiv.sum_comp _]
      exact FixedUniversal.initial_sum index
    change (∑ j : Fin 28, (fixedInitialQ index j : ℝ)) = 1
    exact_mod_cast h

theorem relabel_word (w : List (Fin 2)) :
    wordProduct fixedData.P w =
      (wordProduct FixedUniversal.matrices (w.map letterEquiv)).submatrix stateEquiv stateEquiv := by
  induction w with
  | nil => simp [Matrix.submatrix_one_equiv]
  | cons a w ih =>
    simp only [wordProduct_cons,List.map_cons,ih]
    change (FixedUniversal.matrices (letterEquiv a)).submatrix stateEquiv stateEquiv *
        (wordProduct FixedUniversal.matrices (w.map letterEquiv)).submatrix stateEquiv stateEquiv = _
    exact Matrix.submatrix_mul_equiv _ _ stateEquiv stateEquiv stateEquiv

theorem cast_word (w : List (Fin 2)) (i j : Fin 28) :
    fixedData.toReal.wordMatrix w i j = (wordProduct fixedData.P w i j : ℚ) := by
  induction w generalizing i with
  | nil =>
    simp only [Data.wordMatrix_nil,wordProduct_nil,Matrix.one_apply]
    split <;> norm_num
  | cons a w ih =>
    rw [Data.wordMatrix_cons,wordProduct_cons,Matrix.mul_apply,Matrix.mul_apply]
    simp only [Rat.cast_sum,Rat.cast_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [ih]
    rfl

theorem acceptance_cast (index : Nat.Partrec.Code) (w : List (Fin 2)) :
    fixedData.toReal.acceptance (fixedInitialReal index) w =
      (((FixedUniversal.initial index ᵥ*
        wordProduct FixedUniversal.matrices (w.map letterEquiv)) ⬝ᵥ FixedUniversal.output : ℚ) : ℝ) := by
  unfold Data.acceptance Data.value
  rw [Matrix.dotProduct_mulVec]
  have hcast :
      (fixedInitialReal index ᵥ* fixedData.toReal.wordMatrix w) ⬝ᵥ fixedData.toReal.f =
      (((fixedInitialQ index ᵥ* wordProduct fixedData.P w) ⬝ᵥ fixedData.f : ℚ) : ℝ) := by
    simp only [dotProduct,Matrix.vecMul,Rat.cast_sum,Rat.cast_mul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [cast_word]
    rfl
  rw [hcast]
  congr 1
  rw [relabel_word]
  change (∑ j : Fin 28, (∑ i : Fin 28,
      FixedUniversal.initial index (stateEquiv i) *
      wordProduct FixedUniversal.matrices (w.map letterEquiv) (stateEquiv i) (stateEquiv j)) *
      FixedUniversal.output (stateEquiv j)) = _
  have hin (j : Fin 28) :
      (∑ i : Fin 28, FixedUniversal.initial index (stateEquiv i) *
        wordProduct FixedUniversal.matrices (w.map letterEquiv) (stateEquiv i) (stateEquiv j)) =
      ∑ i : FixedUniversal.BlockState, FixedUniversal.initial index i *
        wordProduct FixedUniversal.matrices (w.map letterEquiv) i (stateEquiv j) :=
    stateEquiv.sum_comp (fun i : FixedUniversal.BlockState => FixedUniversal.initial index i *
      wordProduct FixedUniversal.matrices (w.map letterEquiv) i (stateEquiv j))
  simp_rw [hin]
  exact stateEquiv.sum_comp (fun j : FixedUniversal.BlockState =>
    (∑ i : FixedUniversal.BlockState, FixedUniversal.initial index i *
      wordProduct FixedUniversal.matrices (w.map letterEquiv) i j) * FixedUniversal.output j)

/-- No intended-language restriction is imposed on the universally quantified
binary word. -/
theorem fixed_cutpoint_iff (index : Nat.Partrec.Code) :
    fixedData.toReal.UniversalCutpoint (fixedInitialReal index) (1/2) ↔
      ¬ MatrixMortality.Undecidability.CodeHalts index := by
  rw [← FixedUniversal.universal_iff index]
  have heq (w : List (Fin 2)) :
      fixedData.toReal.acceptance (fixedInitialReal index) w ≤ 1/2 ↔
        (FixedUniversal.initial index ᵥ* wordProduct FixedUniversal.matrices
          (w.map letterEquiv)) ⬝ᵥ FixedUniversal.output ≤ 1/2 := by
    rw [acceptance_cast]
    have hc : ((1/2 : ℚ) : ℝ) = 1/2 := by norm_num
    rw [← hc,Rat.cast_le]
  change (∀ w, _ ≤ _) ↔ _
  simp_rw [heq]
  constructor
  · intro h w
    simpa only [List.map_map,Function.comp_def,letterEquiv.apply_symm_apply,List.map_id_fun',id_eq] using
      h (w.map letterEquiv.symm)
  · intro h w
    exact h (w.map letterEquiv)

end MixedVolume.FixedAutomatonBridge

end -- noncomputable section
end -- public section
end -- component scope
/- END SOURCE: MixedVolume/General/FixedAutomatonBridge.lean -/

/- BEGIN SOURCE: MixedVolume/General/FixedSection.lean -/
section


/-! Corollary 5.1, with an explicit fixed rational quadratic map from the
twenty-eight-coordinate probability simplex to all cubic coefficients of
ninety-one bodies. Rational inputs use a surjective, denominator-safe coding.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.FixedSection

open VolumePolynomials AutomatonWords AutomatonMoments GeneralLabels
open GeneralTarget GeneralDeficit GeneralLocus CanonicalArithmetic ParameterDegree
open RationalExtraction RationalReduction MvPolynomial FixedAutomatonBridge
open scoped BigOperators

abbrev Label := GeneralLabels.Label 2 28
abbrev Index := MultiIndex 91 3

def delta (j : Fin 28) : MvPolynomial (Fin 28) ℚ :=
  C (deltaQ fixedData (fun _ => 0) (1/2) j) - X j

def weight (w : Label → ℚ) : Label → MvPolynomial (Fin 28) ℚ
  | .inr (.inl j) => C (w (stateLabel j)) + delta j * C (w deficitLabel)
  | i => C (w i)

/-- The complete cubic coefficient at an arbitrary multindex, as a rational
polynomial in the twenty-eight initial probabilities alone. -/
def symbol (α : Index) : MvPolynomial (Fin 28) ℚ :=
  ∑ k, C (RationalExtraction.coefficientExtractionWeight α k) * formula fixedData (weight (sample k))

def sectionMap (p : Fin 28 → ℝ) : Coefficients 91 3 :=
  fun α => MvPolynomial.aeval p (symbol α)

def rationalSection (p : Fin 28 → ℚ) (α : Index) : ℚ :=
  MvPolynomial.eval p (symbol α)

theorem rationalSection_cast (p : Fin 28 → ℚ) (α : Index) :
    (rationalSection p α : ℝ) = sectionMap (fun j => (p j : ℝ)) α := by
  unfold rationalSection sectionMap
  rw [MvPolynomial.aeval_def]
  simpa only [MvPolynomial.eval₂_id,RingHom.comp_id,eq_ratCast] using
    MvPolynomial.hom_eval₂ (symbol α) (RingHom.id ℚ) (algebraMap ℚ ℝ) p

theorem delta_degree (j : Fin 28) : (delta j).totalDegree ≤ 1 := by
  apply (totalDegree_sub _ _).trans
  exact max_le ((degree_C _).trans (by omega)) ((isHomogeneous_X ℚ j).totalDegree_le)

theorem symbol_degree (α : Index) : (symbol α).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro k _
  apply (degree_mul (e := 2) (degree_C _) ?_).trans (by omega)
  apply formula_degree fixedData
  · intro r; exact degree_C _
  · intro j
    exact degree_add ((degree_C _).trans (by omega))
      ((degree_mul (delta_degree j) (degree_C _)).trans (by omega))
  · intro a j; exact degree_C _

theorem eval_delta (p : Fin 28 → ℝ) (j : Fin 28) :
    MvPolynomial.aeval p (delta j) = targetDelta fixedData.toReal p (1/2) j := by
  simp [delta,deltaQ,targetDelta,eta,cast_gammaQ,RationalData.toReal]

theorem eval_weight (p : Fin 28 → ℝ) (w : Label → ℚ) (i : Label) :
    MvPolynomial.aeval p (weight w i) =
      shiftWeight (targetDelta fixedData.toReal p (1/2)) (fun j => (w j : ℝ)) i := by
  rcases i with r | j | aj | u <;>
    simp [weight,shiftWeight,eval_delta,stateLabel]

theorem sectionMap_eq (p : Fin 28 → ℝ) :
    sectionMap p = RationalReduction.coefficientMap fixedData p (1/2) := by
  rw [RationalReduction.coefficientMap_eq fixedData (by decide)]
  ext α
  rw [sectionMap,symbol,map_sum]
  rw [RationalExtraction.coefficient_eq_rational_samples
    (GeneralLocus.coefficientArray fixedData.toReal (by decide) p (1/2)) α]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul,MvPolynomial.aeval_C,map_formula]
  rw [GeneralLocus.evaluate_coefficientArray,CanonicalVolume.targetPolynomial_eval_formula]
  congr 2
  funext i
  exact eval_weight p (sample k) i

theorem section_membership (p : Fin 28 → ℝ) (hp : ProbabilityRow p) :
    sectionMap p ∈ VolumeLocus 91 3 ↔
      fixedData.toReal.UniversalCutpoint p (1/2) := by
  rw [sectionMap_eq,RationalReduction.coefficientMap_eq fixedData (by decide)]
  exact GeneralLocus.coefficientArray_mem_iff fixedData.toReal (by decide)
    p hp (1/2) (by norm_num) (by norm_num)

abbrev Input := Fin 28 → RationalCode.Code

def decode (c : Input) (j : Fin 28) : ℝ := RationalCode.eval (c j)

/-- Rational membership on the probability-simplex domain. The guard states
the exact domain of Corollary 5.1; emitted hard instances always satisfy it. -/
def RationalMembership (c : Input) : Prop :=
  ProbabilityRow (decode c) ∧ sectionMap (decode c) ∈ VolumeLocus 91 3

theorem rational_input_coverage (p : Fin 28 → ℚ) :
    ∃ c : Input, decode c = fun j => (p j : ℝ) := by
  choose c hc using (fun j => RationalCode.eval_surjective (p j))
  refine ⟨c,?_⟩
  funext j
  simp only [decode,hc]

/-- A primitive-recursive exact initial-row code for every source program. -/
def initialCodes : Nat.Partrec.Code → Input :=
  Classical.choose (RationalPrimrec.finite_output fixedInitialQ_effective)

theorem initialCodes_primrec : Primrec initialCodes :=
  (Classical.choose_spec (RationalPrimrec.finite_output fixedInitialQ_effective)).1

theorem decode_initialCodes (index : Nat.Partrec.Code) :
    decode (initialCodes index) = fixedInitialReal index := by
  funext j
  have h := (Classical.choose_spec
    (RationalPrimrec.finite_output fixedInitialQ_effective)).2 index j
  change (RationalCode.eval (initialCodes index j) : ℝ) = (fixedInitialQ index j : ℝ)
  exact congrArg (fun q : ℚ => (q : ℝ)) h

theorem hard_instance (index : Nat.Partrec.Code) :
    RationalMembership (initialCodes index) ↔
      ¬ MatrixMortality.Undecidability.CodeHalts index := by
  unfold RationalMembership
  rw [decode_initialCodes]
  rw [and_iff_right (fixedInitialReal_probability index)]
  rw [section_membership _ (fixedInitialReal_probability index),fixed_cutpoint_iff]

theorem nonhalting_reduces_section :
    (fun c => ¬ MatrixMortality.Undecidability.CodeHalts c) ≤₀ RationalMembership :=
  ⟨initialCodes,initialCodes_primrec.to_comp,fun c => (hard_instance c).symm⟩

/-- Even an algorithm required to be correct only on probability rows would
decide the halting problem. No computability assumption about a promise guard
is needed for this precise simplex-domain formulation. -/
theorem no_decider_on_simplex :
    ¬ ∃ decision : Input → Bool, Computable decision ∧
      ∀ c, ProbabilityRow (decode c) →
        (decision c = true ↔ sectionMap (decode c) ∈ VolumeLocus 91 3) := by
  rintro ⟨decision,hd,correct⟩
  have hnon : ComputablePred (fun index =>
      ¬ MatrixMortality.Undecidability.CodeHalts index) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun index => decision (initialCodes index),hd.comp initialCodes_primrec.to_comp,?_⟩
    funext index
    apply propext
    have hp : ProbabilityRow (decode (initialCodes index)) := by
      rw [decode_initialCodes]
      exact fixedInitialReal_probability index
    have hc := correct (initialCodes index) hp
    have hh := hard_instance index
    change (ProbabilityRow _ ∧ _) ↔ _ at hh
    rw [and_iff_right hp] at hh
    exact hh.symm.trans hc.symm
  exact MatrixMortality.Undecidability.codeHalts_not_computable
    (hnon.not.of_eq (fun _ => not_not))

/-- Corollary 5.1: the rational quadratic section has undecidable rational
membership, and all twenty-eight initial probabilities remain its variables. -/
theorem corollary_5_1 :
    (∀ α : Index, (symbol α).totalDegree ≤ 2) ∧
      ¬ ∃ decision : Input → Bool, Computable decision ∧
        ∀ c, ProbabilityRow (decode c) →
          (decision c = true ↔ sectionMap (decode c) ∈ VolumeLocus 91 3) :=
  ⟨symbol_degree,no_decider_on_simplex⟩

theorem rational_membership_not_computable : ¬ComputablePred RationalMembership :=
  Completeness.not_computable_of_nonhalting_reduction nonhalting_reduces_section

theorem rational_section_not_re : ¬REPred RationalMembership :=
  Completeness.not_re_of_nonhalting_reduction nonhalting_reduces_section

end MixedVolume.FixedSection

end -- noncomputable section
end -- public section
end -- component scope
/- END SOURCE: MixedVolume/General/FixedSection.lean -/

/- BEGIN SOURCE: MixedVolume/General/FixedCoefficientFamily.lean -/
section


/-! The fixed quadratic family as an exact coefficient-code decision problem.

The promise consists of rational coefficient arrays in the image of the whole
real probability simplex. Even partial procedures which halt on every promised
input cannot decide membership. Each hard input has an explicitly coded rational
parameter row, so the same obstruction holds on the rational-parameter image.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.FixedSection

open CoefficientCoding VolumePolynomials AutomatonWords FixedAutomatonBridge

theorem rationalSection_effective (a : Index) :
    RationalPrimrec (fun c : Input => rationalSection (fun j => RationalCode.eval (c j)) a) := by
  exact RationalPrimrec.polynomial_eval (symbol a) (fun j =>
    RationalPrimrec.eval.comp (Primrec.fin_app.comp Primrec.id (Primrec.const j)))

/-- The entire array is emitted together, not merely one selected coefficient. -/
def coefficientProgram : Input → ArrayCode 91 3 :=
  Classical.choose (output_program rationalSection_effective)

theorem coefficientProgram_primrec : Primrec coefficientProgram :=
  (Classical.choose_spec (output_program rationalSection_effective)).1

theorem coefficientProgram_rational (c : Input) :
    rationalDecode (coefficientProgram c) =
      rationalSection (fun j => RationalCode.eval (c j)) :=
  (Classical.choose_spec (output_program rationalSection_effective)).2 c

theorem coefficientProgram_semantics (c : Input) :
    realDecode (coefficientProgram c) = sectionMap (decode c) := by
  ext a
  change (rationalDecode (coefficientProgram c) a : ℝ) = _
  rw [coefficientProgram_rational]
  exact rationalSection_cast _ a

/-- Rational coefficient arrays lying in the image of the real probability
simplex under this one fixed rational quadratic map. -/
def OnImage (c : ArrayCode 91 3) : Prop :=
  ∃ p : Fin 28 → ℝ, ProbabilityRow p ∧ realDecode c = sectionMap p

/-- The smaller promise where the parameter row itself is rational. -/
def OnRationalImage (c : ArrayCode 91 3) : Prop :=
  ∃ p : Input, ProbabilityRow (decode p) ∧ realDecode c = sectionMap (decode p)

theorem onRationalImage_iff (c : ArrayCode 91 3) :
    OnRationalImage c ↔ ∃ p : Fin 28 → ℚ,
      ProbabilityRow (fun j => (p j : ℝ)) ∧
        realDecode c = sectionMap (fun j => (p j : ℝ)) := by
  constructor
  · rintro ⟨p,hp,he⟩
    exact ⟨fun j => RationalCode.eval (p j),hp,he⟩
  · rintro ⟨p,hp,he⟩
    obtain ⟨encoded,heq⟩ := rational_input_coverage p
    exact ⟨encoded,by simpa only [heq] using hp,by simpa only [heq] using he⟩

theorem onRationalImage_implies_onImage {c : ArrayCode 91 3} (hc : OnRationalImage c) :
    OnImage c := by
  obtain ⟨p,hp,he⟩ := hc
  exact ⟨decode p,hp,he⟩

def hardCoefficientProgram (index : Nat.Partrec.Code) : ArrayCode 91 3 :=
  coefficientProgram (initialCodes index)

theorem hardCoefficientProgram_primrec : Primrec hardCoefficientProgram :=
  coefficientProgram_primrec.comp initialCodes_primrec

theorem hardCoefficientProgram_promised (index : Nat.Partrec.Code) :
    OnRationalImage (hardCoefficientProgram index) := by
  refine ⟨initialCodes index,?_,coefficientProgram_semantics _⟩
  rw [decode_initialCodes]
  exact fixedInitialReal_probability index

theorem hardCoefficientProgram_correct (index : Nat.Partrec.Code) :
    Realizable (hardCoefficientProgram index) ↔
      ¬ MatrixMortality.Undecidability.CodeHalts index := by
  change realDecode (coefficientProgram (initialCodes index)) ∈ VolumeLocus 91 3 ↔ _
  rw [coefficientProgram_semantics,decode_initialCodes,
    section_membership _ (fixedInitialReal_probability index),fixed_cutpoint_iff]

/-- No partial recursive algorithm can decide the realizability of rational
arrays promised to belong to this fixed quadratic family, even when their
parameter rows are rational. -/
theorem no_partial_decider_on_rational_image :
    ¬ ∃ decision : ArrayCode 91 3 →. Bool, Partrec decision ∧
      ∀ c, OnRationalImage c → ∃ answer : Bool,
        answer ∈ decision c ∧ (answer = true ↔ Realizable c) :=
  Completeness.no_partial_decider_on_promise hardCoefficientProgram
    hardCoefficientProgram_primrec.to_comp hardCoefficientProgram_promised
    hardCoefficientProgram_correct

theorem no_partial_decider_on_image :
    ¬ ∃ decision : ArrayCode 91 3 →. Bool, Partrec decision ∧
      ∀ c, OnImage c → ∃ answer : Bool,
        answer ∈ decision c ∧ (answer = true ↔ Realizable c) := by
  rintro ⟨decision,hd,hcorrect⟩
  exact no_partial_decider_on_rational_image
    ⟨decision,hd,fun c hc => hcorrect c (onRationalImage_implies_onImage hc)⟩

/-- Corollary 5.1 in coefficient-space form, with a full promise-decision
statement and all twenty-eight probabilities retained as polynomial variables. -/
theorem corollary_5_1_coefficient_form :
    (∀ a : Index, (symbol a).totalDegree ≤ 2) ∧
      ¬ ∃ decision : ArrayCode 91 3 →. Bool, Partrec decision ∧
        ∀ c, OnImage c → ∃ answer : Bool,
          answer ∈ decision c ∧ (answer = true ↔ Realizable c) :=
  ⟨symbol_degree,no_partial_decider_on_image⟩

/-- The existential wording of Corollary 5.1. The preceding definitions give
the specific rational polynomial map witnessing this statement. -/
theorem corollary_5_1_exists :
    ∃ P : Index → MvPolynomial (Fin 28) ℚ,
      (∀ a, (P a).totalDegree ≤ 2) ∧
        ¬ ∃ decision : ArrayCode 91 3 →. Bool, Partrec decision ∧
          ∀ c, (∃ p : Fin 28 → ℝ, ProbabilityRow p ∧
              realDecode c = fun a => MvPolynomial.aeval p (P a)) →
            ∃ answer : Bool, answer ∈ decision c ∧
              (answer = true ↔ Realizable c) :=
  ⟨symbol,symbol_degree,no_partial_decider_on_image⟩

end MixedVolume.FixedSection

end -- noncomputable section
end -- public section
end -- component scope
/- END SOURCE: MixedVolume/General/FixedCoefficientFamily.lean -/

/- BEGIN SOURCE: MixedVolume/General/ExplicitLabels.lean -/
section


/-! Explicit block numbering of the canonical labels.  Unlike the abstract
finite equivalence used in the geometric proof, its natural-number coordinate
is a fixed arithmetic expression in the alphabet and state dimensions. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.ExplicitLabels

open GeneralLabels GeneralLocus VolumePolynomials GeneralTarget GeneralDeficit

def unitEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := Subsingleton.elim _ _

def referenceEquiv (s : ℕ) : Reference s ≃ Fin (3 + (s + 1)) :=
  (Equiv.sumCongr (Equiv.refl (Fin 3))
    ((Equiv.sumCongr (Equiv.refl (Fin s)) unitEquiv).trans finSumFinEquiv)).trans
    finSumFinEquiv

def referenceIndex {s : ℕ} : Reference s → ℕ
  | .inl i => i.val
  | .inr (.inl a) => 3 + a.val
  | .inr (.inr _) => 3 + s

@[simp] theorem referenceEquiv_val {s : ℕ} (i : Reference s) :
    (referenceEquiv s i).val = referenceIndex i := by
  rcases i with i | a | u <;>
    simp [referenceEquiv,referenceIndex,unitEquiv,Equiv.trans_apply,
      finSumFinEquiv,Equiv.sumCongr]

def labelEquiv (s m : ℕ) : Label s m ≃ Fin (numberOfBodies s m) :=
  ((Equiv.sumCongr (referenceEquiv s)
    ((Equiv.sumCongr (Equiv.refl (Fin m))
      ((Equiv.sumCongr finProdFinEquiv unitEquiv).trans finSumFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv).trans
    (finCongr (by dsimp [numberOfBodies]; ring))

/-- Zero-based block indices: axes, letters, identity, states, images, deficit. -/
def index {s m : ℕ} : Label s m → ℕ
  | .inl (.inl i) => i.val
  | .inl (.inr (.inl a)) => 3 + a.val
  | .inl (.inr (.inr _)) => 3 + s
  | .inr (.inl j) => 3 + (s + 1) + j.val
  | .inr (.inr (.inl (a,j))) => 3 + (s + 1) + (m + (j.val + m*a.val))
  | .inr (.inr (.inr _)) => 3 + (s + 1) + (m + s*m)

@[simp] theorem index_ref {s m : ℕ} (r : Reference s) :
    index (ref (m := m) r) = referenceIndex r := by
  rcases r with i | a | u <;> rfl

@[simp] theorem labelEquiv_val {s m : ℕ} (i : Label s m) :
    (labelEquiv s m i).val = index i := by
  rcases i with (i | a | u) | j | ⟨a,j⟩ | u <;>
    simp [labelEquiv,referenceEquiv,unitEquiv,index,Equiv.trans_apply,
      finSumFinEquiv,finProdFinEquiv,finCongr,Equiv.sumCongr]

theorem index_lt {s m : ℕ} (i : Label s m) : index i < numberOfBodies s m := by
  rw [← labelEquiv_val]
  exact (labelEquiv s m i).isLt

/-- The explicit and abstract arrays differ by this finite permutation. -/
def relabel (s m : ℕ) : Fin (numberOfBodies s m) ≃ Fin (numberOfBodies s m) :=
  (GeneralLocus.labelEquiv s m).symm.trans (labelEquiv s m)

@[simp] theorem relabel_label {s m : ℕ} (i : Label s m) :
    relabel s m (GeneralLocus.labelEquiv s m i) = labelEquiv s m i := by
  simp [relabel]

def polynomial {s m : ℕ} (A : AutomatonWords.Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (theta : ℝ) : MvPolynomial (Fin (numberOfBodies s m)) ℝ :=
  MvPolynomial.rename (labelEquiv s m)
    (targetPolynomial A hs (targetDelta A p theta))

theorem polynomial_relabel {s m : ℕ} (A : AutomatonWords.Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (theta : ℝ) :
    polynomial A hs p theta = MvPolynomial.rename (relabel s m)
      (GeneralLocus.polynomial A hs p theta) := by
  unfold polynomial GeneralLocus.polynomial
  rw [MvPolynomial.rename_rename]
  have he : (relabel s m : Fin (numberOfBodies s m) → Fin (numberOfBodies s m)) ∘
      (GeneralLocus.labelEquiv s m : Label s m → Fin (numberOfBodies s m)) =
      (labelEquiv s m : Label s m → Fin (numberOfBodies s m)) := by
    funext i
    exact relabel_label i
  rw [he]

theorem polynomial_homogeneous {s m : ℕ} (A : AutomatonWords.Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (theta : ℝ) : (polynomial A hs p theta).IsHomogeneous 3 :=
  (targetPolynomial_homogeneous A hs (targetDelta A p theta)).rename_isHomogeneous

def coefficientArray {s m : ℕ} (A : AutomatonWords.Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (theta : ℝ) : Coefficients (numberOfBodies s m) 3 :=
  coefficientsOfPolynomial (polynomial A hs p theta)

theorem evaluate_coefficientArray {s m : ℕ} (A : AutomatonWords.Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (theta : ℝ) (w : Fin (numberOfBodies s m) → ℝ) :
    evaluate (coefficientArray A hs p theta) w =
      MvPolynomial.eval (w ∘ labelEquiv s m)
        (targetPolynomial A hs (targetDelta A p theta)) := by
  rw [coefficientArray,evaluate_eq_polynomial_eval,
    coefficientPolynomial_coefficientsOfPolynomial _ (polynomial_homogeneous A hs p theta),
    polynomial,MvPolynomial.eval_rename]

/-- The block-numbered array retains exactly the same arbitrary-body
realization condition; no geometric hypothesis is introduced by numbering. -/
theorem coefficientArray_mem_iff {s m : ℕ} (A : AutomatonWords.Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (theta : ℝ) :
    coefficientArray A hs p theta ∈ VolumeLocus (numberOfBodies s m) 3 ↔
      GeneralLocus.coefficientArray A hs p theta ∈ VolumeLocus (numberOfBodies s m) 3 := by
  rw [GeneralLocus.coefficientArray_mem_iff_target,mem_volumeLocus]
  constructor
  · rintro ⟨K,hK⟩
    refine ⟨K ∘ labelEquiv s m,?_⟩
    intro w hw
    have h := hK (w ∘ (labelEquiv s m).symm) (fun i => hw _)
    rw [evaluate_coefficientArray] at h
    have hf : (w ∘ (labelEquiv s m).symm) ∘ labelEquiv s m = w := by ext i; simp
    rw [hf] at h
    rw [h]
    change bodyVolume (sumBody K (w ∘ (labelEquiv s m).symm)) = _
    congr 1
    have hr := GeneralLocus.sumBody_reindex (labelEquiv s m) K
      (w ∘ (labelEquiv s m).symm)
    rw [hf] at hr
    exact hr.symm
  · rintro ⟨K,hK⟩
    refine ⟨K ∘ (labelEquiv s m).symm,?_⟩
    intro w hw
    rw [evaluate_coefficientArray,hK (w ∘ labelEquiv s m) (fun i => hw _)]
    change bodyVolume (sumBody K (w ∘ labelEquiv s m)) =
      bodyVolume (sumBody (K ∘ (labelEquiv s m).symm) w)
    congr 1
    have hr := GeneralLocus.sumBody_reindex (labelEquiv s m).symm K
      (w ∘ labelEquiv s m)
    simpa [Function.comp_def] using hr.symm

end MixedVolume.ExplicitLabels

end
end
end -- component scope
/- END SOURCE: MixedVolume/General/ExplicitLabels.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/PrimitiveFunProp.lean -/
section


/-! Ordinary proof-producing automation for represented rational programs.
The registered closure rules all exhibit actual primitive-recursive programs.
The tactic is only an elaborator: its output is checked by the Lean kernel. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MixedVolume.Represented

/-- A named bounded quantifier, so the standard function-property tactic can
recognize its checked closure rule without treating a binder as a function. -/
def AllMem {β : Type} (l : List β) (p : β → Prop) : Prop := ∀ y ∈ l, p y

instance {β : Type} (l : List β) (p : β → Prop) [DecidablePred p] :
    Decidable (AllMem l p) := inferInstanceAs (Decidable (∀ y ∈ l, p y))

namespace Primitive

variable {α : Type} [Representation α]

theorem nat_div {f g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x / g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => Nat.div (F c) (G c),Primrec.nat_div.comp hF hG,
    fun c => by
      change Nat.div (F c) (G c) = f (decode c) / g (decode c)
      rw [←heF c,←heG c] <;> rfl⟩

theorem nat_mod {f g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x % g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => Nat.mod (F c) (G c),Primrec.nat_mod.comp hF hG,
    fun c => by
      change Nat.mod (F c) (G c) = f (decode c) % g (decode c)
      rw [←heF c,←heG c] <;> rfl⟩

theorem nat_pow {f g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x ^ g x) := by
  have h := nat_rec hg (const (1 : ℕ))
    ((snd.comp snd).nat_mul (hf.comp fst))
  refine h.of_eq (fun x => ?_)
  induction g x with
  | zero => rfl
  | succ n ih =>
      simpa only [Nat.rec_add_one,pow_succ] using congrArg (fun z => z * f x) ih

theorem list_foldl {β γ : Type} [Representation β] [Representation γ]
    {f : α → List β} {g : α → γ} {h : α × (γ × β) → γ}
    (hf : Primitive f) (hg : Primitive g) (hh : Primitive h) :
    Primitive (fun x => (f x).foldl (fun c b => h (x,(c,b))) (g x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  obtain ⟨H,hH,heH⟩ := hh
  refine ⟨fun c => (F c).foldl (fun d b => H (c,(d,b))) (G c),
    Primrec.list_foldl (h := fun c p => H (c,p)) hF hG (Primrec₂.mk hH),?_⟩
  intro c
  have aux (l : List (Code β)) (z : Code γ) :
      decode (l.foldl (fun d b => H (c,(d,b))) z) =
        (l.map decode).foldl (fun d b => h (decode c,(d,b))) (decode z) := by
    induction l generalizing z with
    | nil => rfl
    | cons b l ih =>
      simp only [List.foldl_cons,List.map_cons,ih,heH] <;> rfl
  change decode ((F c).foldl (fun d b => H (c,(d,b))) (G c)) =
    (f (decode c)).foldl (fun d b => h (decode c,(d,b))) (g (decode c))
  rw [←heF c,←heG c]
  exact aux (F c) (G c)

/- The curried facades present callback metavariables in higher-order pattern
form to the ordinary elaborator. Their proofs are the exact tuple-code rules
above; no function-space representation is introduced. -/

theorem list_map_curried {β γ : Type} [Representation β] [Representation γ]
    {f : α → List β} {g : α → β → γ}
    (hf : Primitive f) (hg : Primitive (fun p : α × β => g p.1 p.2)) :
    Primitive (fun x => (f x).map (g x)) :=
  list_map (g := fun p => g p.1 p.2) hf hg

theorem list_flatMap_curried {β γ : Type} [Representation β] [Representation γ]
    {f : α → List β} {g : α → β → List γ}
    (hf : Primitive f) (hg : Primitive (fun p : α × β => g p.1 p.2)) :
    Primitive (fun x => (f x).flatMap (g x)) :=
  list_flatMap (g := fun p => g p.1 p.2) hf hg

theorem list_filter_curried {β : Type} [Representation β]
    {f : α → List β} {p : α → β → Prop} [∀ x, DecidablePred (p x)]
    (hf : Primitive f) (hp : PrimitivePred (fun q : α × β => p q.1 q.2)) :
    Primitive (fun x => (f x).filter (fun y => p x y)) :=
  list_filter (p := fun q => p q.1 q.2) hf hp

theorem list_foldr_curried {β γ : Type} [Representation β] [Representation γ]
    {f : α → List β} {g : α → γ} {h : α → β → γ → γ}
    (hf : Primitive f) (hg : Primitive g)
    (hh : Primitive (fun p : α × (β × γ) => h p.1 p.2.1 p.2.2)) :
    Primitive (fun x => (f x).foldr (h x) (g x)) :=
  list_foldr (h := fun p => h p.1 p.2.1 p.2.2) hf hg hh

theorem list_foldl_curried {β γ : Type} [Representation β] [Representation γ]
    {f : α → List β} {g : α → γ} {h : α → γ → β → γ}
    (hf : Primitive f) (hg : Primitive g)
    (hh : Primitive (fun p : α × (γ × β) => h p.1 p.2.1 p.2.2)) :
    Primitive (fun x => (f x).foldl (h x) (g x)) :=
  list_foldl (h := fun p => h p.1 p.2.1 p.2.2) hf hg hh

end Primitive

namespace PrimitivePred

variable {α : Type} [Representation α]

theorem const (p : Prop) : PrimitivePred (fun _ : α => p) := by
  classical
  exact (Primrec.const (α := Code α) (decide p)).primrecPred

theorem nat_eq {f g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    PrimitivePred (fun x => f x = g x) :=
  ((nat_le hf hg).and (nat_le hg hf)).of_eq fun _ => le_antisymm_iff.symm

theorem allMem {β : Type} [Representation β] {p : α × β → Prop}
    {f : α → List β} (hp : PrimitivePred p) (hf : Primitive f) :
    PrimitivePred (fun x => AllMem (f x) (fun y => p (x,y))) :=
  forall_mem hp hf

theorem allMem_curried {β : Type} [Representation β] {p : α → β → Prop}
    {f : α → List β} (hp : PrimitivePred (fun q : α × β => p q.1 q.2))
    (hf : Primitive f) : PrimitivePred (fun x => AllMem (f x) (p x)) :=
  forall_mem (p := fun q => p q.1 q.2) hp hf

end PrimitivePred

attribute [fun_prop] Primitive PrimitivePred
attribute [fun_prop] Primitive.id Primitive.const Primitive.fst Primitive.snd
  Primitive.comp Primitive.pair Primitive.nat Primitive.add Primitive.mul
  Primitive.neg Primitive.inv Primitive.abs Primitive.sub Primitive.div
  Primitive.pow_nat Primitive.nat_add Primitive.nat_sub Primitive.nat_mul
  Primitive.nat_div Primitive.nat_mod Primitive.nat_pow
  Primitive.ite Primitive.list_cons Primitive.list_append Primitive.list_length
  Primitive.list_range Primitive.list_getD Primitive.list_map_curried
  Primitive.list_foldr_curried Primitive.list_foldl_curried
  Primitive.list_flatMap_curried Primitive.list_filter_curried Primitive.list_sum Primitive.list_prod
attribute [fun_prop] PrimitivePred.const PrimitivePred.comp PrimitivePred.not
  PrimitivePred.and PrimitivePred.or
  PrimitivePred.nat_le PrimitivePred.nat_lt PrimitivePred.nat_eq
  PrimitivePred.le PrimitivePred.lt PrimitivePred.eq PrimitivePred.allMem_curried

end MixedVolume.Represented

end -- public section
end -- component scope
/- END SOURCE: MixedVolume/Computability/PrimitiveFunProp.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/CertificateSearch.lean -/
section


/-! Uniform partial recursive search for exact finite rational certificates.
The search is one program over the complete input code.  Its termination
criterion is exactly the existence of a certificate, not a bound on any
dimension or on any denominator. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MixedVolume.CertificateSearch

open Represented

variable {α β : Type} [Representation α] [Representation β]

def candidate (P : α × β → Prop) [DecidablePred P]
    (c : Code α) (n : ℕ) : Option (Code β) :=
  match Encodable.decode n with
  | none => none
  | some d => if P (decode c,decode d) then some d else none

def program (P : α × β → Prop) [DecidablePred P] (c : Code α) : Part (Code β) :=
  Nat.rfindOpt (candidate P c)

set_option maxHeartbeats 800000 in
theorem candidate_computable (P : α × β → Prop) [DecidablePred P]
    (hP : EffectivePred P) : Computable₂ (candidate P) := by
  change ComputablePred (fun q : Code α × Code β =>
    P (decode q.1,decode q.2)) at hP
  have hprojection : Computable
      (fun p : (Code α × ℕ) × Code β => (p.1.1,p.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have htest : Computable (fun p : (Code α × ℕ) × Code β =>
      decide (P (decode p.1.1,decode p.2))) := hP.decide.comp hprojection
  have hc : Computable (fun p : Code α × ℕ =>
    Option.casesOn (motive := fun _ => Option (Code β))
      (Encodable.decode (α := Code β) p.2) none
      (fun d => if P (decode p.1,decode d) then some d else none)) := by
    apply Computable.option_casesOn
      (α := Code α × ℕ) (β := Code β) (σ := Option (Code β))
      (g := fun p d => if P (decode p.1,decode d) then some d else none)
      (Computable.decode.comp Computable.snd) (Computable.const none)
    have h : Computable (fun p : (Code α × ℕ) × Code β =>
        cond (decide (P (decode p.1.1,decode p.2))) (some p.2) none) :=
      Computable.cond
        htest
        (Computable.option_some.comp Computable.snd) (Computable.const none)
    simpa only [Bool.cond_decide] using h.to₂
  change Computable (fun p : Code α × ℕ => candidate P p.1 p.2)
  apply hc.of_eq
  intro p
  cases he : Encodable.decode (α := Code β) p.2 <;> simp [candidate,he]

theorem program_partrec (P : α × β → Prop) [DecidablePred P]
    (hP : EffectivePred P) : Partrec (program P) :=
  Partrec.rfindOpt (candidate_computable P hP)

theorem candidate_spec (P : α × β → Prop) [DecidablePred P]
    (c : Code α) (n : ℕ) (d : Code β) (hd : d ∈ candidate P c n) :
    P (decode c,decode d) := by
  cases he : Encodable.decode (α := Code β) n with
  | none => simp [candidate,he] at hd
  | some e =>
    by_cases h : P (decode c,decode e)
    · have hd' : e = d := by simpa [candidate,he,h] using hd
      simpa only [hd'] using h
    · simp [candidate,he,h] at hd

theorem program_spec (P : α × β → Prop) [DecidablePred P]
    (c : Code α) (d : Code β) (hd : d ∈ program P c) :
    P (decode c,decode d) := by
  obtain ⟨n,hn⟩ := Nat.rfindOpt_spec hd
  exact candidate_spec P c n d hn

theorem program_dom (P : α × β → Prop) [DecidablePred P] (c : Code α) :
    (program P c).Dom ↔ ∃ b, P (decode c,b) := by
  rw [program,Nat.rfindOpt_dom]
  constructor
  · rintro ⟨n,d,hd⟩
    exact ⟨decode d,candidate_spec P c n d hd⟩
  · rintro ⟨b,hb⟩
    obtain ⟨d,hd⟩ := Representation.onto b
    refine ⟨Encodable.encode d,d,?_⟩
    simp [candidate,Encodable.encodek,hd,hb]

/-- A computable readout may be attached to the selected witness.  The
resulting partial recursive program still terminates exactly when a witness
exists, because the readout is total. -/
theorem readout_partrec (P : α × β → Prop) [DecidablePred P]
    (hP : EffectivePred P) {γ : Type} [Primcodable γ]
    (readout : Code α → Code β → γ) (hread : Computable₂ readout) :
    Partrec (fun c => (program P c).map (readout c)) :=
  (program_partrec P hP).map hread

end MixedVolume.CertificateSearch

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/CertificateSearch.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/UniformLinearSystems.lean -/
section


/-! Exact, dimension-uniform verification of rational fixed-point systems.
All dimensions and all matrix entries are ordinary input data. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.UniformLinearSystems

open Represented Represented.Primitive
open scoped BigOperators

def rangeSum (n : ℕ) (f : ℕ → ℚ) : ℚ := ((List.range n).map f).sum

theorem rangeSum_eq (n : ℕ) (f : ℕ → ℚ) :
    rangeSum n f = ∑ i : Fin n, f i :=
  Primitive.range_sum_eq_fin_sum n f

@[simp] theorem getD_ofFn {n : ℕ} {α : Type} (f : Fin n → α) (i : Fin n) (a : α) :
    (List.ofFn f).getD i.val a = f i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]

abbrev System := ℕ × (List (List ℚ) × List ℚ)

def matrixEntry (M : List (List ℚ)) (i j : ℕ) : ℚ := (M.getD i []).getD j 0

def rhs (S : System) (x : List ℚ) (i : ℕ) : ℚ :=
  S.2.2.getD i 0 + rangeSum S.1 (fun j => matrixEntry S.2.1 i j * x.getD j 0)

def Solves (S : System) (x : List ℚ) : Prop :=
  ∀ i ∈ List.range S.1, x.getD i 0 = rhs S x i

instance (S : System) (x : List ℚ) : Decidable (Solves S x) :=
  inferInstanceAs (Decidable (∀ i ∈ List.range S.1, x.getD i 0 = rhs S x i))

theorem matrixEntry_primitive :
    Primitive (fun p : List (List ℚ) × (ℕ × ℕ) => matrixEntry p.1 p.2.1 p.2.2) :=
  Primitive.list_getD 0
    (Primitive.list_getD [] Primitive.fst (Primitive.fst.comp Primitive.snd))
    (Primitive.snd.comp Primitive.snd)

theorem rhs_primitive :
    Primitive (fun p : (System × List ℚ) × ℕ => rhs p.1.1 p.1.2 p.2) := by
  have hS : Primitive (fun p : (System × List ℚ) × ℕ => p.1.1) := fst.comp fst
  have hx : Primitive (fun p : (System × List ℚ) × ℕ => p.1.2) := snd.comp fst
  have hi : Primitive (fun p : (System × List ℚ) × ℕ => p.2) := snd
  have hb := list_getD 0 ((snd.comp snd).comp hS) hi
  have hm := (fst.comp snd).comp hS
  have hn := fst.comp hS
  exact hb.add (range_sum
    ((matrixEntry_primitive.comp ((hm.comp fst).pair ((hi.comp fst).pair snd))).mul
      (list_getD 0 (hx.comp fst) snd)) hn)

theorem solves_primitive : PrimitivePred (fun p : System × List ℚ => Solves p.1 p.2) := by
  apply PrimitivePred.forall_mem
    (PrimitivePred.eq (Primitive.list_getD 0 (Primitive.snd.comp Primitive.fst)
      Primitive.snd) rhs_primitive)
    (Primitive.list_range (Primitive.fst.comp Primitive.fst))

def vector (n : ℕ) (x : List ℚ) : Fin n → ℚ := fun i => x.getD i.val 0

open scoped Matrix

def matrix (n : ℕ) (M : List (List ℚ)) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => matrixEntry M i.val j.val

theorem solves_iff (S : System) (x : List ℚ) :
    Solves S x ↔ vector S.1 x = vector S.1 S.2.2 + matrix S.1 S.2.1 *ᵥ vector S.1 x := by
  constructor
  · intro h
    funext i
    have hi := h i.val (List.mem_range.mpr i.isLt)
    simpa only [rhs,rangeSum_eq,vector,matrix,Matrix.mulVec,dotProduct,
      Pi.add_apply] using hi
  · intro h i hi
    have h' := congrFun h ⟨i,List.mem_range.mp hi⟩
    simpa only [rhs,rangeSum_eq,vector,matrix,Matrix.mulVec,dotProduct,
      Pi.add_apply] using h'

def encode {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) : System :=
  (n,(List.ofFn (fun i => List.ofFn (M i)),List.ofFn b))

@[simp] theorem matrix_encode {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    matrix n (List.ofFn (fun i => List.ofFn (M i))) = M := by
  funext i j
  simp [matrix,matrixEntry]

@[simp] theorem vector_encode {n : ℕ} (b : Fin n → ℚ) : vector n (List.ofFn b) = b := by
  funext i
  simp [vector]

theorem solves_encode {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (x : List ℚ) :
    Solves (encode M b) x ↔ vector n x = b + M *ᵥ vector n x := by
  simpa only [encode,matrix_encode,vector_encode] using solves_iff (encode M b) x

/-- A rational certificate for a contractive system has the unique exact
adjugate value already used by the geometric arithmetic construction. -/
theorem fixedpoint_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (b : ι → ℚ) (r : ℝ) (hr : 0 ≤ r) (hr₁ : r < 1)
    (hrow : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ r)
    (x : ι → ℚ) (hx : x = b + M *ᵥ x) :
    x = RationalSystems.rationalSolution M b := by
  apply RationalSystems.castVector_injective
  apply RationalSystems.real_solution_is_rational M b r hr hr₁ hrow
  simpa only [RationalSystems.castVector_add,RationalSystems.cast_mulVec] using
    congrArg RationalSystems.castVector hx

theorem solution_unique {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (r : ℝ) (hr : 0 ≤ r) (hr₁ : r < 1)
    (hrow : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ r) (x : List ℚ)
    (hx : Solves (encode M b) x) :
    vector n x = RationalSystems.rationalSolution M b :=
  fixedpoint_unique M b r hr hr₁ hrow _ ((solves_encode M b x).mp hx)

end MixedVolume.UniformLinearSystems

end
end
end -- component scope
/- END SOURCE: MixedVolume/Computability/UniformLinearSystems.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/UniformMoments.lean -/
section


/-! A single finite rational certificate format for all automaton dimensions.
The four witness blocks are mass, first moment, pair mixed area, and absolute
reference moment.  Their equations are checked by a uniform primitive
recursive predicate; contractivity identifies every accepted witness with
the exact rational moments of the geometric construction. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.UniformMoments

open Represented UniformLinearSystems
open scoped BigOperators

abbrev RawAutomaton := ℕ × (ℕ × (List (List (List ℚ)) × List ℚ))
abbrev MomentWitness := List ℚ × (List ℚ × (List (List ℚ) × List (List ℚ)))

def alphabet (D : RawAutomaton) : ℕ := D.1
def states (D : RawAutomaton) : ℕ := D.2.1
def transition (D : RawAutomaton) (a j k : ℕ) : ℚ :=
  ((D.2.2.1.getD a []).getD j []).getD k 0
def accepting (D : RawAutomaton) (j : ℕ) : ℚ := D.2.2.2.getD j 0
def mass (W : MomentWitness) (j : ℕ) : ℚ := W.1.getD j 0
def first (W : MomentWitness) (j : ℕ) : ℚ := W.2.1.getD j 0
def pair (W : MomentWitness) (j k : ℕ) : ℚ := (W.2.2.1.getD j []).getD k 0
def threshold (W : MomentWitness) (a j : ℕ) : ℚ := (W.2.2.2.getD a []).getD j 0

def rho (D : RawAutomaton) : ℚ := 1 / (4 * (alphabet D : ℚ))
def base (D : RawAutomaton) : ℚ := (alphabet D : ℚ) + 1
def digit (a : ℕ) : ℚ := (a : ℚ) + 1

def massSource (D : RawAutomaton) (j : ℕ) : ℚ := 1 + accepting D j
def massMatrix (D : RawAutomaton) (j k : ℕ) : ℚ :=
  rho D * rangeSum (alphabet D) (fun a => transition D a j k)
def firstMatrix (D : RawAutomaton) (j k : ℕ) : ℚ :=
  rho D / base D * rangeSum (alphabet D) (fun a => transition D a j k)
def firstSource (D : RawAutomaton) (W : MomentWitness) (j : ℕ) : ℚ :=
  rho D / base D * rangeSum (alphabet D) (fun a =>
    rangeSum (states D) (fun k => transition D a j k * digit a * mass W k))

def imageFactor (D : RawAutomaton) : ℚ := rho D ^ 2 / base D
def cross (D : RawAutomaton) (W : MomentWitness) (a b j k : ℕ) : ℚ :=
  if a < b then imageFactor D *
    (((b : ℚ)-(a : ℚ))*mass W j*mass W k + mass W j*first W k - first W j*mass W k)
  else if b < a then imageFactor D *
    (((a : ℚ)-(b : ℚ))*mass W k*mass W j + mass W k*first W j - first W k*mass W j)
  else 0
def areaMatrix (D : RawAutomaton) (j k l r : ℕ) : ℚ :=
  imageFactor D * rangeSum (alphabet D) (fun a => transition D a j l * transition D a k r)
def areaSource (D : RawAutomaton) (W : MomentWitness) (j k : ℕ) : ℚ :=
  (1 + accepting D j) * first W k + rangeSum (alphabet D) (fun a =>
    rangeSum (states D) (fun l => transition D a j l *
      ((1 + accepting D k) * (rho D / base D * (first W l + digit a * mass W l)) +
        rangeSum (alphabet D) (fun b => rangeSum (states D) (fun r =>
          transition D b k r * cross D W a b l r)))))

def headConstant (D : RawAutomaton) (a b : ℕ) : ℚ :=
  base D * digit a - (alphabet D : ℚ) * digit b
def offHead (D : RawAutomaton) (W : MomentWitness) (a b k : ℕ) : ℚ :=
  if b < a then headConstant D a b * mass W k - (alphabet D : ℚ) * first W k
  else if a < b then (alphabet D : ℚ) * first W k - headConstant D a b * mass W k
  else 0
def thresholdMatrix (D : RawAutomaton) (a j k : ℕ) : ℚ :=
  rho D / base D * transition D a j k
def thresholdSource (D : RawAutomaton) (W : MomentWitness) (a j : ℕ) : ℚ :=
  digit a * (1 + accepting D j) + rho D / base D * rangeSum (alphabet D) (fun b =>
    rangeSum (states D) (fun k => transition D b j k * offHead D W a b k))

def Correct (D : RawAutomaton) (W : MomentWitness) : Prop :=
  AllMem (List.range (states D)) (fun j => mass W j = massSource D j +
    rangeSum (states D) (fun k => massMatrix D j k * mass W k)) ∧
  AllMem (List.range (states D)) (fun j => first W j = firstSource D W j +
    rangeSum (states D) (fun k => firstMatrix D j k * first W k)) ∧
  AllMem (List.range (states D)) (fun j => AllMem (List.range (states D)) (fun k =>
    pair W j k = areaSource D W j k +
      rangeSum (states D) (fun l => rangeSum (states D) (fun r => areaMatrix D j k l r * pair W l r)))) ∧
  AllMem (List.range (alphabet D)) (fun a => AllMem (List.range (states D)) (fun j =>
    threshold W a j = thresholdSource D W a j +
      rangeSum (states D) (fun k => thresholdMatrix D a j k * threshold W a k)))

instance (D : RawAutomaton) (W : MomentWitness) : Decidable (Correct D W) := by
  unfold Correct
  infer_instance

@[fun_prop] theorem alphabet_primitive : Primitive alphabet := Primitive.fst
@[fun_prop] theorem states_primitive : Primitive states := Primitive.fst.comp Primitive.snd
@[fun_prop] theorem transition_primitive :
    Primitive (fun p : RawAutomaton × (ℕ × (ℕ × ℕ)) => transition p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold transition
  fun_prop
@[fun_prop] theorem accepting_primitive :
    Primitive (fun p : RawAutomaton × ℕ => accepting p.1 p.2) := by
  unfold accepting
  fun_prop
@[fun_prop] theorem mass_primitive : Primitive (fun p : MomentWitness × ℕ => mass p.1 p.2) := by
  unfold mass
  fun_prop
@[fun_prop] theorem first_primitive : Primitive (fun p : MomentWitness × ℕ => first p.1 p.2) := by
  unfold first
  fun_prop
@[fun_prop] theorem pair_primitive :
    Primitive (fun p : MomentWitness × (ℕ × ℕ) => pair p.1 p.2.1 p.2.2) := by
  unfold pair
  fun_prop
@[fun_prop] theorem threshold_primitive :
    Primitive (fun p : MomentWitness × (ℕ × ℕ) => threshold p.1 p.2.1 p.2.2) := by
  unfold threshold
  fun_prop

theorem correct_primitive : PrimitivePred (fun p : RawAutomaton × MomentWitness => Correct p.1 p.2) := by
  unfold Correct massSource massMatrix firstMatrix firstSource areaMatrix areaSource
    thresholdMatrix thresholdSource cross offHead headConstant imageFactor rho base digit rangeSum
  fun_prop

def encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) : RawAutomaton :=
  (s,(m,(List.ofFn (fun a => List.ofFn (fun j => List.ofFn (A.P a j))),List.ofFn A.f)))

def witness {s m : ℕ} (A : AutomatonMoments.RationalData s m) : MomentWitness :=
  (List.ofFn (AutomatonMoments.massQ A),
    (List.ofFn (AutomatonMoments.firstQ A),
      (List.ofFn (fun j => List.ofFn (fun k => QuadraticMoments.pairMomentQ A (j,k))),
        List.ofFn (fun a => List.ofFn (ReferenceMoments.thresholdMomentQ A a)))))

@[simp] theorem alphabet_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) : alphabet (encode A) = s := rfl
@[simp] theorem states_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) : states (encode A) = m := rfl
@[simp] theorem transition_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m)
    (a : Fin s) (j k : Fin m) : transition (encode A) a j k = A.P a j k := by
  simp [transition,encode]
@[simp] theorem accepting_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m)
    (j : Fin m) : accepting (encode A) j = A.f j := by
  simp [accepting,encode]
@[simp] theorem rho_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) :
    rho (encode A) = AutomatonMoments.rhoQ s := rfl
@[simp] theorem base_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) :
    base (encode A) = AutomatonMoments.baseQ s := rfl
@[simp] theorem mass_witness {s m : ℕ} (A : AutomatonMoments.RationalData s m) (j : Fin m) :
    mass (witness A) j = AutomatonMoments.massQ A j := by simp [mass,witness]
@[simp] theorem first_witness {s m : ℕ} (A : AutomatonMoments.RationalData s m) (j : Fin m) :
    first (witness A) j = AutomatonMoments.firstQ A j := by simp [first,witness]
@[simp] theorem pair_witness {s m : ℕ} (A : AutomatonMoments.RationalData s m) (j k : Fin m) :
    pair (witness A) j k = QuadraticMoments.pairMomentQ A (j,k) := by simp [pair,witness]
@[simp] theorem threshold_witness {s m : ℕ} (A : AutomatonMoments.RationalData s m) (a : Fin s) (j : Fin m) :
    threshold (witness A) a j = ReferenceMoments.thresholdMomentQ A a j := by simp [threshold,witness]

@[simp] theorem massSource_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (j : Fin m) :
    massSource (encode A) j = 1 + A.f j := by simp [massSource]
@[simp] theorem massMatrix_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (j k : Fin m) :
    massMatrix (encode A) j k = AutomatonMoments.massMatrix A j k := by
  simp [massMatrix,AutomatonMoments.massMatrix,rangeSum_eq]
@[simp] theorem firstMatrix_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (j k : Fin m) :
    firstMatrix (encode A) j k = AutomatonMoments.firstMatrix A j k := by
  simp [firstMatrix,AutomatonMoments.firstMatrix,rangeSum_eq]
@[simp] theorem imageFactor_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) :
    imageFactor (encode A) = QuadraticMoments.imageFactorQ s := rfl
@[simp] theorem areaMatrix_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (j k l r : Fin m) :
    areaMatrix (encode A) j k l r = QuadraticMoments.areaMatrix A (j,k) (l,r) := by
  simp [areaMatrix,QuadraticMoments.areaMatrix,rangeSum_eq]
@[simp] theorem headConstant_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (a b : Fin s) :
    headConstant (encode A) a b = ReferenceMoments.headConstantQ a b := rfl
@[simp] theorem thresholdMatrix_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m)
    (a : Fin s) (j k : Fin m) :
    thresholdMatrix (encode A) a j k = ReferenceMoments.thresholdMatrix A a j k := by
  simp [thresholdMatrix,ReferenceMoments.thresholdMatrix]

theorem firstSource_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (W : MomentWitness)
    (hm : ∀ j : Fin m, mass W j = AutomatonMoments.massQ A j) (j : Fin m) :
    firstSource (encode A) W j = AutomatonMoments.firstSourceQ A j := by
  simp [firstSource,AutomatonMoments.firstSourceQ,rangeSum_eq,digit,hm]

theorem cross_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (W : MomentWitness)
    (hm : ∀ j : Fin m, mass W j = AutomatonMoments.massQ A j)
    (hx : ∀ j : Fin m, first W j = AutomatonMoments.firstQ A j)
    (a b : Fin s) (j k : Fin m) :
    cross (encode A) W a b j k = QuadraticMoments.crossMomentQ A a b j k := by
  simp [cross,QuadraticMoments.crossMomentQ,hm,hx]

theorem areaSource_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (W : MomentWitness)
    (hm : ∀ j : Fin m, mass W j = AutomatonMoments.massQ A j)
    (hx : ∀ j : Fin m, first W j = AutomatonMoments.firstQ A j) (j k : Fin m) :
    areaSource (encode A) W j k = QuadraticMoments.areaSourceQ A (j,k) := by
  simp [areaSource,QuadraticMoments.areaSourceQ,rangeSum_eq,digit,hm,hx,cross_encode A W hm hx]

theorem offHead_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (W : MomentWitness)
    (hm : ∀ j : Fin m, mass W j = AutomatonMoments.massQ A j)
    (hx : ∀ j : Fin m, first W j = AutomatonMoments.firstQ A j)
    (a b : Fin s) (k : Fin m) :
    offHead (encode A) W a b k = ReferenceMoments.offHeadMomentQ A a b k := by
  simp [offHead,ReferenceMoments.offHeadMomentQ,hm,hx]

theorem thresholdSource_encode {s m : ℕ} (A : AutomatonMoments.RationalData s m) (W : MomentWitness)
    (hm : ∀ j : Fin m, mass W j = AutomatonMoments.massQ A j)
    (hx : ∀ j : Fin m, first W j = AutomatonMoments.firstQ A j) (a : Fin s) (j : Fin m) :
    thresholdSource (encode A) W a j = ReferenceMoments.thresholdSourceQ A a j := by
  simp [thresholdSource,ReferenceMoments.thresholdSourceQ,ReferenceMoments.digitQ,
    rangeSum_eq,digit,hm,hx,offHead_encode A W hm hx]

open scoped Matrix

theorem mass_eq {s m : ℕ} (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
    (W : MomentWitness) (hW : Correct (encode A) W) (j : Fin m) :
    mass W j = AutomatonMoments.massQ A j := by
  have hfix : (fun j : Fin m => mass W j) =
      (fun j => 1 + A.f j) + AutomatonMoments.massMatrix A *ᵥ (fun j : Fin m => mass W j) := by
    funext k
    simpa only [states_encode,rangeSum_eq,massSource_encode,massMatrix_encode,
      Pi.add_apply,Matrix.mulVec,dotProduct] using hW.1 k.val (List.mem_range.mpr k.isLt)
  have h := UniformLinearSystems.fixedpoint_unique (AutomatonMoments.massMatrix A)
    (fun j => 1 + A.f j) (1/4) (by norm_num) (by norm_num)
    (fun j => (AutomatonMoments.massMatrix_row A hs j).le) _ hfix
  exact congrFun h j

theorem first_eq {s m : ℕ} (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
    (W : MomentWitness) (hW : Correct (encode A) W) (j : Fin m) :
    first W j = AutomatonMoments.firstQ A j := by
  have hm := mass_eq A hs W hW
  have hfix : (fun j : Fin m => first W j) =
      AutomatonMoments.firstSourceQ A + AutomatonMoments.firstMatrix A *ᵥ (fun j : Fin m => first W j) := by
    funext k
    simpa only [states_encode,rangeSum_eq,firstSource_encode A W hm,firstMatrix_encode,
      Pi.add_apply,Matrix.mulVec,dotProduct] using hW.2.1 k.val (List.mem_range.mpr k.isLt)
  have h := UniformLinearSystems.fixedpoint_unique (AutomatonMoments.firstMatrix A)
    (AutomatonMoments.firstSourceQ A) (1/4) (by norm_num) (by norm_num)
    (AutomatonMoments.firstMatrix_row A hs) _ hfix
  exact congrFun h j

theorem pair_eq {s m : ℕ} (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
    (W : MomentWitness) (hW : Correct (encode A) W) (j k : Fin m) :
    pair W j k = QuadraticMoments.pairMomentQ A (j,k) := by
  have hm := mass_eq A hs W hW
  have hx := first_eq A hs W hW
  have hfix : (fun p : Fin m × Fin m => pair W p.1 p.2) =
      QuadraticMoments.areaSourceQ A + QuadraticMoments.areaMatrix A *ᵥ
        (fun p : Fin m × Fin m => pair W p.1 p.2) := by
    funext p
    simpa only [states_encode,rangeSum_eq,areaSource_encode A W hm hx,areaMatrix_encode,
      Pi.add_apply,Matrix.mulVec,dotProduct,Fintype.sum_prod_type] using
      hW.2.2.1 p.1.val (List.mem_range.mpr p.1.isLt) p.2.val (List.mem_range.mpr p.2.isLt)
  have h := UniformLinearSystems.fixedpoint_unique (QuadraticMoments.areaMatrix A)
    (QuadraticMoments.areaSourceQ A) (1/4) (by norm_num) (by norm_num)
    (QuadraticMoments.areaMatrix_row A hs) _ hfix
  exact congrFun h (j,k)

theorem threshold_eq {s m : ℕ} (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
    (W : MomentWitness) (hW : Correct (encode A) W) (a : Fin s) (j : Fin m) :
    threshold W a j = ReferenceMoments.thresholdMomentQ A a j := by
  have hm := mass_eq A hs W hW
  have hx := first_eq A hs W hW
  have hfix : (fun j : Fin m => threshold W a j) =
      ReferenceMoments.thresholdSourceQ A a + ReferenceMoments.thresholdMatrix A a *ᵥ
        (fun j : Fin m => threshold W a j) := by
    funext k
    simpa only [states_encode,rangeSum_eq,thresholdSource_encode A W hm hx,thresholdMatrix_encode,
      Pi.add_apply,Matrix.mulVec,dotProduct] using
      hW.2.2.2 a.val (List.mem_range.mpr a.isLt) k.val (List.mem_range.mpr k.isLt)
  have h := UniformLinearSystems.fixedpoint_unique (ReferenceMoments.thresholdMatrix A a)
    (ReferenceMoments.thresholdSourceQ A a) (1/4) (by norm_num) (by norm_num)
    (ReferenceMoments.thresholdMatrix_row A hs a) _ hfix
  exact congrFun h j

private theorem resolvent_recurrence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (b : ι → ℚ)
    (hrow : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ 1/4) :
    RationalSystems.rationalSolution M b = b + M *ᵥ RationalSystems.rationalSolution M b :=
  RationalSystems.rationalSolution_eq M b
    (RationalSystems.rational_det_ne_zero M (1/4) (by norm_num) (by norm_num) hrow)

theorem canonical_correct {s m : ℕ} (A : AutomatonMoments.RationalData s m) (hs : 0 < s) :
    Correct (encode A) (witness A) := by
  have hm : ∀ j : Fin m, mass (witness A) j = AutomatonMoments.massQ A j := mass_witness A
  have hx : ∀ j : Fin m, first (witness A) j = AutomatonMoments.firstQ A j := first_witness A
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj
    let i : Fin m := ⟨j,List.mem_range.mp hj⟩
    change mass (witness A) i = massSource (encode A) i +
      rangeSum m (fun k => massMatrix (encode A) i k * mass (witness A) k)
    have h := congrFun (resolvent_recurrence (AutomatonMoments.massMatrix A)
      (fun j => 1+A.f j) (fun j => (AutomatonMoments.massMatrix_row A hs j).le)) i
    simpa only [states_encode,rangeSum_eq,massSource_encode,massMatrix_encode,mass_witness,
      AutomatonMoments.massQ,Pi.add_apply,Matrix.mulVec,dotProduct] using h
  · intro j hj
    let i : Fin m := ⟨j,List.mem_range.mp hj⟩
    change first (witness A) i = firstSource (encode A) (witness A) i +
      rangeSum m (fun k => firstMatrix (encode A) i k * first (witness A) k)
    have h := congrFun (resolvent_recurrence (AutomatonMoments.firstMatrix A)
      (AutomatonMoments.firstSourceQ A) (AutomatonMoments.firstMatrix_row A hs)) i
    simpa only [states_encode,rangeSum_eq,firstSource_encode A (witness A) hm,firstMatrix_encode,
      first_witness,AutomatonMoments.firstQ,Pi.add_apply,Matrix.mulVec,dotProduct] using h
  · intro j hj k hk
    let i : Fin m := ⟨j,List.mem_range.mp hj⟩
    let l : Fin m := ⟨k,List.mem_range.mp hk⟩
    change pair (witness A) i l = areaSource (encode A) (witness A) i l +
      rangeSum m (fun q => rangeSum m (fun r => areaMatrix (encode A) i l q r * pair (witness A) q r))
    have h := congrFun (resolvent_recurrence (QuadraticMoments.areaMatrix A)
      (QuadraticMoments.areaSourceQ A) (QuadraticMoments.areaMatrix_row A hs)) (i,l)
    simpa only [states_encode,rangeSum_eq,areaSource_encode A (witness A) hm hx,areaMatrix_encode,
      pair_witness,QuadraticMoments.pairMomentQ,Pi.add_apply,Matrix.mulVec,dotProduct,
      Fintype.sum_prod_type] using h
  · intro a ha j hj
    let b : Fin s := ⟨a,List.mem_range.mp ha⟩
    let i : Fin m := ⟨j,List.mem_range.mp hj⟩
    change threshold (witness A) b i = thresholdSource (encode A) (witness A) b i +
      rangeSum m (fun k => thresholdMatrix (encode A) b i k * threshold (witness A) b k)
    have h := congrFun (resolvent_recurrence (ReferenceMoments.thresholdMatrix A b)
      (ReferenceMoments.thresholdSourceQ A b) (ReferenceMoments.thresholdMatrix_row A hs b)) i
    simpa only [states_encode,rangeSum_eq,thresholdSource_encode A (witness A) hm hx,thresholdMatrix_encode,
      threshold_witness,ReferenceMoments.thresholdMomentQ,Pi.add_apply,Matrix.mulVec,dotProduct] using h

def program : Code RawAutomaton → Part (Code MomentWitness) :=
  CertificateSearch.program (fun p : RawAutomaton × MomentWitness => Correct p.1 p.2)

theorem program_partrec : Partrec program :=
  CertificateSearch.program_partrec _ correct_primitive.effective

theorem program_spec (c : Code RawAutomaton) (d : Code MomentWitness) (hd : d ∈ program c) :
    Correct (decode c) (decode d) := CertificateSearch.program_spec _ c d hd

/-- The same partial recursive program terminates on every encoded rational
stochastic automaton, independently of the alphabet and state dimensions. -/
theorem program_terminates {s m : ℕ} (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
    (c : Code RawAutomaton) (hc : decode c = encode A) : (program c).Dom := by
  apply (CertificateSearch.program_dom _ c).mpr
  rw [hc]
  exact ⟨witness A,canonical_correct A hs⟩

end MixedVolume.UniformMoments

end
end
end -- component scope
/- END SOURCE: MixedVolume/Computability/UniformMoments.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/UniformFormulaData.lean -/
section


/-! The complete rational volume evaluator, with both dimensions as inputs.

All variable-sized vectors and matrices are finite lists. The formulas use
only exact rational arithmetic, natural indices, finite maps, and a finite
fold. A separate correctness module identifies these registers with the
geometric volume, projected areas, and widths of the canonical construction.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MixedVolume.UniformFormula

open Represented UniformMoments UniformLinearSystems

abbrev Vec3 := ℚ × (ℚ × ℚ)
abbrev RawStats := ℚ × (List ℚ × List (List ℚ))
abbrev Input := RawAutomaton × (MomentWitness × List ℚ)

def referenceCount (D : RawAutomaton) : ℕ := alphabet D + 4
def primitiveCount (D : RawAutomaton) : ℕ := states D + alphabet D * states D
def bodyCount (D : RawAutomaton) : ℕ := referenceCount D + primitiveCount D + 1

def get (l : List ℚ) (i : ℕ) : ℚ := l.getD i 0
def imageLetter (D : RawAutomaton) (i : ℕ) : ℕ := (i - states D) / states D
def imageState (D : RawAutomaton) (i : ℕ) : ℕ := (i - states D) % states D

def imageWidth (D : RawAutomaton) (W : MomentWitness) (a j : ℕ) : ℚ :=
  rho D / base D * (first W j + digit a * mass W j)

def imageMixed (D : RawAutomaton) (W : MomentWitness) (a b j k : ℕ) : ℚ :=
  (if a = b then imageFactor D * pair W j k else 0) + cross D W a b j k

def stateImage (D : RawAutomaton) (W : MomentWitness) (j a k : ℕ) : ℚ :=
  (1 + accepting D j) * imageWidth D W a k +
    rangeSum (alphabet D) (fun b => rangeSum (states D) (fun l =>
      transition D b j l * imageMixed D W b a l k))

def primitiveHeight (D : RawAutomaton) (W : MomentWitness) (i : ℕ) : ℚ :=
  if i < states D then mass W i else rho D * mass W (imageState D i)

def primitiveWidth (D : RawAutomaton) (W : MomentWitness) (i : ℕ) : ℚ :=
  if i < states D then first W i else imageWidth D W (imageLetter D i) (imageState D i)

def primitiveMixed (D : RawAutomaton) (W : MomentWitness) (i j : ℕ) : ℚ :=
  if i < states D then
    if j < states D then pair W i j
    else stateImage D W i (imageLetter D j) (imageState D j)
  else if j < states D then stateImage D W j (imageLetter D i) (imageState D i)
  else imageMixed D W (imageLetter D i) (imageLetter D j) (imageState D i) (imageState D j)

def linearHeight (D : RawAutomaton) (W : MomentWitness) (b : List ℚ) : ℚ :=
  rangeSum (primitiveCount D) (fun i => get b i * primitiveHeight D W i)

def linearWidth (D : RawAutomaton) (W : MomentWitness) (b : List ℚ) : ℚ :=
  rangeSum (primitiveCount D) (fun i => get b i * primitiveWidth D W i)

def area (D : RawAutomaton) (W : MomentWitness) (b : List ℚ) : ℚ :=
  (1/2 : ℚ) * rangeSum (primitiveCount D) (fun i =>
    rangeSum (primitiveCount D) (fun j => get b i * get b j * primitiveMixed D W i j))

def stateWeight (D : RawAutomaton) (w : List ℚ) (j : ℕ) : ℚ :=
  get w (referenceCount D + j)

def imageWeight (D : RawAutomaton) (w : List ℚ) (a j : ℕ) : ℚ :=
  get w (referenceCount D + (states D + (j + states D * a)))

def stateWeights (D : RawAutomaton) (w : List ℚ) : List ℚ :=
  (List.range (primitiveCount D)).map (fun i =>
    if i < states D then stateWeight D w i else 0)

def imageWeights (D : RawAutomaton) (w : List ℚ) : List ℚ :=
  (List.range (primitiveCount D)).map (fun i =>
    if i < states D then 0 else imageWeight D w (imageLetter D i) (imageState D i))

def totalWeights (D : RawAutomaton) (w : List ℚ) : List ℚ :=
  (List.range (primitiveCount D)).map (fun i =>
    if i < states D then stateWeight D w i
    else imageWeight D w (imageLetter D i) (imageState D i))

def letterWeights (D : RawAutomaton) (w : List ℚ) (a : ℕ) : List ℚ :=
  (List.range (primitiveCount D)).map (fun i =>
    if i < states D then 0 else
      imageWeight D w (imageLetter D i) (imageState D i) +
        if imageLetter D i = a then base D / rho D * stateWeight D w (imageState D i) else 0)

def direction (s r : ℕ) : Vec3 :=
  if r = 0 then (1,(0,0)) else
  if r = 1 then (0,(1,0)) else
  if r = 2 then (0,(0,1)) else
  if r < s + 3 then (-((r-3 : ℕ) : ℚ)-1,(-((s : ℚ)+1),1)) else (0,(-1,1))

def determinant (u v x : Vec3) : ℚ :=
  u.1 * (v.2.1*x.2.2-v.2.2*x.2.1) -
  u.2.1 * (v.1*x.2.2-v.2.2*x.1) +
  u.2.2 * (v.1*x.2.1-v.2.1*x.1)

def triple (s i j k : ℕ) : ℚ :=
  |determinant (direction s i) (direction s j) (direction s k)|

def statePoint (W : MomentWitness) (k : ℕ) : Vec3 := (first W k,(0,mass W k))
def imagePoint (D : RawAutomaton) (W : MomentWitness) (a k : ℕ) : Vec3 :=
  (imageWidth D W a k,(rho D * mass W k,0))

def IsLetter (s r : ℕ) : Prop := 3 ≤ r ∧ r < s + 3
instance (s r : ℕ) : Decidable (IsLetter s r) := inferInstanceAs (Decidable (_ ∧ _))

def head (D : RawAutomaton) (W : MomentWitness) (a b k : ℕ) : ℚ :=
  if b = a then threshold W a k else offHead D W a b k

def statePair (D : RawAutomaton) (W : MomentWitness) (k i j : ℕ) : ℚ :=
  if IsLetter (alphabet D) i ∧ j = alphabet D + 3 then threshold W (i-3) k
  else if i = alphabet D + 3 ∧ IsLetter (alphabet D) j then threshold W (j-3) k
  else |determinant (direction (alphabet D) i) (direction (alphabet D) j) (statePoint W k)|

def imagePair (D : RawAutomaton) (W : MomentWitness) (b k i j : ℕ) : ℚ :=
  if IsLetter (alphabet D) i ∧ j = alphabet D + 3 then rho D / base D * head D W (i-3) b k
  else if i = alphabet D + 3 ∧ IsLetter (alphabet D) j then rho D / base D * head D W (j-3) b k
  else |determinant (direction (alphabet D) i) (direction (alphabet D) j) (imagePoint D W b k)|

def initialVolume (D : RawAutomaton) (W : MomentWitness) (w : List ℚ) : ℚ :=
  area D W (stateWeights D w) * linearHeight D W (imageWeights D w) +
    linearHeight D W (stateWeights D w) * area D W (imageWeights D w)

def initialArea (D : RawAutomaton) (W : MomentWitness) (w : List ℚ) (r : ℕ) : ℚ :=
  if r = 0 then linearHeight D W (stateWeights D w) * linearHeight D W (imageWeights D w)
  else if r = 1 then area D W (stateWeights D w) +
    linearWidth D W (imageWeights D w) * linearHeight D W (stateWeights D w)
  else if r = 2 then area D W (imageWeights D w) +
    linearWidth D W (stateWeights D w) * linearHeight D W (imageWeights D w)
  else if r < alphabet D + 3 then area D W (letterWeights D w (r-3))
  else area D W (totalWeights D w)

def initialWidth (D : RawAutomaton) (W : MomentWitness) (w : List ℚ) (i j : ℕ) : ℚ :=
  rangeSum (states D) (fun k => stateWeight D w k * statePair D W k i j) +
    rangeSum (alphabet D) (fun a => rangeSum (states D) (fun k =>
      imageWeight D w a k * imagePair D W a k i j))

def initialStats (D : RawAutomaton) (W : MomentWitness) (w : List ℚ) : RawStats :=
  (initialVolume D W w,
    ((List.range (referenceCount D)).map (initialArea D W w),
      (List.range (referenceCount D)).map (fun i =>
        (List.range (referenceCount D)).map (initialWidth D W w i))))

def statsArea (z : RawStats) (i : ℕ) : ℚ := z.2.1.getD i 0
def statsWidth (z : RawStats) (i j : ℕ) : ℚ := (z.2.2.getD i []).getD j 0

def step (s : ℕ) (w : List ℚ) (j : ℕ) (z : RawStats) : RawStats :=
  (z.1 + get w j * statsArea z j,
    ((List.range (s+4)).map (fun i => statsArea z i + get w j * statsWidth z j i),
      (List.range (s+4)).map (fun i => (List.range (s+4)).map (fun k =>
        statsWidth z i k + get w j * triple s i k j))))

def references (s : ℕ) : List ℕ :=
  List.range 3 ++ (List.range s).map (fun a => 3+a) ++ [3+s]

def formula (D : RawAutomaton) (W : MomentWitness) (w : List ℚ) : ℚ :=
  ((references (alphabet D)).foldl (fun z j => step (alphabet D) w j z)
    (initialStats D W w)).1

/-! The following proof registers use fixed finite product types only. All
list lengths, summation ranges and dimensions remain part of the input. -/

@[fun_prop] theorem get_primitive : Primitive (fun p : List ℚ × ℕ => get p.1 p.2) := by
  unfold get
  fun_prop

@[fun_prop] theorem referenceCount_primitive : Primitive referenceCount := by
  unfold referenceCount
  fun_prop
@[fun_prop] theorem primitiveCount_primitive : Primitive primitiveCount := by
  unfold primitiveCount
  fun_prop
@[fun_prop] theorem bodyCount_primitive : Primitive bodyCount := by
  unfold bodyCount
  fun_prop

@[fun_prop] theorem imageLetter_primitive :
    Primitive (fun p : RawAutomaton × ℕ => imageLetter p.1 p.2) := by
  unfold imageLetter
  fun_prop
@[fun_prop] theorem imageState_primitive :
    Primitive (fun p : RawAutomaton × ℕ => imageState p.1 p.2) := by
  unfold imageState
  fun_prop

@[fun_prop] theorem imageWidth_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (ℕ × ℕ)) =>
      imageWidth p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold imageWidth rho base digit
  fun_prop

@[fun_prop] theorem imageMixed_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (ℕ × (ℕ × (ℕ × ℕ)))) =>
      imageMixed p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold imageMixed cross imageFactor rho base
  fun_prop

@[fun_prop] theorem stateImage_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (ℕ × (ℕ × ℕ))) =>
      stateImage p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold stateImage rangeSum
  fun_prop

@[fun_prop] theorem primitiveHeight_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × ℕ) =>
      primitiveHeight p.1 p.2.1 p.2.2) := by
  unfold primitiveHeight rho
  fun_prop
@[fun_prop] theorem primitiveWidth_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × ℕ) =>
      primitiveWidth p.1 p.2.1 p.2.2) := by
  unfold primitiveWidth
  fun_prop
@[fun_prop] theorem primitiveMixed_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (ℕ × ℕ)) =>
      primitiveMixed p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold primitiveMixed
  fun_prop

@[fun_prop] theorem linearHeight_primitive :
    Primitive (fun p : Input => linearHeight p.1 p.2.1 p.2.2) := by
  unfold linearHeight rangeSum
  fun_prop
@[fun_prop] theorem linearWidth_primitive :
    Primitive (fun p : Input => linearWidth p.1 p.2.1 p.2.2) := by
  unfold linearWidth rangeSum
  fun_prop
@[fun_prop] theorem area_primitive :
    Primitive (fun p : Input => area p.1 p.2.1 p.2.2) := by
  unfold area rangeSum
  fun_prop

@[fun_prop] theorem stateWeight_primitive :
    Primitive (fun p : RawAutomaton × (List ℚ × ℕ) =>
      stateWeight p.1 p.2.1 p.2.2) := by
  unfold stateWeight
  fun_prop
@[fun_prop] theorem imageWeight_primitive :
    Primitive (fun p : RawAutomaton × (List ℚ × (ℕ × ℕ)) =>
      imageWeight p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold imageWeight
  fun_prop

@[fun_prop] theorem stateWeights_primitive :
    Primitive (fun p : RawAutomaton × List ℚ => stateWeights p.1 p.2) := by
  unfold stateWeights
  fun_prop
@[fun_prop] theorem imageWeights_primitive :
    Primitive (fun p : RawAutomaton × List ℚ => imageWeights p.1 p.2) := by
  unfold imageWeights
  fun_prop
@[fun_prop] theorem totalWeights_primitive :
    Primitive (fun p : RawAutomaton × List ℚ => totalWeights p.1 p.2) := by
  unfold totalWeights
  fun_prop
@[fun_prop] theorem letterWeights_primitive :
    Primitive (fun p : RawAutomaton × (List ℚ × ℕ) =>
      letterWeights p.1 p.2.1 p.2.2) := by
  unfold letterWeights base rho
  fun_prop

@[fun_prop] theorem direction_primitive : Primitive (fun p : ℕ × ℕ => direction p.1 p.2) := by
  unfold direction
  fun_prop
@[fun_prop] theorem determinant_primitive :
    Primitive (fun p : Vec3 × (Vec3 × Vec3) => determinant p.1 p.2.1 p.2.2) := by
  unfold determinant
  fun_prop
@[fun_prop] theorem triple_primitive :
    Primitive (fun p : ℕ × (ℕ × (ℕ × ℕ)) => triple p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold triple
  fun_prop
@[fun_prop] theorem statePoint_primitive :
    Primitive (fun p : MomentWitness × ℕ => statePoint p.1 p.2) := by
  unfold statePoint
  fun_prop
@[fun_prop] theorem imagePoint_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (ℕ × ℕ)) =>
      imagePoint p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold imagePoint rho
  fun_prop
@[fun_prop] theorem isLetter_primitive : PrimitivePred (fun p : ℕ × ℕ => IsLetter p.1 p.2) := by
  unfold IsLetter
  fun_prop
@[fun_prop] theorem head_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (ℕ × (ℕ × ℕ))) =>
      head p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold head offHead headConstant base digit
  fun_prop
@[fun_prop] theorem statePair_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (ℕ × (ℕ × ℕ))) =>
      statePair p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold statePair
  fun_prop
@[fun_prop] theorem imagePair_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (ℕ × (ℕ × (ℕ × ℕ)))) =>
      imagePair p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold imagePair rho base
  fun_prop

@[fun_prop] theorem initialVolume_primitive :
    Primitive (fun p : Input => initialVolume p.1 p.2.1 p.2.2) := by
  unfold initialVolume
  fun_prop
@[fun_prop] theorem initialArea_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (List ℚ × ℕ)) =>
      initialArea p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold initialArea
  fun_prop
@[fun_prop] theorem initialWidth_primitive :
    Primitive (fun p : RawAutomaton × (MomentWitness × (List ℚ × (ℕ × ℕ))) =>
      initialWidth p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold initialWidth rangeSum
  fun_prop
@[fun_prop] theorem initialStats_primitive :
    Primitive (fun p : Input => initialStats p.1 p.2.1 p.2.2) := by
  unfold initialStats
  fun_prop

@[fun_prop] theorem statsArea_primitive :
    Primitive (fun p : RawStats × ℕ => statsArea p.1 p.2) := by
  unfold statsArea
  fun_prop
@[fun_prop] theorem statsWidth_primitive :
    Primitive (fun p : RawStats × (ℕ × ℕ) => statsWidth p.1 p.2.1 p.2.2) := by
  unfold statsWidth
  fun_prop
@[fun_prop] theorem step_primitive :
    Primitive (fun p : ℕ × (List ℚ × (ℕ × RawStats)) =>
      step p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold step
  fun_prop
@[fun_prop] theorem references_primitive : Primitive references := by
  unfold references
  fun_prop

/-- One exact primitive-recursive rational evaluator for every dimension and
every finite input, before the moment certificate search is attached. -/
theorem formula_primitive : Primitive (fun p : Input => formula p.1 p.2.1 p.2.2) := by
  unfold formula
  fun_prop

end MixedVolume.UniformFormula

end -- public section
end -- component scope
/- END SOURCE: MixedVolume/Computability/UniformFormulaData.lean -/

end -- former unit scope
/- END FORMER UNIT: MixedVolume.General.UniformFoundations -/

/- BEGIN FORMER UNIT: MixedVolume.MainResultsAll -/
section

/-! Standby source partition. Generation is not a proof certificate.
Exact copied proof ranges are recorded in the adjacent manifest. -/

/- BEGIN SOURCE: MixedVolume/Computability/UniformFormulaCorrectness.lean -/
section


/-! Identification of the dimension-uniform list evaluator with the complete
canonical arithmetic formula. No bound on either dimension occurs here. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.UniformFormula

open UniformMoments UniformLinearSystems GeneralLabels
open scoped BigOperators

variable {s m : ℕ}

def primitiveIndex : PlanarRational.Primitive s m → ℕ
  | .inl j => j.val
  | .inr (a,j) => m + (j.val + m*a.val)

def primitiveEquiv (s m : ℕ) : PlanarRational.Primitive s m ≃ Fin (m+s*m) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) finProdFinEquiv).trans finSumFinEquiv

@[simp] theorem primitiveEquiv_val (i : PlanarRational.Primitive s m) :
    (primitiveEquiv s m i).val = primitiveIndex i := by
  rcases i with j | ⟨a,j⟩ <;>
    simp [primitiveEquiv,primitiveIndex,finSumFinEquiv,finProdFinEquiv,
      Equiv.trans_apply,Equiv.sumCongr]

theorem primitiveIndex_lt (i : PlanarRational.Primitive s m) : primitiveIndex i < m+s*m := by
  rw [← primitiveEquiv_val]
  exact (primitiveEquiv s m i).isLt

theorem primitive_sum (s m : ℕ) (f : ℕ → ℚ) :
    rangeSum (m+s*m) f = ∑ i : PlanarRational.Primitive s m, f (primitiveIndex i) := by
  rw [rangeSum_eq]
  simpa only [primitiveEquiv_val] using
    ((primitiveEquiv s m).sum_comp (fun i : Fin (m+s*m) => f i.val)).symm

theorem map_range_eq_ofFn {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (i : ℕ) (hi : i < n) (a : α) :
    ((List.range n).map f).getD i a = f i := by
  rw [map_range_eq_ofFn]
  exact getD_ofFn _ ⟨i,hi⟩ a

theorem referenceIndex_lt (r : Reference s) : ExplicitLabels.referenceIndex r < s+4 := by
  have h := (ExplicitLabels.referenceEquiv s r).isLt
  rw [ExplicitLabels.referenceEquiv_val] at h
  omega

@[simp] theorem imageLetter_index (A : AutomatonMoments.RationalData s m) (a : Fin s) (j : Fin m) :
    imageLetter (encode A) (primitiveIndex (.inr (a,j))) = a.val := by
  have hm : 0 < m := Nat.zero_lt_of_lt j.isLt
  simp only [imageLetter,primitiveIndex,states_encode,Nat.add_sub_cancel_left]
  rw [Nat.add_mul_div_left _ _ hm,Nat.div_eq_of_lt j.isLt,zero_add]

@[simp] theorem imageState_index (A : AutomatonMoments.RationalData s m) (a : Fin s) (j : Fin m) :
    imageState (encode A) (primitiveIndex (.inr (a,j))) = j.val := by
  simp only [imageState,primitiveIndex,states_encode,Nat.add_sub_cancel_left,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]

section Moments

variable (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
  (W : MomentWitness) (hW : Correct (encode A) W)

include hs hW

theorem imageWidth_correct (a : Fin s) (j : Fin m) :
    imageWidth (encode A) W a j = PlanarRational.imageWidthQ A a j := by
  simp [imageWidth,PlanarRational.imageWidthQ,digit,
    UniformMoments.mass_eq A hs W hW,UniformMoments.first_eq A hs W hW]

theorem imageMixed_correct (a b : Fin s) (j k : Fin m) :
    imageMixed (encode A) W a b j k = PlanarRational.imageMixedQ A a b j k := by
  simp [imageMixed,PlanarRational.imageMixedQ,Fin.val_inj,
    UniformMoments.pair_eq A hs W hW,
    UniformMoments.cross_encode A W (UniformMoments.mass_eq A hs W hW)
      (UniformMoments.first_eq A hs W hW)]

theorem stateImage_correct (j : Fin m) (a : Fin s) (k : Fin m) :
    stateImage (encode A) W j a k = PlanarRational.stateImageQ A j a k := by
  simp [stateImage,PlanarRational.stateImageQ,rangeSum_eq,
    imageWidth_correct A hs W hW,imageMixed_correct A hs W hW]

theorem primitiveHeight_correct (i : PlanarRational.Primitive s m) :
    primitiveHeight (encode A) W (primitiveIndex i) = PlanarRational.heightQ A i := by
  rcases i with j | ⟨a,j⟩
  · simp [primitiveHeight,primitiveIndex,j.isLt,PlanarRational.heightQ,
      UniformMoments.mass_eq A hs W hW]
  · have h : ¬m+(j.val+m*a.val)<m := by omega
    simp only [primitiveHeight,states_encode,primitiveIndex,if_neg h]
    change rho (encode A) * mass W
      (imageState (encode A) (primitiveIndex (.inr (a,j)))) = _
    rw [imageState_index,rho_encode,UniformMoments.mass_eq A hs W hW]
    rfl

theorem primitiveWidth_correct (i : PlanarRational.Primitive s m) :
    primitiveWidth (encode A) W (primitiveIndex i) = PlanarRational.widthQ A i := by
  rcases i with j | ⟨a,j⟩
  · simp [primitiveWidth,primitiveIndex,j.isLt,PlanarRational.widthQ,
      UniformMoments.first_eq A hs W hW]
  · have h : ¬m+(j.val+m*a.val)<m := by omega
    simp only [primitiveWidth,states_encode,primitiveIndex,if_neg h]
    change imageWidth (encode A) W
      (imageLetter (encode A) (primitiveIndex (.inr (a,j))))
      (imageState (encode A) (primitiveIndex (.inr (a,j)))) = _
    rw [imageLetter_index,imageState_index,imageWidth_correct A hs W hW]
    rfl

theorem primitiveMixed_correct (i j : PlanarRational.Primitive s m) :
    primitiveMixed (encode A) W (primitiveIndex i) (primitiveIndex j) = PlanarRational.mixedQ A i j := by
  have him (a : Fin s) (j : Fin m) : ¬primitiveIndex (.inr (a,j)) < m := by
    dsimp [primitiveIndex]
    omega
  rcases i with i | ⟨a,i⟩ <;> rcases j with j | ⟨b,j⟩
  · simp [primitiveMixed,primitiveIndex,PlanarRational.mixedQ,i.isLt,j.isLt,
      UniformMoments.pair_eq A hs W hW]
  · simp only [primitiveMixed,states_encode,
      show primitiveIndex (.inl i : PlanarRational.Primitive s m) = i.val from rfl,
      if_pos i.isLt,if_neg (him b j)]
    rw [imageLetter_index,imageState_index,stateImage_correct A hs W hW]
    rfl
  · simp only [primitiveMixed,states_encode,if_neg (him a i)]
    rw [show primitiveIndex (.inl j) = j.val from rfl,if_pos j.isLt,
      imageLetter_index,imageState_index,stateImage_correct A hs W hW]
    rfl
  · simp only [primitiveMixed,states_encode,if_neg (him a i),if_neg (him b j),
      imageLetter_index,imageState_index,imageMixed_correct A hs W hW]
    rfl

theorem linearHeight_correct (b : List ℚ) (c : PlanarRational.Primitive s m → ℚ)
    (hb : ∀ i, get b (primitiveIndex i) = c i) :
    linearHeight (encode A) W b = CanonicalArithmetic.height A c := by
  change rangeSum (m+s*m) (fun i => get b i * primitiveHeight (encode A) W i) = _
  rw [primitive_sum]
  simp_rw [hb,primitiveHeight_correct A hs W hW]
  simp [CanonicalArithmetic.height,CanonicalArithmetic.linear]

theorem linearWidth_correct (b : List ℚ) (c : PlanarRational.Primitive s m → ℚ)
    (hb : ∀ i, get b (primitiveIndex i) = c i) :
    linearWidth (encode A) W b = CanonicalArithmetic.width A c := by
  change rangeSum (m+s*m) (fun i => get b i * primitiveWidth (encode A) W i) = _
  rw [primitive_sum]
  simp_rw [hb,primitiveWidth_correct A hs W hW]
  simp [CanonicalArithmetic.width,CanonicalArithmetic.linear]

theorem area_correct (b : List ℚ) (c : PlanarRational.Primitive s m → ℚ)
    (hb : ∀ i, get b (primitiveIndex i) = c i) :
    area (encode A) W b = CanonicalArithmetic.area A c := by
  change (1/2 : ℚ) * rangeSum (m+s*m) (fun i =>
    rangeSum (m+s*m) (fun j => get b i * get b j * primitiveMixed (encode A) W i j)) = _
  rw [primitive_sum]
  simp_rw [primitive_sum,hb,primitiveMixed_correct A hs W hW]
  simp [CanonicalArithmetic.area]

end Moments

section Weights

variable (A : AutomatonMoments.RationalData s m) (u : List ℚ) (w : Label s m → ℚ)
  (hw : ∀ i, u.getD (ExplicitLabels.index i) 0 = w i)

include hw

theorem stateWeight_correct (j : Fin m) : stateWeight (encode A) u j = w (stateLabel j) := by
  simpa [stateWeight,get,referenceCount,ExplicitLabels.index,stateLabel,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hw (stateLabel j)

theorem imageWeight_correct (a : Fin s) (j : Fin m) : imageWeight (encode A) u a j = w (imageLabel a j) := by
  simpa [imageWeight,get,referenceCount,ExplicitLabels.index,imageLabel,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hw (imageLabel a j)

theorem referenceWeight_correct (r : Reference s) :
    get u (ExplicitLabels.referenceIndex r) = w (ref r) := by
  simpa only [ExplicitLabels.index_ref,get] using hw (ref r)

theorem stateWeights_correct (i : PlanarRational.Primitive s m) :
    get (stateWeights (encode A) u) (primitiveIndex i) =
      GeneralProjections.stateWeights (fun j => w (stateLabel j)) i := by
  simp only [stateWeights,get,primitiveCount,states_encode,alphabet_encode]
  rw [getD_map_range _ _ _ (primitiveIndex_lt i)]
  rcases i with j | ⟨a,j⟩
  · simp [primitiveIndex,j.isLt,GeneralProjections.stateWeights,stateWeight_correct A u w hw]
  · have h : ¬m+(j.val+m*a.val)<m := by omega
    simp [primitiveIndex,h,GeneralProjections.stateWeights]

theorem imageWeights_correct (i : PlanarRational.Primitive s m) :
    get (imageWeights (encode A) u) (primitiveIndex i) =
      GeneralProjections.imageWeights (fun aj => w (imageLabel aj.1 aj.2)) i := by
  simp only [imageWeights,get,primitiveCount,states_encode,alphabet_encode]
  rw [getD_map_range _ _ _ (primitiveIndex_lt i)]
  rcases i with j | ⟨a,j⟩
  · simp [primitiveIndex,j.isLt,GeneralProjections.imageWeights]
  · have h : ¬primitiveIndex (.inr (a,j)) < m := by dsimp [primitiveIndex]; omega
    simp only [states_encode,if_neg h,imageLetter_index,imageState_index,
      imageWeight_correct A u w hw,GeneralProjections.imageWeights]

theorem totalWeights_correct (i : PlanarRational.Primitive s m) :
    get (totalWeights (encode A) u) (primitiveIndex i) =
      GeneralProjections.totalWeights (fun j => w (stateLabel j))
        (fun aj => w (imageLabel aj.1 aj.2)) i := by
  simp only [totalWeights,get,primitiveCount,states_encode,alphabet_encode]
  rw [getD_map_range _ _ _ (primitiveIndex_lt i)]
  rcases i with j | ⟨a,j⟩
  · simp [primitiveIndex,j.isLt,GeneralProjections.totalWeights,stateWeight_correct A u w hw]
  · have h : ¬primitiveIndex (.inr (a,j)) < m := by dsimp [primitiveIndex]; omega
    simp only [states_encode,if_neg h,imageLetter_index,imageState_index,
      imageWeight_correct A u w hw,GeneralProjections.totalWeights]

theorem letterWeights_correct (a : Fin s) (i : PlanarRational.Primitive s m) :
    get (letterWeights (encode A) u a) (primitiveIndex i) =
      GeneralProjections.letterWeights (AutomatonMoments.baseQ s/AutomatonMoments.rhoQ s) a
        (fun j => w (stateLabel j)) (fun aj => w (imageLabel aj.1 aj.2)) i := by
  simp only [letterWeights,get,primitiveCount,states_encode,alphabet_encode]
  rw [getD_map_range _ _ _ (primitiveIndex_lt i)]
  rcases i with j | ⟨b,j⟩
  · simp [primitiveIndex,j.isLt,GeneralProjections.letterWeights]
  · have h : ¬primitiveIndex (.inr (b,j)) < m := by dsimp [primitiveIndex]; omega
    simp only [states_encode,if_neg h,imageLetter_index,imageState_index,
      imageWeight_correct A u w hw,stateWeight_correct A u w hw,
      GeneralProjections.letterWeights,base_encode,rho_encode,Fin.val_inj]

end Weights

def pack (v : Fin 3 → ℚ) : Vec3 := (v 0,(v 1,v 2))

theorem determinant_pack (u v x : Fin 3 → ℚ) :
    determinant (pack u) (pack v) (pack x) = GeneralWidths.detQ u v x := rfl

theorem direction_correct (r : Reference s) :
    direction s (ExplicitLabels.referenceIndex r) = pack (ReferenceRecursion.directionQ r) := by
  rcases r with i | a | u
  · fin_cases i <;>
      norm_num [direction,ExplicitLabels.referenceIndex,pack,ReferenceRecursion.directionQ,Pi.single_apply]
  · have ha := a.isLt
    change direction s (3+a.val) = (-((a.val : ℚ)+1),(-((s : ℚ)+1),1))
    dsimp [direction]
    split_ifs <;> try omega
    simp only [Nat.add_sub_cancel_left]
    congr 1 <;> ring
  · change direction s (3+s) = (0,(-1,1))
    dsimp [direction]
    split_ifs <;> try omega
    rfl

theorem tripleQ_eq_abs_det (i j k : Reference s) :
    ReferenceRecursion.tripleQ i j k =
      |GeneralWidths.detQ (ReferenceRecursion.directionQ i) (ReferenceRecursion.directionQ j)
        (ReferenceRecursion.directionQ k)| := by
  apply Rat.cast_injective (α := ℝ)
  rw [ReferenceRecursion.cast_tripleQ,Rat.cast_abs,GeneralWidths.cast_detQ]
  simp only [ReferenceRecursion.cast_directionQ]
  rw [GeneralWidths.pairFunctional_oriented]
  split_ifs <;> simp only [ContinuousLinearMap.neg_apply,abs_neg]

theorem triple_correct (i j k : Reference s) :
    triple s (ExplicitLabels.referenceIndex i) (ExplicitLabels.referenceIndex j)
      (ExplicitLabels.referenceIndex k) = ReferenceRecursion.tripleQ i j k := by
  rw [triple,direction_correct,direction_correct,direction_correct,determinant_pack,tripleQ_eq_abs_det]

section PairWidths

variable (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
  (W : MomentWitness) (hW : Correct (encode A) W)

include hs hW in
theorem statePoint_correct (k : Fin m) : statePoint W k = pack (GeneralWidths.statePointQ A k) := by
  simp [statePoint,pack,GeneralWidths.statePointQ,UniformMoments.first_eq A hs W hW,
    UniformMoments.mass_eq A hs W hW]

include hs hW in
theorem imagePoint_correct (a : Fin s) (k : Fin m) :
    imagePoint (encode A) W a k = pack (GeneralWidths.imagePointQ A a k) := by
  simp [imagePoint,pack,GeneralWidths.imagePointQ,imageWidth_correct A hs W hW,
    PlanarRational.imageWidthQ,UniformMoments.mass_eq A hs W hW]

include hs hW in
theorem head_correct (a b : Fin s) (k : Fin m) :
    head (encode A) W a b k = WidthAlgebra.headMomentQ A a b k := by
  simp [head,WidthAlgebra.headMomentQ,Fin.val_inj,UniformMoments.threshold_eq A hs W hW,
    UniformMoments.offHead_encode A W (UniformMoments.mass_eq A hs W hW)
      (UniformMoments.first_eq A hs W hW)]

private theorem isLetter_axis (i : Fin 3) : ¬IsLetter s i.val := by
  have hi := i.isLt
  simp only [IsLetter]
  omega

private theorem axis_ne_identity (i : Fin 3) : i.val ≠ s+3 := by
  have hi := i.isLt
  omega

private theorem isLetter_letter (a : Fin s) : IsLetter s (3+a.val) := by
  have ha := a.isLt
  constructor <;> omega

private theorem letter_ne_identity (a : Fin s) : 3+a.val ≠ s+3 := by
  have ha := a.isLt
  omega

private theorem not_isLetter_identity : ¬IsLetter s (s+3) := by
  simp only [IsLetter]
  omega

include hs hW in
theorem statePair_correct (k : Fin m) (i j : Reference s) :
    statePair (encode A) W k (ExplicitLabels.referenceIndex i) (ExplicitLabels.referenceIndex j) =
      GeneralWidths.statePairQ A k i j := by
  simp only [statePair,alphabet_encode,direction_correct,statePoint_correct A hs W hW,determinant_pack]
  rcases i with i | a | u <;> rcases j with j | b | v <;>
    simp only [ExplicitLabels.referenceIndex,GeneralWidths.statePairQ,Nat.add_comm 3 s,
      isLetter_axis,axis_ne_identity,isLetter_letter,letter_ne_identity,not_isLetter_identity,
      and_false,false_and,true_and,and_true,eq_self_iff_true,if_false,if_true,
      Nat.add_sub_cancel_left,UniformMoments.threshold_eq A hs W hW]

include hs hW in
theorem imagePair_correct (b : Fin s) (k : Fin m) (i j : Reference s) :
    imagePair (encode A) W b k (ExplicitLabels.referenceIndex i) (ExplicitLabels.referenceIndex j) =
      GeneralWidths.imagePairQ A b k i j := by
  simp only [imagePair,alphabet_encode,direction_correct,imagePoint_correct A hs W hW,determinant_pack]
  rcases i with i | a | u <;> rcases j with j | c | v <;>
    simp only [ExplicitLabels.referenceIndex,GeneralWidths.imagePairQ,Nat.add_comm 3 s,
      isLetter_axis,axis_ne_identity,isLetter_letter,letter_ne_identity,not_isLetter_identity,
      and_false,false_and,true_and,and_true,eq_self_iff_true,if_false,if_true,
      Nat.add_sub_cancel_left,head_correct A hs W hW,rho_encode,base_encode]

end PairWidths

def unpack (s : ℕ) (z : RawStats) : ReferenceRecursion.Stats ℚ s where
  volume := z.1
  area i := statsArea z (ExplicitLabels.referenceIndex i)
  width i j := statsWidth z (ExplicitLabels.referenceIndex i) (ExplicitLabels.referenceIndex j)

section Initial

variable (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
  (W : MomentWitness) (hW : Correct (encode A) W)
  (u : List ℚ) (w : Label s m → ℚ) (hw : ∀ i, u.getD (ExplicitLabels.index i) 0 = w i)

include hs hW hw

theorem initialVolume_correct :
    initialVolume (encode A) W u =
      (CanonicalArithmetic.initialStats A (fun j => w (stateLabel j))
        (fun aj => w (imageLabel aj.1 aj.2))).volume := by
  rw [initialVolume,
    area_correct A hs W hW _ _ (stateWeights_correct A u w hw),
    linearHeight_correct A hs W hW _ _ (imageWeights_correct A u w hw),
    linearHeight_correct A hs W hW _ _ (stateWeights_correct A u w hw),
    area_correct A hs W hW _ _ (imageWeights_correct A u w hw)]
  rfl

theorem initialArea_correct (r : Reference s) :
    initialArea (encode A) W u (ExplicitLabels.referenceIndex r) =
      (CanonicalArithmetic.initialStats A (fun j => w (stateLabel j))
        (fun aj => w (imageLabel aj.1 aj.2))).area r := by
  have hAs := area_correct A hs W hW _ _ (stateWeights_correct A u w hw)
  have hAi := area_correct A hs W hW _ _ (imageWeights_correct A u w hw)
  have hHs := linearHeight_correct A hs W hW _ _ (stateWeights_correct A u w hw)
  have hHi := linearHeight_correct A hs W hW _ _ (imageWeights_correct A u w hw)
  have hWs := linearWidth_correct A hs W hW _ _ (stateWeights_correct A u w hw)
  have hWi := linearWidth_correct A hs W hW _ _ (imageWeights_correct A u w hw)
  rcases r with i | a | v
  · fin_cases i <;> simp [initialArea,ExplicitLabels.referenceIndex,CanonicalArithmetic.initialStats,
      hAs,hAi,hHs,hHi,hWs,hWi]
  · have ha := a.isLt
    simp only [initialArea,ExplicitLabels.referenceIndex,alphabet_encode]
    split_ifs <;> try omega
    simp only [Nat.add_sub_cancel_left]
    exact area_correct A hs W hW _ _ (letterWeights_correct A u w hw a)
  · simp only [initialArea,ExplicitLabels.referenceIndex,alphabet_encode]
    split_ifs <;> try omega
    exact area_correct A hs W hW _ _ (totalWeights_correct A u w hw)

theorem initialWidth_correct (i j : Reference s) :
    initialWidth (encode A) W u (ExplicitLabels.referenceIndex i) (ExplicitLabels.referenceIndex j) =
      (CanonicalArithmetic.initialStats A (fun j => w (stateLabel j))
        (fun aj => w (imageLabel aj.1 aj.2))).width i j := by
  simp [initialWidth,rangeSum_eq,stateWeight_correct A u w hw,imageWeight_correct A u w hw,
    statePair_correct A hs W hW,imagePair_correct A hs W hW,
    CanonicalArithmetic.initialStats,CanonicalArithmetic.linear,Fintype.sum_prod_type]

theorem initialStats_correct :
    unpack s (initialStats (encode A) W u) =
      CanonicalArithmetic.initialStats A (fun j => w (stateLabel j))
        (fun aj => w (imageLabel aj.1 aj.2)) := by
  apply ReferenceRecursion.Stats.ext
  · exact initialVolume_correct A hs W hW u w hw
  · funext i
    change ((List.range (referenceCount (encode A))).map (initialArea (encode A) W u)).getD
      (ExplicitLabels.referenceIndex i) 0 = _
    simp only [referenceCount,alphabet_encode]
    rw [getD_map_range _ _ _ (referenceIndex_lt i)]
    exact initialArea_correct A hs W hW u w hw i
  · funext i j
    change (((List.range (referenceCount (encode A))).map (fun i =>
      (List.range (referenceCount (encode A))).map (initialWidth (encode A) W u i))).getD
      (ExplicitLabels.referenceIndex i) []).getD (ExplicitLabels.referenceIndex j) 0 = _
    simp only [referenceCount,alphabet_encode]
    rw [getD_map_range _ _ _ (referenceIndex_lt i),getD_map_range _ _ _ (referenceIndex_lt j)]
    exact initialWidth_correct A hs W hW u w hw i j

end Initial

theorem references_correct (s : ℕ) :
    references s = (CanonicalArithmetic.references s).map ExplicitLabels.referenceIndex := by
  simp only [references,CanonicalArithmetic.references,List.map_append,List.map_ofFn,
    Function.comp_def,List.map_cons,List.map_nil,axisRef,letterRef,identityRef,ExplicitLabels.referenceIndex]
  rw [← map_range_eq_ofFn 3 (fun i => i),← map_range_eq_ofFn s (fun a => 3+a)]
  simp only [List.map_id_fun',id_eq]

theorem step_correct (s : ℕ) (u : List ℚ) (v : Reference s → ℚ)
    (hu : ∀ r, get u (ExplicitLabels.referenceIndex r) = v r)
    (j : Reference s) (z : RawStats) :
    unpack s (step s u (ExplicitLabels.referenceIndex j) z) =
      ReferenceRecursion.step ReferenceRecursion.tripleQ (v j) j (unpack s z) := by
  apply ReferenceRecursion.Stats.ext
  · change z.1 + get u (ExplicitLabels.referenceIndex j) * _ = _
    rw [hu]
    rfl
  · funext i
    change ((List.range (s+4)).map _).getD (ExplicitLabels.referenceIndex i) 0 = _
    rw [getD_map_range _ _ _ (referenceIndex_lt i),hu]
    rfl
  · funext i k
    change (((List.range (s+4)).map _).getD (ExplicitLabels.referenceIndex i) []).getD
      (ExplicitLabels.referenceIndex k) 0 = _
    rw [getD_map_range _ _ _ (referenceIndex_lt i),getD_map_range _ _ _ (referenceIndex_lt k),
      hu,triple_correct]
    rfl

theorem run_correct (s : ℕ) (u : List ℚ) (v : Reference s → ℚ)
    (hu : ∀ r, get u (ExplicitLabels.referenceIndex r) = v r)
    (l : List (Reference s)) (z : RawStats) :
    unpack s ((l.map ExplicitLabels.referenceIndex).foldl (fun z j => step s u j z) z) =
      ReferenceRecursion.run ReferenceRecursion.tripleQ v (unpack s z) l := by
  induction l generalizing z with
  | nil => rfl
  | cons j l ih =>
    simp only [List.map_cons,List.foldl_cons,ReferenceRecursion.run,ih,step_correct s u v hu]

/-- Exact equality of the single dimension-uniform list program with the
complete canonical cubic, for every accepted moment certificate. -/
theorem formula_correct (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
    (W : MomentWitness) (hW : Correct (encode A) W)
    (u : List ℚ) (w : Label s m → ℚ) (hw : ∀ i, u.getD (ExplicitLabels.index i) 0 = w i) :
    formula (encode A) W u = CanonicalArithmetic.formula A w := by
  have h := run_correct s u (fun r => w (ref r)) (referenceWeight_correct u w hw)
    (CanonicalArithmetic.references s) (initialStats (encode A) W u)
  rw [initialStats_correct A hs W hW u w hw] at h
  rw [formula,alphabet_encode,references_correct]
  simpa only [unpack,CanonicalArithmetic.formula,Algebra.algebraMap_self,RingHom.id_apply] using
    congrArg ReferenceRecursion.Stats.volume h

theorem formula_eq (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
    (W : MomentWitness) (hW : Correct (encode A) W)
    (u : List ℚ) (w : Label s m → ℚ) (hw : ∀ i, u.getD (ExplicitLabels.index i) 0 = w i) :
    formula (encode A) W u = CanonicalArithmetic.formula A w :=
  formula_correct A hs W hW u w hw

end MixedVolume.UniformFormula

end
end
end -- component scope
/- END SOURCE: MixedVolume/Computability/UniformFormulaCorrectness.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/UniformInterpolation.lean -/
section


/-! Uniform exact interpolation with natural-number dimensions and indices.

The existing Lagrange correctness theorem is retained. Its coefficient recursion
is implemented by a finite coefficient-list fold; every coefficient and sample
weight is computed by one primitive recursive program with all bounds supplied
as input. There is no fixed bound on dimension, degree, index, or denominator.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.UniformInterpolation

open Represented RationalExtraction VolumePolynomials
open scoped BigOperators

/-- Multiply a finite coefficient vector by the normalized factor
`(X-a)/(x-a)`, retaining its final coefficient. -/
def coefficientStep (x a : ℚ) (cs : List ℚ) : List ℚ :=
  (List.range (cs.length+1)).map fun k =>
    (x-a)⁻¹ * ((0::cs).getD k 0 - a*cs.getD k 0)

theorem coefficientStep_getD (x a : ℚ) (cs : List ℚ) (k : ℕ) :
    (coefficientStep x a cs).getD k 0 =
      (x-a)⁻¹ * ((0::cs).getD k 0 - a*cs.getD k 0) := by
  by_cases hk : k < cs.length+1
  · simp only [coefficientStep,List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_range hk,Option.map_some,Option.getD_some]
  · have hstep : (coefficientStep x a cs).length ≤ k := by
      simp only [coefficientStep,List.length_map,List.length_range]
      omega
    have hshift : (0::cs).length ≤ k := by simp only [List.length_cons]; omega
    have hcs : cs.length ≤ k := by omega
    rw [List.getD_eq_default (coefficientStep x a cs) 0 hstep,
      List.getD_eq_default (0::cs) 0 hshift,List.getD_eq_default cs 0 hcs]
    simp

def coefficientList (x : ℚ) (nodes : List ℚ) : List ℚ :=
  nodes.foldr (coefficientStep x) [1]

theorem coefficientList_length (x : ℚ) (nodes : List ℚ) :
    (coefficientList x nodes).length = nodes.length+1 := by
  induction nodes with
  | nil => rfl
  | cons a nodes ih =>
    change (coefficientStep x a (coefficientList x nodes)).length = _
    simp only [coefficientStep,List.length_map,List.length_range,List.length_cons,ih]

/-- The finite-list program computes exactly the previously justified
Lagrange coefficient, including all indices beyond the polynomial degree. -/
theorem coefficientList_getD (x : ℚ) (nodes : List ℚ) (k : ℕ) :
    (coefficientList x nodes).getD k 0 = RationalExtraction.lagrangeCoefficient x nodes k := by
  induction nodes generalizing k with
  | nil => cases k <;> simp [coefficientList,RationalExtraction.lagrangeCoefficient]
  | cons a nodes ih =>
    change (coefficientStep x a (coefficientList x nodes)).getD k 0 = _
    rw [coefficientStep_getD]
    cases k with
    | zero =>
        simp only [List.getD_cons_zero,ih,RationalExtraction.lagrangeCoefficient,zero_sub]
    | succ k =>
        simp only [List.getD_cons_succ,ih,RationalExtraction.lagrangeCoefficient]

variable {α : Type} [Representation α]

@[fun_prop] theorem coefficientStep_primitive {x a : α → ℚ} {cs : α → List ℚ}
    (hx : Primitive x) (ha : Primitive a) (hc : Primitive cs) :
    Primitive (fun u => coefficientStep (x u) (a u) (cs u)) := by
  unfold coefficientStep
  fun_prop

@[fun_prop] theorem coefficientList_primitive {x : α → ℚ} {nodes : α → List ℚ}
    (hx : Primitive x) (hn : Primitive nodes) :
    Primitive (fun u => coefficientList (x u) (nodes u)) := by
  unfold coefficientList
  apply Primitive.list_foldr
    (h := fun u : α × (ℚ × List ℚ) => coefficientStep (x u.1) u.2.1 u.2.2)
    hn (Primitive.const [1])
  exact coefficientStep_primitive (hx.comp Primitive.fst)
    (Primitive.fst.comp Primitive.snd) (Primitive.snd.comp Primitive.snd)

@[fun_prop] theorem lagrangeCoefficient_primitive {x : α → ℚ}
    {nodes : α → List ℚ} {k : α → ℕ}
    (hx : Primitive x) (hn : Primitive nodes) (hk : Primitive k) :
    Primitive (fun u => RationalExtraction.lagrangeCoefficient (x u) (nodes u) (k u)) := by
  exact (Primitive.list_getD 0 (coefficientList_primitive hx hn) hk).of_eq
    (fun u => coefficientList_getD (x u) (nodes u) (k u))

/-- The list of all other interpolation nodes, with a variable bound. -/
def otherNodes (N j : ℕ) : List ℚ :=
  ((List.range N).filter (fun k => decide (k ≠ j))).map (fun k : ℕ => (k : ℚ)+1)

@[fun_prop] theorem otherNodes_primitive {N j : α → ℕ}
    (hN : Primitive N) (hj : Primitive j) :
    Primitive (fun u => otherNodes (N u) (j u)) := by
  unfold otherNodes
  fun_prop

/-- Runtime inputs are the interpolation-table size, node number, and
coefficient index. The function remains total for arbitrary natural inputs. -/
def extractionWeight (N j k : ℕ) : ℚ :=
  (coefficientList ((j : ℚ)+1) (otherNodes N j)).getD k 0

@[fun_prop] theorem extractionWeight_primitive {N j k : α → ℕ}
    (hN : Primitive N) (hj : Primitive j) (hk : Primitive k) :
    Primitive (fun u => extractionWeight (N u) (j u) (k u)) := by
  unfold extractionWeight
  fun_prop

theorem finRange_values (N : ℕ) :
    (List.finRange N).map (Fin.val : Fin N → ℕ) = List.range N := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem otherNodes_eq (N : ℕ) (j : Fin N) :
    otherNodes N j =
      (((List.finRange N).filter (fun k => decide (k ≠ j))).map
        (fun k : Fin N => (k.val : ℚ)+1)) := by
  unfold otherNodes
  rw [←finRange_values N,List.filter_map,List.map_map]
  simp only [Function.comp_def,ne_eq,Fin.val_inj]

/-- Compatibility with every entry of the already proved coefficient extractor. -/
theorem extractionWeight_eq {n d : ℕ} (a : MultiIndex n d)
    (j : Fin (RationalExtraction.interpolationSize n d)) :
    extractionWeight (RationalExtraction.interpolationSize n d) j (RationalExtraction.coefficientCode a) =
      RationalExtraction.coefficientExtractionWeight a j := by
  rw [extractionWeight,coefficientList_getD,otherNodes_eq]
  rfl

/-- Runtime sample weights, with a variable coordinate index and base. -/
def sampleWeight (base node coordinate : ℕ) : ℚ :=
  ((node : ℚ)+1) ^ (base ^ coordinate)

@[fun_prop] theorem sampleWeight_primitive {base node coordinate : α → ℕ}
    (hb : Primitive base) (hn : Primitive node) (hi : Primitive coordinate) :
    Primitive (fun u => sampleWeight (base u) (node u) (coordinate u)) := by
  unfold sampleWeight
  fun_prop

theorem sampleWeight_eq {n d : ℕ} (j : Fin (RationalExtraction.interpolationSize n d)) (i : Fin n) :
    sampleWeight (d+2) j i = RationalExtraction.interpolationWeight j i := rfl

/-- The base and the entire exponent list are computational inputs. -/
@[fun_prop] theorem ofDigits_primitive {base : α → ℕ} {digits : α → List ℕ}
    (hb : Primitive base) (hd : Primitive digits) :
    Primitive (fun u => Nat.ofDigits (base u) (digits u)) := by
  have h := Primitive.list_foldr
    (h := fun u : α × (ℕ × ℕ) => u.2.1 + base u.1 * u.2.2)
    hd (Primitive.const (0 : ℕ))
    ((Primitive.fst.comp Primitive.snd).nat_add
      ((hb.comp Primitive.fst).nat_mul (Primitive.snd.comp Primitive.snd)))
  apply h.of_eq
  intro u
  simpa only [Nat.cast_id] using (Nat.ofDigits_eq_foldr (base u) (digits u)).symm

/-- Recover one coefficient from a finite list of sample values. All lengths
and the requested index are ordinary input data to the same program. -/
def coefficientFromSamples (N k : ℕ) (values : List ℚ) : ℚ :=
  ((List.range N).map fun j => extractionWeight N j k * values.getD j 0).sum

@[fun_prop] theorem coefficientFromSamples_primitive {N k : α → ℕ}
    {values : α → List ℚ} (hN : Primitive N) (hk : Primitive k)
    (hv : Primitive values) :
    Primitive (fun u => coefficientFromSamples (N u) (k u) (values u)) := by
  unfold coefficientFromSamples
  fun_prop

/-- The uniform program recovers the intended ordinary coefficient for every
dimension and degree whenever its list supplies the exact interpolation samples. -/
theorem coefficientFromSamples_cast {n d : ℕ} (c : Coefficients n d)
    (a : MultiIndex n d) (values : List ℚ)
    (hvalues : ∀ j : Fin (RationalExtraction.interpolationSize n d),
      (values.getD j 0 : ℝ) = evaluate c (fun i => (RationalExtraction.interpolationWeight j i : ℝ))) :
    (coefficientFromSamples (RationalExtraction.interpolationSize n d) (RationalExtraction.coefficientCode a) values : ℝ) =
      c a := by
  rw [RationalExtraction.coefficient_eq_rational_samples c a]
  unfold coefficientFromSamples
  rw [Primitive.range_sum_eq_fin_sum]
  simp only [Rat.cast_sum,Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [extractionWeight_eq,hvalues]

end MixedVolume.UniformInterpolation

end -- noncomputable section
end -- public section
end -- component scope
/- END SOURCE: MixedVolume/Computability/UniformInterpolation.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/UniformEncoding.lean -/
section


/-! A single partial recursive coefficient algorithm for Theorem 4.3.

The alphabet size, state size, transition matrices, stationary row, initial
row, and threshold are all input data. A terminating exact search obtains the
four finite moment arrays; finite rational interpolation then emits every
cubic coefficient. The output records its dimension and a dense coefficient
table in base five. The table includes every homogeneous cubic multi-index,
without an a priori bound on either dimension or any input denominator.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.UniformEncoding

open Represented UniformMoments UniformInterpolation UniformLinearSystems
open AutomatonMoments GeneralLabels GeneralLocus VolumePolynomials RationalExtraction
open GeneralDeficit GeneralTarget CanonicalArithmetic CanonicalVolume RationalReduction
open scoped BigOperators

/-- Automaton, stationary row, initial row, and threshold, all as ordinary
finite rational data. Validity is a semantic input promise in the correctness
theorem, rather than an extra argument supplied to the program. -/
abbrev Input := RawAutomaton × (List ℚ × (List ℚ × ℚ))

/-- The dimension is included explicitly in the output header. -/
abbrev Output := ℕ × List ℚ

def encodeInput {s m : ℕ} (A : RationalData s m) (p : Fin m → ℚ) (theta : ℚ) : Input :=
  (UniformMoments.encode A,(List.ofFn A.stationary,(List.ofFn p,theta)))

def dimension (I : Input) : ℕ :=
  (alphabet I.1+1)*states I.1+alphabet I.1+5

def tableSize (I : Input) : ℕ := 5 ^ dimension I

def stateStart (D : RawAutomaton) : ℕ := 3+(alphabet D+1)

def deficitIndex (D : RawAutomaton) : ℕ :=
  stateStart D+(states D+alphabet D*states D)

def gamma (I : Input) : ℚ :=
  rangeSum (states I.1) (fun j => I.2.1.getD j 0 * accepting I.1 j)

def delta (I : Input) (j : ℕ) : ℚ :=
  ((1+I.2.2.2)/(1+gamma I))*I.2.1.getD j 0-I.2.2.1.getD j 0

def shiftedWeight (I : Input) (node i : ℕ) : ℚ :=
  if stateStart I.1 ≤ i ∧ i < stateStart I.1+states I.1 then
    sampleWeight 5 node i+
      delta I (i-stateStart I.1)*sampleWeight 5 node (deficitIndex I.1)
  else sampleWeight 5 node i

def shiftedWeights (I : Input) (node : ℕ) : List ℚ :=
  (List.range (dimension I)).map (shiftedWeight I node)

def samples (I : Input) (W : MomentWitness) : List ℚ :=
  (List.range (tableSize I)).map (fun node =>
    UniformFormula.formula I.1 W (shiftedWeights I node))

def coefficientTable (I : Input) (W : MomentWitness) : List ℚ :=
  let values := samples I W
  (List.range (tableSize I)).map (fun k =>
    coefficientFromSamples (tableSize I) k values)

def output (I : Input) (W : MomentWitness) : Output :=
  (dimension I,coefficientTable I W)

section Computation

variable {α : Type} [Representation α]

@[fun_prop] theorem dimension_primitive {I : α → Input} (hI : Primitive I) :
    Primitive (fun x => dimension (I x)) := by
  unfold dimension alphabet states
  fun_prop

@[fun_prop] theorem tableSize_primitive {I : α → Input} (hI : Primitive I) :
    Primitive (fun x => tableSize (I x)) := by
  unfold tableSize
  fun_prop

@[fun_prop] theorem stateStart_primitive {D : α → RawAutomaton} (hD : Primitive D) :
    Primitive (fun x => stateStart (D x)) := by
  unfold stateStart alphabet
  fun_prop

@[fun_prop] theorem deficitIndex_primitive {D : α → RawAutomaton} (hD : Primitive D) :
    Primitive (fun x => deficitIndex (D x)) := by
  unfold deficitIndex alphabet states
  fun_prop

@[fun_prop] theorem gamma_primitive {I : α → Input} (hI : Primitive I) :
    Primitive (fun x => gamma (I x)) := by
  unfold gamma rangeSum accepting states
  fun_prop

@[fun_prop] theorem delta_primitive {I : α → Input} {j : α → ℕ}
    (hI : Primitive I) (hj : Primitive j) :
    Primitive (fun x => delta (I x) (j x)) := by
  unfold delta
  fun_prop

@[fun_prop] theorem shiftedWeight_primitive {I : α → Input} {node i : α → ℕ}
    (hI : Primitive I) (hn : Primitive node) (hi : Primitive i) :
    Primitive (fun x => shiftedWeight (I x) (node x) (i x)) := by
  unfold shiftedWeight states
  fun_prop

@[fun_prop] theorem shiftedWeights_primitive {I : α → Input} {node : α → ℕ}
    (hI : Primitive I) (hn : Primitive node) :
    Primitive (fun x => shiftedWeights (I x) (node x)) := by
  unfold shiftedWeights
  fun_prop

@[fun_prop] theorem formula_primitive_apply {D : α → RawAutomaton}
    {W : α → MomentWitness} {w : α → List ℚ}
    (hD : Primitive D) (hW : Primitive W) (hw : Primitive w) :
    Primitive (fun x => UniformFormula.formula (D x) (W x) (w x)) :=
  UniformFormula.formula_primitive.comp (hD.pair (hW.pair hw))

@[fun_prop] theorem samples_primitive {I : α → Input} {W : α → MomentWitness}
    (hI : Primitive I) (hW : Primitive W) :
    Primitive (fun x => samples (I x) (W x)) := by
  unfold samples
  fun_prop

@[fun_prop] theorem coefficientTable_primitive {I : α → Input} {W : α → MomentWitness}
    (hI : Primitive I) (hW : Primitive W) :
    Primitive (fun x => coefficientTable (I x) (W x)) := by
  unfold coefficientTable
  fun_prop

theorem output_primitive : Primitive (fun x : Input × MomentWitness => output x.1 x.2) := by
  unfold output
  fun_prop

end Computation

section Correctness

variable {s m : ℕ} (A : RationalData s m) (p : Fin m → ℚ) (theta : ℚ)

@[simp] theorem dimension_encode : dimension (encodeInput A p theta) = numberOfBodies s m := rfl

@[simp] theorem tableSize_encode :
    tableSize (encodeInput A p theta) = RationalExtraction.interpolationSize (numberOfBodies s m) 3 := rfl

theorem gamma_encode : gamma (encodeInput A p theta) = gammaQ A := by
  simp [gamma,encodeInput,rangeSum_eq,gammaQ]

theorem delta_encode (j : Fin m) :
    delta (encodeInput A p theta) j = deltaQ A p theta j := by
  rw [delta,gamma_encode]
  simp [encodeInput,deltaQ]

/-- A typed specification of the finite shifted sample-weight list. -/
def typedWeight (node : ℕ) : Label s m → ℚ
  | .inr (.inl j) =>
    sampleWeight 5 node (ExplicitLabels.index (stateLabel (s := s) j))+
      deltaQ A p theta j*sampleWeight 5 node (ExplicitLabels.index (deficitLabel (s := s) (m := m)))
  | i => sampleWeight 5 node (ExplicitLabels.index i)

theorem shiftedWeight_eq (node : ℕ) (i : Label s m) :
    shiftedWeight (encodeInput A p theta) node (ExplicitLabels.index i) =
      typedWeight A p theta node i := by
  rcases i with (i | a | u) | j | ⟨a,j⟩ | u
  · have h : ¬(3+(s+1) ≤ i.val) := by have := i.isLt; omega
    simp [shiftedWeight,encodeInput,stateStart,ExplicitLabels.index,typedWeight,h]
  · have h : ¬(3+(s+1) ≤ 3+a.val) := by have := a.isLt; omega
    simp [shiftedWeight,encodeInput,stateStart,ExplicitLabels.index,typedWeight,h]
  · have h : ¬(3+(s+1) ≤ 3+s) := by omega
    simp [shiftedWeight,encodeInput,stateStart,ExplicitLabels.index,typedWeight,h]
  · have hlo : 3+(s+1) ≤ 3+(s+1)+j.val := by omega
    have hhi : 3+(s+1)+j.val < 3+(s+1)+m := by have := j.isLt; omega
    simp only [shiftedWeight,encodeInput,UniformMoments.alphabet_encode,
      UniformMoments.states_encode,stateStart,ExplicitLabels.index,hlo,hhi,and_self,ite_true,
      Nat.add_sub_cancel_left]
    rw [show delta (UniformMoments.encode A,(List.ofFn A.stationary,(List.ofFn p,theta))) j =
      deltaQ A p theta j from delta_encode A p theta j]
    rfl
  · have h : ¬(3+(s+1)+(m+(j.val+m*a.val)) < 3+(s+1)+m) := by omega
    simp [shiftedWeight,encodeInput,stateStart,ExplicitLabels.index,typedWeight,h]
  · have h : ¬(3+(s+1)+(m+s*m) < 3+(s+1)+m) := by omega
    simp [shiftedWeight,encodeInput,stateStart,ExplicitLabels.index,typedWeight,h]

theorem shiftedWeights_getD (node : ℕ) (i : Label s m) :
    (shiftedWeights (encodeInput A p theta) node).getD (ExplicitLabels.index i) 0 =
      typedWeight A p theta node i := by
  have hi : ExplicitLabels.index i < dimension (encodeInput A p theta) :=
    ExplicitLabels.index_lt i
  simp only [shiftedWeights,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some]
  exact shiftedWeight_eq A p theta node i

theorem typedWeight_cast
    (node : Fin (RationalExtraction.interpolationSize (numberOfBodies s m) 3)) (i : Label s m) :
    (typedWeight A p theta node i : ℝ) =
      shiftWeight (targetDelta A.toReal (fun j => (p j : ℝ)) (theta : ℝ))
        (fun k => (RationalExtraction.interpolationWeight node (ExplicitLabels.labelEquiv s m k) : ℝ)) i := by
  rcases i with r | j | aj | u <;>
    simp [typedWeight,shiftWeight,cast_deltaQ,sampleWeight,RationalExtraction.interpolationWeight,
      RationalExtraction.interpolationNode,ExplicitLabels.labelEquiv_val,stateLabel,deficitLabel]

theorem samples_getD (W : MomentWitness)
    (node : Fin (RationalExtraction.interpolationSize (numberOfBodies s m) 3)) :
    (samples (encodeInput A p theta) W).getD node 0 =
      UniformFormula.formula (UniformMoments.encode A) W
        (shiftedWeights (encodeInput A p theta) node) := by
  have hn : node.val < tableSize (encodeInput A p theta) := node.isLt
  simp only [samples,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range hn,Option.map_some,Option.getD_some]
  rfl

theorem samples_cast (hs : 0 < s) (W : MomentWitness)
    (hW : Correct (UniformMoments.encode A) W)
    (node : Fin (RationalExtraction.interpolationSize (numberOfBodies s m) 3)) :
    ((samples (encodeInput A p theta) W).getD node 0 : ℝ) =
      evaluate (ExplicitLabels.coefficientArray A.toReal hs
        (fun j => (p j : ℝ)) (theta : ℝ))
        (fun i => (RationalExtraction.interpolationWeight node i : ℝ)) := by
  have hmap (u : Label s m → ℚ) :
      ((formula A u : ℚ) : ℝ) = formula A (fun i => (u i : ℝ)) := by
    simpa only [eq_ratCast] using map_formula (Algebra.ofId ℚ ℝ) A u
  rw [samples_getD,UniformFormula.formula_eq A hs W hW _
    (typedWeight A p theta node) (shiftedWeights_getD A p theta node)]
  rw [hmap,ExplicitLabels.evaluate_coefficientArray,
    targetPolynomial_eval_formula]
  congr 1
  funext i
  exact typedWeight_cast A p theta node i

theorem coefficientTable_length (W : MomentWitness) :
    (coefficientTable (encodeInput A p theta) W).length =
      RationalExtraction.interpolationSize (numberOfBodies s m) 3 := by
  simp [coefficientTable]

theorem coefficientTable_cast (hs : 0 < s) (W : MomentWitness)
    (hW : Correct (UniformMoments.encode A) W)
    (a : MultiIndex (numberOfBodies s m) 3) :
    ((coefficientTable (encodeInput A p theta) W).getD (RationalExtraction.coefficientCode a) 0 : ℝ) =
      ExplicitLabels.coefficientArray A.toReal hs (fun j => (p j : ℝ)) (theta : ℝ) a := by
  have ha : RationalExtraction.coefficientCode a < tableSize (encodeInput A p theta) := RationalExtraction.coefficientCode_lt a
  simp only [coefficientTable,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range ha,Option.map_some,Option.getD_some]
  rw [tableSize_encode]
  exact coefficientFromSamples_cast _ a _ (samples_cast A p theta hs W hW)

end Correctness

/-- A concrete exact-code implementation extracted from the proved primitive
recursive arithmetic expression. This choice selects a proved program and
does not assume any computational claim. -/
def finish : Code (Input × MomentWitness) → Code Output :=
  Classical.choose output_primitive

theorem finish_primrec : Primrec finish := (Classical.choose_spec output_primitive).1

theorem finish_correct (x : Code (Input × MomentWitness)) :
    decode (finish x) = output (decode x.1) (decode x.2) :=
  (Classical.choose_spec output_primitive).2 x

/-- The same partial recursive program handles every alphabet and state size.
The only unbounded search is for the finite exact moment certificate. -/
def program (c : Code Input) : Part (Code Output) :=
  (UniformMoments.program c.1).map (fun w => finish (c,w))

theorem program_partrec : Partrec program :=
  (UniformMoments.program_partrec.comp Computable.fst).map finish_primrec.to_comp.to₂

theorem program_terminates {s m : ℕ} (A : RationalData s m) (hs : 0 < s)
    (p : Fin m → ℚ) (theta : ℚ) (c : Code Input)
    (hc : decode c = encodeInput A p theta) : (program c).Dom := by
  apply UniformMoments.program_terminates A hs c.1
  exact congrArg Prod.fst hc

/-- Every rational stochastic input is representable, with no restriction on
alphabet size, state size, numerator size, or denominator size. -/
theorem input_coverage {s m : ℕ} (A : RationalData s m) (p : Fin m → ℚ) (theta : ℚ) :
    ∃ c : Code Input, decode c = encodeInput A p theta :=
  Representation.onto _

/-- Complete output semantics: the header gives the required number of bodies,
and every cubic coefficient is the coefficient of the canonical target
polynomial, in a specified injective natural-number encoding. -/
theorem program_correct {s m : ℕ} (A : RationalData s m) (hs : 0 < s)
    (p : Fin m → ℚ) (theta : ℚ) (c : Code Input)
    (hc : decode c = encodeInput A p theta) (result : Code Output)
    (hr : result ∈ program c) :
    (decode result).1 = numberOfBodies s m ∧
    (decode result).2.length = RationalExtraction.interpolationSize (numberOfBodies s m) 3 ∧
    ∀ a : MultiIndex (numberOfBodies s m) 3,
      ((decode result).2.getD (RationalExtraction.coefficientCode a) 0 : ℝ) =
        ExplicitLabels.coefficientArray A.toReal hs (fun j => (p j : ℝ)) (theta : ℝ) a := by
  obtain ⟨w,hw,rfl⟩ := (Part.mem_map_iff _).mp hr
  have hW := UniformMoments.program_spec c.1 w hw
  have hD : decode c.1 = UniformMoments.encode A := congrArg Prod.fst hc
  rw [hD] at hW
  rw [finish_correct,hc]
  refine ⟨rfl,coefficientTable_length A p theta (decode w),?_⟩
  exact coefficientTable_cast A p theta hs (decode w) hW

/-- The returned dense table denotes the full homogeneous cubic array. -/
def decodedArray (n : ℕ) (result : Code Output) : Coefficients n 3 :=
  fun a => ((decode result).2.getD (RationalExtraction.coefficientCode a) 0 : ℝ)

/-- The program is chosen before the dimensions and every rational input.
This quantifier order makes the uniform computational claim explicit. -/
theorem exists_uniform_program :
    ∃ F : Code Input → Part (Code Output), Partrec F ∧
      ∀ (s m : ℕ) (A : RationalData s m) (hs : 0 < s)
        (p : Fin m → ℚ) (theta : ℚ) (c : Code Input),
        decode c = encodeInput A p theta →
        (F c).Dom ∧ ∀ result ∈ F c,
          (decode result).1 = numberOfBodies s m ∧
          (decode result).2.length = RationalExtraction.interpolationSize (numberOfBodies s m) 3 ∧
          ∀ a : MultiIndex (numberOfBodies s m) 3,
            decodedArray (numberOfBodies s m) result a =
              ExplicitLabels.coefficientArray A.toReal hs
                (fun j => (p j : ℝ)) (theta : ℝ) a := by
  refine ⟨program,program_partrec,?_⟩
  intro s m A hs p theta c hc
  exact ⟨program_terminates A hs p theta c hc,
    program_correct A hs p theta c hc⟩

/-- The uniform algorithmic assertion in Theorem 4.3, with exact semantic
equivalence to realization by arbitrary compact convex bodies. -/
theorem theorem_4_3_uniform {s m : ℕ} (A : RationalData s m) (hs : 0 < s)
    (p : Fin m → ℚ) (hp : AutomatonWords.ProbabilityRow (fun j => (p j : ℝ)))
    (theta : ℚ) (htheta₀ : 0 < theta) (htheta₁ : theta < 1)
    (c : Code Input) (hc : decode c = encodeInput A p theta) :
    (program c).Dom ∧
    ∀ result ∈ program c,
      (decode result).1 = numberOfBodies s m ∧
      (decode result).2.length = RationalExtraction.interpolationSize (numberOfBodies s m) 3 ∧
      (∀ a : MultiIndex (numberOfBodies s m) 3,
        decodedArray (numberOfBodies s m) result a =
          ExplicitLabels.coefficientArray A.toReal hs (fun j => (p j : ℝ)) (theta : ℝ) a) ∧
      (decodedArray (numberOfBodies s m) result ∈ VolumeLocus (numberOfBodies s m) 3 ↔
        A.toReal.UniversalCutpoint (fun j => (p j : ℝ)) (theta : ℝ)) := by
  refine ⟨program_terminates A hs p theta c hc,?_⟩
  intro result hr
  obtain ⟨hn,hl,he⟩ := program_correct A hs p theta c hc result hr
  refine ⟨hn,hl,he,?_⟩
  have harray : decodedArray (numberOfBodies s m) result =
      ExplicitLabels.coefficientArray A.toReal hs (fun j => (p j : ℝ)) (theta : ℝ) :=
    funext he
  rw [harray,ExplicitLabels.coefficientArray_mem_iff]
  exact GeneralLocus.coefficientArray_mem_iff A.toReal hs _ hp _
    (by exact_mod_cast htheta₀) (by exact_mod_cast htheta₁)

end MixedVolume.UniformEncoding

end -- noncomputable section
end -- public section
end -- component scope
/- END SOURCE: MixedVolume/Computability/UniformEncoding.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/UniformQuadratic.lean -/
section


/-! The exact quadratic family computed by the dimension-uniform algorithm.

The geometric proof originally used an abstract finite enumeration. The
uniform algorithm uses explicit block numbering. This file gives a rational
coefficient polynomial in that same numbering, proves degree at most two,
and identifies the output of the single program with its evaluation. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.UniformQuadratic

open VolumePolynomials AutomatonWords AutomatonMoments GeneralLabels GeneralLocus
open GeneralTarget GeneralDeficit CanonicalArithmetic CanonicalVolume
open ParameterDegree RationalExtraction RationalReduction MvPolynomial
open scoped BigOperators

variable {s m : ℕ}

def sample (k : Fin (RationalExtraction.interpolationSize (numberOfBodies s m) 3)) (i : Label s m) : ℚ :=
  RationalExtraction.interpolationWeight k (ExplicitLabels.labelEquiv s m i)

def coefficientSymbol (A : RationalData s m) (a : MultiIndex (numberOfBodies s m) 3) :
    MvPolynomial (Parameter m) ℚ :=
  ∑ k, C (RationalExtraction.coefficientExtractionWeight a k) * formula A (shiftedSample A (sample k))

def coefficientMap (A : RationalData s m) (p : Fin m → ℝ) (theta : ℝ) :
    Coefficients (numberOfBodies s m) 3 :=
  fun a => MvPolynomial.aeval (assignment p theta) (coefficientSymbol A a)

theorem coefficientSymbol_degree_le_two (A : RationalData s m)
    (a : MultiIndex (numberOfBodies s m) 3) :
    (coefficientSymbol A a).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro k _
  apply (degree_mul (e := 2) (degree_C _) ?_).trans (by omega)
  apply formula_degree A _
  · intro r
    exact degree_C _
  · intro j
    exact degree_add ((degree_C _).trans (by omega))
      ((degree_mul (deltaSymbol_degree A j) (degree_C _)).trans (by omega))
  · intro a j
    exact degree_C _

theorem coefficientMap_eq (A : RationalData s m) (hs : 0 < s)
    (p : Fin m → ℝ) (theta : ℝ) :
    coefficientMap A p theta = ExplicitLabels.coefficientArray A.toReal hs p theta := by
  ext a
  rw [coefficientMap,coefficientSymbol,map_sum]
  rw [RationalExtraction.coefficient_eq_rational_samples (ExplicitLabels.coefficientArray A.toReal hs p theta) a]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul,MvPolynomial.aeval_C,map_formula]
  rw [ExplicitLabels.evaluate_coefficientArray,targetPolynomial_eval_formula]
  congr 2
  funext i
  exact eval_shiftedSample A p theta (sample k) i

/-- All real probability rows and all real cutpoints in the full open interval
have the stated geometric meaning for the same family emitted by the program. -/
theorem coefficientMap_membership (A : RationalData s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : ProbabilityRow p) (theta : ℝ)
    (htheta₀ : 0 < theta) (htheta₁ : theta < 1) :
    coefficientMap A p theta ∈ VolumeLocus (numberOfBodies s m) 3 ↔
      A.toReal.UniversalCutpoint p theta := by
  rw [coefficientMap_eq A hs,ExplicitLabels.coefficientArray_mem_iff]
  exact GeneralLocus.coefficientArray_mem_iff A.toReal hs p hp theta htheta₀ htheta₁

/-- The rational-output program and the real quadratic family are the same
coefficient array, rather than unrelated witnesses to two existence claims. -/
theorem program_matches_map (A : RationalData s m) (hs : 0 < s)
    (p : Fin m → ℚ) (theta : ℚ) (c : Represented.Code UniformEncoding.Input)
    (hc : Represented.decode c = UniformEncoding.encodeInput A p theta)
    (result : Represented.Code UniformEncoding.Output)
    (hr : result ∈ UniformEncoding.program c) :
    UniformEncoding.decodedArray (numberOfBodies s m) result =
      coefficientMap A (fun j => (p j : ℝ)) (theta : ℝ) := by
  rw [coefficientMap_eq A hs]
  exact funext (UniformEncoding.program_correct A hs p theta c hc result hr).2.2

end MixedVolume.UniformQuadratic

end -- noncomputable section
end -- public section
end -- component scope
/- END SOURCE: MixedVolume/Computability/UniformQuadratic.lean -/

/- BEGIN SOURCE: MixedVolume/General/ThreeStateExample.lean -/
section


/-! The literal three-state stochastic matrix and affine coordinates in §6.

The matrix, output, and stationary row are exactly the displayed rational
data in the paper. The spectral formula is proved for every finite word by
induction, and the universal cutpoint condition is identified with every
dyadic half-space inequality. A fixed open ball about the displayed interior
parameter point lies in the probability-row and open-cutpoint domain.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.ThreeStateExample

open Matrix AutomatonWords AutomatonMoments Set
open scoped BigOperators

def transition : Matrix (Fin 3) (Fin 3) ℚ :=
  !![5/8,1/8,1/4; 1/8,5/8,1/4; 1/4,1/4,1/2]

def output : Fin 3 → ℚ := ![1,0,0]

/-- The exact rational stochastic data printed immediately before Theorem 6.1. -/
def rationalData : RationalData 1 3 where
  P _ := transition
  P_nonneg _ i j := by
    fin_cases i <;> fin_cases j <;> norm_num [transition]
  P_sum _ i := by
    fin_cases i <;> norm_num [transition,Fin.sum_univ_succ]
  f := output
  f_nonneg i := by fin_cases i <;> norm_num [output]
  f_le_one i := by fin_cases i <;> norm_num [output]
  stationary _ := 1/3
  stationary_nonneg _ := by norm_num
  stationary_sum := by norm_num [Fin.sum_univ_succ]
  stationary_fixed _ := by
    funext j
    fin_cases j <;> norm_num [Matrix.vecMul,dotProduct,transition,Fin.sum_univ_succ]

def oneVector : Fin 3 → ℝ := ![1,1,1]
def u : Fin 3 → ℝ := ![1,-1,0]
def v : Fin 3 → ℝ := ![1,1,-2]

theorem eigen_one (a : Fin 1) :
    rationalData.toReal.P a *ᵥ oneVector = oneVector := by
  funext j
  fin_cases j <;>
    norm_num [rationalData,RationalData.toReal,transition,oneVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem eigen_half (a : Fin 1) :
    rationalData.toReal.P a *ᵥ u = (1/2 : ℝ) • u := by
  funext j
  fin_cases j <;>
    norm_num [rationalData,RationalData.toReal,transition,u,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem eigen_quarter (a : Fin 1) :
    rationalData.toReal.P a *ᵥ v = (1/4 : ℝ) • v := by
  funext j
  fin_cases j <;>
    norm_num [rationalData,RationalData.toReal,transition,v,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem output_decomposition :
    rationalData.toReal.f = (1/3 : ℝ) • oneVector + (1/2 : ℝ) • u + (1/6 : ℝ) • v := by
  funext j
  fin_cases j <;> norm_num [rationalData,RationalData.toReal,output,oneVector,u,v]

/-- All finite words, including the empty word, satisfy the displayed spectral
formula. There is no bounded-time verification in this statement. -/
theorem word_value (w : Word 1) :
    rationalData.toReal.value w =
      (1/3 : ℝ) • oneVector +
        ((1/2 : ℝ)*(1/2 : ℝ)^w.length) • u +
        ((1/6 : ℝ)*(1/4 : ℝ)^w.length) • v := by
  induction w with
  | nil =>
    have hnil : rationalData.toReal.value [] = rationalData.toReal.f := by
      funext j
      exact Data.value_nil rationalData.toReal j
    rw [hnil]
    simpa only [List.length_nil,pow_zero,mul_one] using output_decomposition
  | cons a w ih =>
    have hstep : rationalData.toReal.value (a::w) =
        rationalData.toReal.P a *ᵥ rationalData.toReal.value w := by
      funext j
      exact Data.value_cons rationalData.toReal a w j
    rw [hstep,ih]
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,eigen_one,eigen_half,eigen_quarter]
    funext j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,List.length_cons,pow_succ]
    ring

theorem wordMatrix_eq_pow (w : Word 1) :
    rationalData.toReal.wordMatrix w = (rationalData.toReal.P 0)^w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [Data.wordMatrix_cons,ih,List.length_cons,pow_succ']
    rfl

/-- The paper's formula for the powers of its literal displayed matrix. -/
theorem power_output (k : ℕ) :
    (rationalData.toReal.P 0)^k *ᵥ rationalData.toReal.f =
      (1/3 : ℝ) • oneVector +
        ((1/2 : ℝ)*(1/2 : ℝ)^k) • u +
        ((1/6 : ℝ)*(1/4 : ℝ)^k) • v := by
  have h := word_value (List.replicate k (0 : Fin 1))
  have hv : rationalData.toReal.value (List.replicate k (0 : Fin 1)) =
      (rationalData.toReal.P 0)^k *ᵥ rationalData.toReal.f := by
    funext j
    simp only [Data.value,wordMatrix_eq_pow,List.length_replicate]
  rw [hv] at h
  simpa only [List.length_replicate] using h

abbrev Parameter := Fin 3 → ℝ

/-- The inverse affine coordinates `(A,B,C) ↦ p` printed in §6. -/
def initial (a : Parameter) : Fin 3 → ℝ :=
  ![1/3+a 2+a 1,1/3+a 2-a 1,1/3-2*a 2]

def cutpoint (a : Parameter) : ℝ := 1/3-a 0

def coordinates (p : Fin 3 → ℝ) (theta : ℝ) : Parameter :=
  ![1/3-theta,(p 0-p 1)/2,(p 0+p 1-2*p 2)/6]

theorem coordinates_initial (a : Parameter) :
    coordinates (initial a) (cutpoint a) = a := by
  funext i
  fin_cases i <;> simp [coordinates,initial,cutpoint] <;> ring

theorem initial_sum (a : Parameter) : ∑ j, initial a j = 1 := by
  simp [initial,Fin.sum_univ_succ] <;> ring

theorem initial_coordinates (p : Fin 3 → ℝ) (theta : ℝ) (hp : ∑ j, p j = 1) :
    initial (coordinates p theta) = p := by
  have hsum : p 0+p 1+p 2 = 1 := by simpa only [Fin.sum_univ_three] using hp
  funext j
  fin_cases j <;> simp [initial,coordinates] <;> linarith

theorem cutpoint_coordinates (p : Fin 3 → ℝ) (theta : ℝ) :
    cutpoint (coordinates p theta) = theta := by
  simp [cutpoint,coordinates] <;> ring

/-- Exact acceptance in the paper's three affine parameters, without any
probability or cutpoint assumption needed for this algebraic identity. -/
theorem acceptance_formula (a : Parameter) (w : Word 1) :
    rationalData.toReal.acceptance (initial a) w =
      1/3+(1/2 : ℝ)^w.length*a 1+(1/4 : ℝ)^w.length*a 2 := by
  rw [Data.acceptance,word_value]
  simp only [dotProduct,Fin.sum_univ_succ,initial,oneVector,u,v,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons,Fin.val_zero,Fin.val_succ,Fin.sum_univ_zero,
    add_zero]
  ring

/-- The unrestricted word quantifier is exactly the unrestricted natural-number
quantifier in equation (10). -/
theorem universal_iff_inequalities (a : Parameter) :
    rationalData.toReal.UniversalCutpoint (initial a) (cutpoint a) ↔
      ∀ k : ℕ, a 0+(1/2 : ℝ)^k*a 1+(1/4 : ℝ)^k*a 2 ≤ 0 := by
  constructor
  · intro h k
    have hk := h (List.replicate k (0 : Fin 1))
    rw [acceptance_formula,List.length_replicate] at hk
    dsimp [cutpoint] at hk
    linarith
  · intro h w
    rw [acceptance_formula]
    dsimp [cutpoint]
    linarith [h w.length]

theorem universal_iff_cone (a : Parameter) :
    rationalData.toReal.UniversalCutpoint (initial a) (cutpoint a) ↔
      a ∈ DyadicCone.cone := by
  rw [universal_iff_inequalities]
  have hpow (k : ℕ) : ((1/2 : ℝ)^k)^2 = (1/4 : ℝ)^k := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  change (∀ k, a 0+(1/2 : ℝ)^k*a 1+(1/4 : ℝ)^k*a 2 ≤ 0) ↔
    ∀ k, a 0+DyadicCone.t k*a 1+DyadicCone.t k^2*a 2 ≤ 0
  simp only [DyadicCone.t,hpow]

/-- A concrete open neighbourhood of the paper's interior parameter point. -/
def parameterBall : Set Parameter := Metric.ball 0 (1/12)

theorem parameterBall_open : IsOpen parameterBall := Metric.isOpen_ball

theorem zero_mem_parameterBall : (0 : Parameter) ∈ parameterBall := by
  norm_num [parameterBall]

theorem coordinates_small {a : Parameter} (ha : a ∈ parameterBall) (j : Fin 3) :
    |a j| < (1/12 : ℝ) := by
  have hn : ‖a‖ < (1/12 : ℝ) := by
    simpa [parameterBall,Metric.mem_ball,dist_zero_right] using ha
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm a j).trans_lt hn

theorem initial_positive_of_mem_ball {a : Parameter} (ha : a ∈ parameterBall) (j : Fin 3) :
    0 < initial a j := by
  obtain ⟨hB₀,hB₁⟩ := abs_lt.mp (coordinates_small ha 1)
  obtain ⟨hC₀,hC₁⟩ := abs_lt.mp (coordinates_small ha 2)
  fin_cases j <;> simp [initial] <;> linarith

theorem domain_of_mem_ball {a : Parameter} (ha : a ∈ parameterBall) :
    ProbabilityRow (initial a) ∧ 0 < cutpoint a ∧ cutpoint a < 1 := by
  obtain ⟨hA₀,hA₁⟩ := abs_lt.mp (coordinates_small ha 0)
  refine ⟨⟨fun j => (initial_positive_of_mem_ball ha j).le,initial_sum a⟩,?_,?_⟩ <;>
    dsimp [cutpoint] <;> linarith

@[simp] theorem initial_zero : initial 0 = fun _ => (1/3 : ℝ) := by
  funext j
  fin_cases j <;> norm_num [initial]

@[simp] theorem cutpoint_zero : cutpoint 0 = (1/3 : ℝ) := by simp [cutpoint]

end MixedVolume.ThreeStateExample

end -- noncomputable section
end -- public section
end -- component scope
/- END SOURCE: MixedVolume/General/ThreeStateExample.lean -/

/- BEGIN SOURCE: MixedVolume/General/ThreeStateSection.lean -/
section


/-! The literal rational quadratic section specified in §6.

The three polynomial parameters are the paper's `(A,B,C)`. Substituting its
affine probability row and cutpoint into the exact general construction gives
the complete twelve-body cubic array. On an explicit open neighbourhood of
zero its realizability condition is exactly the full dyadic cone, with a
boundary patch on every one of the distinct displayed planes.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.ThreeStateSection

open VolumePolynomials GeneralLabels GeneralLocus GeneralTarget GeneralDeficit
open AutomatonMoments CanonicalArithmetic CanonicalVolume ParameterDegree
open RationalExtraction RationalReduction MvPolynomial ThreeStateExample Set
open scoped BigOperators

abbrev Label := GeneralLabels.Label 1 3
abbrev Index := MultiIndex 12 3
abbrev Polynomial := MvPolynomial (Fin 3) ℚ

def initialSymbol : Fin 3 → Polynomial :=
  ![C (1/3)+X 2+X 1,C (1/3)+X 2-X 1,C (1/3)-C 2*X 2]

def cutpointSymbol : Polynomial := C (1/3)-X 0

def delta (j : Fin 3) : Polynomial :=
  C (rationalData.stationary j/(1+gammaQ rationalData))*(1+cutpointSymbol)-initialSymbol j

def weight (w : Label → ℚ) : Label → Polynomial
  | .inr (.inl j) => C (w (stateLabel j))+delta j*C (w deficitLabel)
  | i => C (w i)

/-- Every ordinary cubic coefficient, expressed over the rational polynomial
ring in the three parameters of §6. -/
def coefficientSymbol (a : Index) : Polynomial :=
  ∑ k, C (RationalExtraction.coefficientExtractionWeight a k)*
    formula rationalData (weight (UniformQuadratic.sample k))

def coefficientMap (a : ThreeStateExample.Parameter) : Coefficients 12 3 :=
  fun i => MvPolynomial.aeval a (coefficientSymbol i)

private theorem degree_sub {p q : Polynomial} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    (p-q).totalDegree ≤ d := (totalDegree_sub p q).trans (max_le hp hq)

theorem initialSymbol_degree (j : Fin 3) : (initialSymbol j).totalDegree ≤ 1 := by
  have hc : (C (1/3) : Polynomial).totalDegree ≤ 1 := (degree_C _).trans (by omega)
  have hx (i : Fin 3) : (X i : Polynomial).totalDegree ≤ 1 :=
    (isHomogeneous_X ℚ i).totalDegree_le
  fin_cases j
  · exact degree_add (degree_add hc (hx 2)) (hx 1)
  · exact degree_sub (degree_add hc (hx 2)) (hx 1)
  · exact degree_sub hc (degree_mul (degree_C 2) (hx 2))

theorem cutpointSymbol_degree : cutpointSymbol.totalDegree ≤ 1 :=
  degree_sub ((degree_C _).trans (by omega)) ((isHomogeneous_X ℚ (0 : Fin 3)).totalDegree_le)

theorem delta_degree (j : Fin 3) : (delta j).totalDegree ≤ 1 :=
  degree_sub (degree_mul (degree_C _)
    (degree_add (by simp) cutpointSymbol_degree)) (initialSymbol_degree j)

theorem coefficientSymbol_degree_le_two (a : Index) :
    (coefficientSymbol a).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro k _
  apply (degree_mul (e := 2) (degree_C _) ?_).trans (by omega)
  apply formula_degree rationalData _
  · intro r
    exact degree_C _
  · intro j
    exact degree_add ((degree_C _).trans (by omega))
      ((degree_mul (delta_degree j) (degree_C _)).trans (by omega))
  · intro a j
    exact degree_C _

theorem eval_initialSymbol (a : ThreeStateExample.Parameter) (j : Fin 3) :
    MvPolynomial.aeval a (initialSymbol j) = initial a j := by
  fin_cases j <;> simp [initialSymbol,initial]

theorem eval_cutpointSymbol (a : ThreeStateExample.Parameter) :
    MvPolynomial.aeval a cutpointSymbol = cutpoint a := by
  simp [cutpointSymbol,cutpoint]

theorem eval_delta (a : ThreeStateExample.Parameter) (j : Fin 3) :
    MvPolynomial.aeval a (delta j) =
      targetDelta rationalData.toReal (initial a) (cutpoint a) j := by
  simp only [delta,map_sub,map_mul,MvPolynomial.aeval_C,map_add,map_one,
    eval_initialSymbol,eval_cutpointSymbol,eq_ratCast,Rat.cast_div,Rat.cast_add,Rat.cast_one,
    cast_gammaQ,targetDelta,eta]
  change (rationalData.stationary j : ℝ)/(1+rationalData.toReal.gamma)*(1+cutpoint a)-initial a j =
    ((1+cutpoint a)/(1+rationalData.toReal.gamma))*(rationalData.stationary j : ℝ)-initial a j
  ring

theorem eval_weight (a : ThreeStateExample.Parameter) (w : Label → ℚ) (i : Label) :
    MvPolynomial.aeval a (weight w i) =
      shiftWeight (targetDelta rationalData.toReal (initial a) (cutpoint a))
        (fun j => (w j : ℝ)) i := by
  rcases i with r | j | aj | u <;>
    simp [weight,shiftWeight,eval_delta,stateLabel]

/-- The family is precisely the general construction applied to the displayed
matrix and displayed affine coordinates, for every real parameter triple. -/
theorem coefficientMap_eq (a : ThreeStateExample.Parameter) :
    coefficientMap a =
      UniformQuadratic.coefficientMap rationalData (initial a) (cutpoint a) := by
  rw [UniformQuadratic.coefficientMap_eq rationalData (by decide)]
  ext i
  rw [coefficientMap,coefficientSymbol,map_sum]
  rw [RationalExtraction.coefficient_eq_rational_samples (ExplicitLabels.coefficientArray rationalData.toReal
    (by decide) (initial a) (cutpoint a)) i]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul,MvPolynomial.aeval_C,map_formula]
  rw [ExplicitLabels.evaluate_coefficientArray,targetPolynomial_eval_formula]
  congr 2
  funext i
  exact eval_weight a (UniformQuadratic.sample k) i

theorem membership_on_ball {a : ThreeStateExample.Parameter} (ha : a ∈ parameterBall) :
    coefficientMap a ∈ VolumeLocus 12 3 ↔ a ∈ DyadicCone.cone := by
  obtain ⟨hp,h₀,h₁⟩ := domain_of_mem_ball ha
  rw [coefficientMap_eq]
  exact (UniformQuadratic.coefficientMap_membership rationalData
    (by decide) (initial a) hp (cutpoint a) h₀ h₁).trans (universal_iff_cone a)

/-- Equality on an explicit open neighbourhood of the paper's interior
parameter point; all dyadic inequalities are retained. -/
theorem local_section_eq :
    parameterBall ∩ coefficientMap ⁻¹' VolumeLocus 12 3 =
      parameterBall ∩ DyadicCone.cone := by
  ext a
  constructor
  · rintro ⟨ha,hc⟩
    exact ⟨ha,(membership_on_ball ha).mp hc⟩
  · rintro ⟨ha,hc⟩
    exact ⟨ha,(membership_on_ball ha).mpr hc⟩

theorem frontier_on_ball :
    frontier (coefficientMap ⁻¹' VolumeLocus 12 3) ∩ parameterBall =
      frontier DyadicCone.cone ∩ parameterBall := by
  have he : (coefficientMap ⁻¹' VolumeLocus 12 3) ∩ parameterBall =
      DyadicCone.cone ∩ parameterBall := by
    calc
      (coefficientMap ⁻¹' VolumeLocus 12 3) ∩ parameterBall =
          parameterBall ∩ coefficientMap ⁻¹' VolumeLocus 12 3 := inter_comm _ _
      _ = parameterBall ∩ DyadicCone.cone := local_section_eq
      _ = DyadicCone.cone ∩ parameterBall := inter_comm _ _
  calc
    frontier (coefficientMap ⁻¹' VolumeLocus 12 3) ∩ parameterBall =
        frontier ((coefficientMap ⁻¹' VolumeLocus 12 3) ∩ parameterBall) ∩ parameterBall :=
      (frontier_inter_open_inter parameterBall_open).symm
    _ = frontier (DyadicCone.cone ∩ parameterBall) ∩ parameterBall := by rw [he]
    _ = frontier DyadicCone.cone ∩ parameterBall := frontier_inter_open_inter parameterBall_open

theorem planes_distinct {i j : ℕ} (hij : i ≠ j) : DyadicCone.plane i ≠ DyadicCone.plane j := by
  intro he
  let a : Fin 3 → ℝ := ![-DyadicCone.t i,1,0]
  have hi : a ∈ DyadicCone.plane i := by simp [a,DyadicCone.plane,DyadicCone.normal]
  have hj : a ∈ DyadicCone.plane j := he ▸ hi
  have ht : DyadicCone.t i = DyadicCone.t j := by
    have hh : -DyadicCone.t i+DyadicCone.t j = 0 := by
      simpa [a,DyadicCone.plane,DyadicCone.normal] using hj
    linarith
  exact hij (DyadicCone.t_strictAnti.injective ht)

/-- Each distinct plane has a relatively open patch in the boundary of the
literal section, at every positive scale around the interior parameter point. -/
theorem boundary_plane_patch_local (k : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ a : ThreeStateExample.Parameter, ∃ δ : ℝ, 0 < δ ∧
      a ∈ (DyadicCone.plane k ∩ parameterBall) ∩ Metric.ball 0 R ∧
      ∀ b, dist b a < δ → b ∈ DyadicCone.plane k →
        b ∈ (frontier (coefficientMap ⁻¹' VolumeLocus 12 3) ∩ parameterBall) ∩ Metric.ball 0 R := by
  obtain ⟨a,δ,hδ,ha,hpatch⟩ := DyadicCone.boundary_plane_patch_local
    k (min R (1/12)) (lt_min hR (by norm_num))
  have in_parameterBall {b : ThreeStateExample.Parameter}
      (hb : b ∈ Metric.ball 0 (min R (1/12))) : b ∈ parameterBall :=
    (show dist b 0 < (1/12 : ℝ) from hb.trans_le (min_le_right _ _))
  have in_radius {b : ThreeStateExample.Parameter}
      (hb : b ∈ Metric.ball 0 (min R (1/12))) : b ∈ Metric.ball 0 R :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hb).trans_le (min_le_left _ _))
  refine ⟨a,δ,hδ,⟨⟨ha.1,in_parameterBall ha.2⟩,in_radius ha.2⟩,?_⟩
  intro b hb hbk
  obtain ⟨hfront,hsmall⟩ := hpatch b hb hbk
  refine ⟨?_,in_radius hsmall⟩
  rw [frontier_on_ball]
  exact ⟨hfront,in_parameterBall hsmall⟩

/-- The explicit local-section and infinite-plane assertions of Theorem 6.1
for the actual stochastic matrix and affine coordinates printed in the paper. -/
theorem theorem_6_1_literal_section :
    (∀ a : Index, (coefficientSymbol a).totalDegree ≤ 2) ∧
    IsOpen parameterBall ∧ (0 : ThreeStateExample.Parameter) ∈ parameterBall ∧
    parameterBall ∩ coefficientMap ⁻¹' VolumeLocus 12 3 = parameterBall ∩ DyadicCone.cone ∧
    (∀ i j : ℕ, i ≠ j → DyadicCone.plane i ≠ DyadicCone.plane j) ∧
    (∀ (k : ℕ) (R : ℝ), 0 < R →
      ∃ a : ThreeStateExample.Parameter, ∃ δ : ℝ, 0 < δ ∧
        a ∈ (DyadicCone.plane k ∩ parameterBall) ∩ Metric.ball 0 R ∧
        ∀ b, dist b a < δ → b ∈ DyadicCone.plane k →
          b ∈ (frontier (coefficientMap ⁻¹' VolumeLocus 12 3) ∩ parameterBall) ∩ Metric.ball 0 R) :=
  ⟨coefficientSymbol_degree_le_two,parameterBall_open,zero_mem_parameterBall,local_section_eq,
    fun _ _ h => planes_distinct h,boundary_plane_patch_local⟩

end MixedVolume.ThreeStateSection

end -- noncomputable section
end -- public section
end -- component scope
/- END SOURCE: MixedVolume/General/ThreeStateSection.lean -/

/- BEGIN SOURCE: MixedVolume/MainTheorems.lean -/
section


/-!
# The principal statements of the mixed-volume paper

The named results below use the genuine compact-convex-body realization locus.
Computability refers to the exact, surjective rational input representation in
`CoefficientCoding`, with Mathlib's universal partial-recursive evaluator as
the source of all undecidability reductions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.MainResults

open VolumePolynomials CoefficientCoding Completeness

theorem realization_complement_re (n : ℕ) :
    REPred (fun c : ArrayCode n 3 => ¬ Realizable c) :=
  CoRE.realization_complement_re n 3 (by decide)

theorem nonnegative_realization_complement_re (n : ℕ) :
    REPred (fun c : NonnegativeArray n 3 => ¬ Realizable c.val) :=
  (show Partrec _ from realization_complement_re n).comp
    (nonnegative_val_primrec n 3).to_comp

theorem coRE_complete_44 : CoREComplete (Realizable : ArrayCode 44 3 → Prop) :=
  complete_of_nonhalting_reduction (realization_complement_re 44)
    HaltingEncoding.nonhalting_reduction

theorem coRE_complete_nonnegative_44 :
    CoREComplete (fun c : NonnegativeArray 44 3 => Realizable c.val) :=
  complete_of_nonhalting_reduction (nonnegative_realization_complement_re 44)
    HaltingEncoding.nonhalting_reduction_nonnegative

/-- Theorem 1.1, including the actual restricted input domain and the absence
of a sound and complete effective finite-certificate system. -/
theorem theorem_1_1 :
    CoREComplete (Realizable : ArrayCode 44 3 → Prop) ∧
    CoREComplete (fun c : NonnegativeArray 44 3 => Realizable c.val) ∧
    ¬ ComputablePred (Realizable : ArrayCode 44 3 → Prop) ∧
    ¬ ComputablePred (fun c : NonnegativeArray 44 3 => Realizable c.val) ∧
    ¬ ∃ verify : ArrayCode 44 3 × ℕ → Prop, ComputablePred verify ∧
        ∀ c, Realizable c ↔ ∃ certificate, verify (c,certificate) :=
  ⟨coRE_complete_44,coRE_complete_nonnegative_44,HaltingEncoding.undecidable,
    HaltingEncoding.undecidable_nonnegative,HaltingEncoding.no_realizability_certificates⟩

theorem nonhalting_reduction_all_n (n : ℕ) (hn : 44 ≤ n) :
    (fun index => ¬ MatrixMortality.Undecidability.CodeHalts index) ≤₀
      (Realizable : ArrayCode n 3 → Prop) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact HaltingEncoding.nonhalting_reduction.trans
    (EffectivePadding.padding_reduction 44 3 k)

theorem nonhalting_reduction_nonnegative_all_n (n : ℕ) (hn : 44 ≤ n) :
    (fun index => ¬ MatrixMortality.Undecidability.CodeHalts index) ≤₀
      (fun c : NonnegativeArray n 3 => Realizable c.val) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact HaltingEncoding.nonhalting_reduction_nonnegative.trans
    (EffectivePadding.padding_reduction_nonnegative 44 3 k)

/-- Realizability itself cannot be semidecided, on either full input domain. -/
theorem realization_not_re (n : ℕ) (hn : 44 ≤ n) :
    ¬ REPred (Realizable : ArrayCode n 3 → Prop) :=
  not_re_of_nonhalting_reduction (nonhalting_reduction_all_n n hn)

theorem nonnegative_realization_not_re (n : ℕ) (hn : 44 ≤ n) :
    ¬ REPred (fun c : NonnegativeArray n 3 => Realizable c.val) :=
  not_re_of_nonhalting_reduction (nonhalting_reduction_nonnegative_all_n n hn)

theorem no_nonnegative_realizability_certificates (n : ℕ) (hn : 44 ≤ n) :
    ¬ ∃ verify : NonnegativeArray n 3 × ℕ → Prop, ComputablePred verify ∧
      ∀ c, Realizable c.val ↔ ∃ certificate, verify (c,certificate) :=
  no_finite_certificates (nonhalting_reduction_nonnegative_all_n n hn)

/-- The point-padding extension retains every ordinary coefficient and applies
to every number of bodies at least forty-four. -/
theorem theorem_1_1_all_n (n : ℕ) (hn : 44 ≤ n) :
    CoREComplete (Realizable : ArrayCode n 3 → Prop) ∧
    CoREComplete (fun c : NonnegativeArray n 3 => Realizable c.val) ∧
    ¬ ComputablePred (Realizable : ArrayCode n 3 → Prop) ∧
    ¬ ComputablePred (fun c : NonnegativeArray n 3 => Realizable c.val) ∧
    ¬ ∃ verify : ArrayCode n 3 × ℕ → Prop, ComputablePred verify ∧
        ∀ c, Realizable c ↔ ∃ certificate, verify (c,certificate) := by
  have h := nonhalting_reduction_all_n n hn
  have hp := nonhalting_reduction_nonnegative_all_n n hn
  exact ⟨complete_of_nonhalting_reduction (realization_complement_re n) h,
    complete_of_nonhalting_reduction (nonnegative_realization_complement_re n) hp,
    not_computable_of_nonhalting_reduction h,
    not_computable_of_nonhalting_reduction hp,no_finite_certificates h⟩

/-- Theorem 4.3 combines an exact coefficient program on all rational input
data with the rational quadratic section and its full real-parameter meaning. -/
theorem theorem_4_3_fixed_dimensions (s m : ℕ) (hs : 0 < s) :
    (∃ emit : AutomatonCoding.InputCode s m → ArrayCode (GeneralLocus.numberOfBodies s m) 3,
      Primrec emit ∧ ∀ x, rationalDecode (emit x) = RationalReduction.rationalArray
        (AutomatonCoding.data x.1) (AutomatonCoding.initial x) (AutomatonCoding.cutpoint x)) ∧
    (∀ A : AutomatonMoments.RationalData s m,
      (∀ a : MultiIndex (GeneralLocus.numberOfBodies s m) 3,
        (RationalReduction.coefficientSymbol A a).totalDegree ≤ 2) ∧
      (∀ p : Fin m → ℝ, AutomatonWords.ProbabilityRow p →
        ∀ theta : ℝ, 0 < theta → theta < 1 →
          (RationalReduction.coefficientMap A p theta ∈
            VolumeLocus (GeneralLocus.numberOfBodies s m) 3 ↔
              A.toReal.UniversalCutpoint p theta))) :=
  ⟨AutomatonCoding.theorem_4_3_algorithm s m,fun A => RationalReduction.theorem_4_3 A hs⟩

/-- The complete dimension-uniform form of Theorem 4.3. There is one specified
partial recursive program; it terminates for every representation of every
valid rational automaton in every dimension. Its entire output is the same
rational quadratic map whose full real-parameter semantics is given here. -/
theorem theorem_4_3 :
    Partrec UniformEncoding.program ∧
    (∀ (s m : ℕ) (A : AutomatonMoments.RationalData s m)
      (p : Fin m → ℚ) (theta : ℚ),
      ∃ c : Represented.Code UniformEncoding.Input,
        Represented.decode c = UniformEncoding.encodeInput A p theta) ∧
    (∀ (s m : ℕ) (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
      (p : Fin m → ℚ) (theta : ℚ) (c : Represented.Code UniformEncoding.Input),
      Represented.decode c = UniformEncoding.encodeInput A p theta →
        (UniformEncoding.program c).Dom ∧
        ∀ result ∈ UniformEncoding.program c,
          (Represented.decode result).1 = GeneralLocus.numberOfBodies s m ∧
          (Represented.decode result).2.length =
            RationalExtraction.interpolationSize (GeneralLocus.numberOfBodies s m) 3 ∧
          UniformEncoding.decodedArray (GeneralLocus.numberOfBodies s m) result =
            UniformQuadratic.coefficientMap A (fun j => (p j : ℝ)) (theta : ℝ)) ∧
    (∀ (s m : ℕ) (A : AutomatonMoments.RationalData s m) (hs : 0 < s),
      (∀ a : MultiIndex (GeneralLocus.numberOfBodies s m) 3,
        (UniformQuadratic.coefficientSymbol A a).totalDegree ≤ 2) ∧
      (∀ p : Fin m → ℝ, AutomatonWords.ProbabilityRow p →
        ∀ theta : ℝ, 0 < theta → theta < 1 →
          (UniformQuadratic.coefficientMap A p theta ∈
            VolumeLocus (GeneralLocus.numberOfBodies s m) 3 ↔
              A.toReal.UniversalCutpoint p theta))) := by
  refine ⟨UniformEncoding.program_partrec,?_,?_,?_⟩
  · intro s m A p theta
    exact UniformEncoding.input_coverage A p theta
  · intro s m A hs p theta c hc
    refine ⟨UniformEncoding.program_terminates A hs p theta c hc,?_⟩
    intro result hr
    have h := UniformEncoding.program_correct A hs p theta c hc result hr
    exact ⟨h.1,h.2.1,UniformQuadratic.program_matches_map A hs p theta c hc result hr⟩
  · intro s m A hs
    exact ⟨UniformQuadratic.coefficientSymbol_degree_le_two A,
      fun p hp theta h₀ h₁ => UniformQuadratic.coefficientMap_membership A hs p hp theta h₀ h₁⟩

end MixedVolume.MainResults

end
end -- original EOF section
end -- component scope
/- END SOURCE: MixedVolume/MainTheorems.lean -/

end -- former unit scope
/- END FORMER UNIT: MixedVolume.MainResultsAll -/

/- Supplementary endpoint inspection for the full development proof pass.

Append after the unchanged VerificationAll body, with the source correspondence
and this suffix separately hashed. These are the stock Lean inspection commands.
They add no mathematical declarations and do not replace the private-body audit.
The resulting log is evidence only if the complete compiler invocation succeeds.
-/

#check MixedVolume.MainResults.theorem_1_1
#print axioms MixedVolume.MainResults.theorem_1_1

#check MixedVolume.MainResults.theorem_1_1_all_n
#print axioms MixedVolume.MainResults.theorem_1_1_all_n

#check MixedVolume.MainResults.theorem_4_3
#print axioms MixedVolume.MainResults.theorem_4_3

#check MixedVolume.FixedSection.corollary_5_1_exists
#print axioms MixedVolume.FixedSection.corollary_5_1_exists

#check MixedVolume.ScalarSection.theorem_6_1
#print axioms MixedVolume.ScalarSection.theorem_6_1

#check MixedVolume.ScalarSection.theorem_6_1_all_n
#print axioms MixedVolume.ScalarSection.theorem_6_1_all_n

#check MixedVolume.ThreeStateSection.theorem_6_1_literal_section
#print axioms MixedVolume.ThreeStateSection.theorem_6_1_literal_section

/- Independently check the intended real-parameter domain: the probability
and open-cutoff hypotheses are explicit binders outside the equivalence. -/
#check (show ∀ (s m : ℕ)
    (A : MixedVolume.AutomatonMoments.RationalData s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : MixedVolume.AutomatonWords.ProbabilityRow p)
    (theta : ℝ) (h0 : 0 < theta) (h1 : theta < 1),
    (MixedVolume.UniformQuadratic.coefficientMap A p theta ∈
        VolumePolynomials.VolumeLocus (MixedVolume.GeneralLocus.numberOfBodies s m) 3 ↔
      MixedVolume.AutomatonWords.Data.UniversalCutpoint
        (MixedVolume.AutomatonMoments.RationalData.toReal A) p theta)
  from fun s m A hs p hp theta h0 h1 =>
    (MixedVolume.MainResults.theorem_4_3.2.2.2 s m A hs).2 p hp theta h0 h1)
