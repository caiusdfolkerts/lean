module

public import main
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import projection_boundary
public import projection_core
public import projection_escape
public import rank_three_algebra

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


@[expose] public section

set_option Elab.async false
set_option debug.skipKernelTC false

/-!
# Additional statements and examples from the paper

These sections verify the displayed hexagon matrix and its signature,
the full-dimensionality conclusion of Lemma 2.1 through Hlawka's
inequality, the strict-density assertion, the seminorm and circle
statements of Lemmas 3.1 and 5.1, the dimension-zero convention,
and compatibility under positivity on the two boundary quartets.

Generated from the exact inputs in `assembly/additions/`.
The source correspondence is in `audit/additional-source-map.json`.
Regenerate with `python3 scripts/assemble_additions.py`.
-/

/-! ## 1. Hexagon -/

section Source_Hexagon

@[expose] public section

/-!
# The matrix in the paper's introduction

This example connects the general obstruction to the explicit five-by-five
matrix on page 2. Its entries, positivity, and exact rank are checked here;
the geometric nonapproximation conclusion then follows from Theorem 1.1.

The two short rank certificates have complementary roles. A factorization
through a three-dimensional space gives the upper bound. The first three
coordinates have determinant six, giving the lower bound.
-/

noncomputable section

open Matrix Set
open scoped Topology BigOperators

namespace ProjectionAreaExamples

open ProjectionAreaRankThree ProjectionAreaTopology ProjectionAreaPaper

/-- Squared distances between five consecutive vertices of a regular hexagon
of circumradius one, exactly as displayed in the introduction. -/
def hexagonMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 3, 4, 3;
     1, 0, 1, 3, 4;
     3, 1, 0, 1, 3;
     4, 3, 1, 0, 1;
     3, 4, 3, 1, 0]

private def hexagonLeft : Matrix (Fin 5) (Fin 3) ℝ :=
  !![1,  2,  0;
     1,  1,  1;
     1, -1,  1;
     1, -2,  0;
     1, -1, -1]

private def hexagonRight : Matrix (Fin 3) (Fin 5) ℝ :=
  !![2, 2, 2, 2, 2;
     -1, -(1 / 2), 1 / 2, 1, 1 / 2;
     0, -(3 / 2), -(3 / 2), 0, 3 / 2]

/-- The five vertices, with their ordinary Euclidean coordinates. -/
def hexagonPoint (i : Fin 5) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![![2, 1, -1, -2, -1] i / 2,
    Real.sqrt 3 * ![0, 1, 1, 0, -1] i / 2]

/-- Every displayed vertex lies on the circle of radius one about the origin. -/
theorem hexagonPoint_norm (i : Fin 5) : ‖hexagonPoint i‖ = 1 := by
  have hsq : ‖hexagonPoint i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;>
      norm_num [hexagonPoint, Fin.sum_univ_two, div_pow]
  nlinarith [norm_nonneg (hexagonPoint i)]

/-- The matrix entries are exactly the squared Euclidean distances of these
five concrete points, without rounding or a numerical eigenvalue calculation. -/
theorem hexagonMatrix_eq_sq_dist (i j : Fin 5) :
    hexagonMatrix i j = dist (hexagonPoint i) (hexagonPoint j) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  fin_cases i <;> fin_cases j <;>
    norm_num [hexagonMatrix, hexagonPoint, Fin.sum_univ_two, div_pow] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem hexagon_factorization :
    hexagonMatrix = hexagonLeft * hexagonRight := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hexagonMatrix, hexagonLeft, hexagonRight,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The matrix is positive off the diagonal, symmetric, and hollow. -/
def hexagon : PositiveHollowMatrix 5 where
  entries := hexagonMatrix
  hollow := by
    intro i
    fin_cases i <;> norm_num [hexagonMatrix]
  symmetric := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [hexagonMatrix]
  positive := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [hexagonMatrix] at *

/-- The points are distinct, as witnessed by the positive off-diagonal entries. -/
theorem hexagonPoint_injective : Function.Injective hexagonPoint := by
  intro i j hij
  by_contra hne
  have hp := hexagon.positive i j hne
  change 0 < hexagonMatrix i j at hp
  rw [hexagonMatrix_eq_sq_dist, hij, dist_self, zero_pow (by decide : 2 ≠ 0)] at hp
  exact (lt_irrefl 0) hp

/-- Exact rank, rather than only a numerical rank computation. -/
theorem hexagon_rank : hexagonMatrix.rank = 3 := by
  apply Nat.le_antisymm
  · rw [hexagon_factorization]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · let σ : Fin 3 → Fin 5 := ![0, 1, 2]
    have hdet : (hexagonMatrix.submatrix σ σ).det = 6 := by
      norm_num [hexagonMatrix, σ, Matrix.submatrix, Matrix.det_fin_three]
    have hrank : (hexagonMatrix.submatrix σ σ).rank = 3 := by
      simpa using Matrix.rank_of_det_ne_zero
        (A := hexagonMatrix.submatrix σ σ) (by rw [hdet]; norm_num)
    rw [← hrank]
    exact Matrix.rank_submatrix_le _ σ σ

/-- No sequence of compact convex bodies can have projection-area arrays
converging to the displayed matrix, although every four-coordinate
restriction has an exact realization. -/
theorem hexagon_obstruction :
    hexagonMatrix ∉ closure (realizationLocus 5) ∧
      ∀ σ : Fin 4 → Fin 5, Function.Injective σ →
        hexagonMatrix.submatrix σ σ ∈ realizationLocus 4 := by
  exact positive_rank_three_obstruction hexagon (by decide) hexagon_rank

/-- The escape obstruction also applies to nonnegative weight vectors
whose coordinates are allowed to vanish. -/
theorem hexagon_has_no_escape_weights :
    hexagonMatrix ∉ ProjectionAreaEscape.EscapeCone 5 := by
  exact positive_rank_le_three_not_in_escapeCone hexagon (by decide)
    hexagon_rank.le

/-- The exact quadratic form of the displayed matrix, using the two vectors
from its rank-three factorization in the introduction. -/
theorem hexagon_quadratic_form (x : Fin 5 → ℝ) :
    dotProduct x (hexagonMatrix.mulVec x) =
      2 * (∑ i, x i) ^ 2 - (2 * x 0 + x 1 - x 2 - 2 * x 3 - x 4) ^ 2 / 2 -
        3 * (x 1 + x 2 - x 4) ^ 2 / 2 := by
  norm_num [hexagonMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The signature asserted for the introductory example: one positive,
two negative, and two zero eigenvalues, counted with their actual Mathlib
spectral multiplicities. -/
theorem hexagon_signature :
    ∃ hQ : hexagonMatrix.IsHermitian,
      (Finset.univ.filter (fun i => 0 < hQ.eigenvalues i)).card = 1 ∧
      (Finset.univ.filter (fun i => hQ.eigenvalues i < 0)).card = 2 ∧
      (Finset.univ.filter (fun i => hQ.eigenvalues i = 0)).card = 2 := by
  classical
  have hQ : hexagonMatrix.IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr
      (Matrix.IsSymm.ext (fun i j => hexagon.symmetric j i))
  have hnonpos (x : Fin 5 → ℝ)
      (hs : ProjectionAreaStrict.sumFunctional x = 0) :
      dotProduct x (hexagonMatrix.mulVec x) ≤ 0 := by
    change (∑ i, x i) = 0 at hs
    rw [hexagon_quadratic_form, hs]
    nlinarith [sq_nonneg (2 * x 0 + x 1 - x 2 - 2 * x 3 - x 4),
      sq_nonneg (x 1 + x 2 - x 4)]
  have hpos_le := ProjectionAreaEigenvalues.positive_eigenvalue_count_le_one
    hexagonMatrix hQ ProjectionAreaStrict.sumFunctional hnonpos
  have htrace : hexagonMatrix.trace = 0 := by
    norm_num [Matrix.trace, hexagonMatrix, Fin.sum_univ_succ]
  have hsum : ∑ i, hQ.eigenvalues i = 0 := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using
      hQ.trace_eq_sum_eigenvalues.symm.trans htrace
  have hex : ∃ i, 0 < hQ.eigenvalues i := by
    by_contra! hn
    have hz : hQ.eigenvalues = 0 := by
      funext i
      exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hn j)).mp hsum i
        (Finset.mem_univ i)
    have hmatrix := hQ.eigenvalues_eq_zero_iff.mp hz
    have hentry := congrFun (congrFun hmatrix 0) 1
    norm_num [hexagonMatrix] at hentry
  have hpos : (Finset.univ.filter (fun i => 0 < hQ.eigenvalues i)).card = 1 := by
    apply Nat.le_antisymm hpos_le
    obtain ⟨i, hi⟩ := hex
    exact Finset.one_le_card.mpr ⟨i, by simp [hi]⟩
  have hnonzero : (Finset.univ.filter (fun i => hQ.eigenvalues i ≠ 0)).card = 3 := by
    have h := hQ.rank_eq_card_non_zero_eigs
    rw [hexagon_rank, Fintype.card_subtype] at h
    exact h.symm
  have hpos_filter :
      ((Finset.univ.filter (fun i => hQ.eigenvalues i ≠ 0)).filter
        (fun i => 0 < hQ.eigenvalues i)) =
      Finset.univ.filter (fun i => 0 < hQ.eigenvalues i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun hi => ⟨ne_of_gt hi, hi⟩⟩
  have hneg_filter :
      ((Finset.univ.filter (fun i => hQ.eigenvalues i ≠ 0)).filter
        (fun i => ¬ 0 < hQ.eigenvalues i)) =
      Finset.univ.filter (fun i => hQ.eigenvalues i < 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    constructor
    · rintro ⟨hne, hle⟩
      exact lt_of_le_of_ne hle hne
    · intro hlt
      exact ⟨ne_of_lt hlt, hlt.le⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i => hQ.eigenvalues i ≠ 0))
    (fun i => 0 < hQ.eigenvalues i)
  rw [hpos_filter, hneg_filter, hpos, hnonzero] at hsplit
  have hneg : (Finset.univ.filter (fun i => hQ.eigenvalues i < 0)).card = 2 := by
    omega
  have hsplit_zero := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 5))) (fun i => hQ.eigenvalues i = 0)
  rw [hnonzero] at hsplit_zero
  have hzero : (Finset.univ.filter (fun i => hQ.eigenvalues i = 0)).card = 2 := by
    simpa using Nat.add_right_cancel (by simpa using hsplit_zero :
      (Finset.univ.filter (fun i => hQ.eigenvalues i = 0)).card + 3 = 2 + 3)
  exact ⟨hQ, hpos, hneg, hzero⟩

end ProjectionAreaExamples

#print axioms ProjectionAreaExamples.hexagon_rank
#print axioms ProjectionAreaExamples.hexagonPoint_norm
#print axioms ProjectionAreaExamples.hexagonMatrix_eq_sq_dist
#print axioms ProjectionAreaExamples.hexagonPoint_injective
#print axioms ProjectionAreaExamples.hexagon_obstruction
#print axioms ProjectionAreaExamples.hexagon_has_no_escape_weights

#print axioms ProjectionAreaExamples.hexagon_signature

end
end
end Source_Hexagon

/-! ## 2. Hlawka -/

section Source_Hlawka

@[expose] public section

/-!
# Hlawka's inequality for the mixed-volume brightness functional

For a compact convex body `L` in three dimensions, the functional
`brightness L v = 3 V([0,v], L, L)` is nonnegative and even, obeys Hlawka's
inequality, and is positive away from zero when `L` has nonempty interior.

The proof of Hlawka uses an actual inclusion between Minkowski sums of
segments. Its support-function inequality is the scalar Hlawka inequality
written with positive parts. Positivity uses the already verified strict
monotonicity consequence of Alexandrov–Fenchel.
-/

noncomputable section

open Set MeasureTheory
open scoped Pointwise
open VolumePolynomials
open ProjectionAreaMixedGeometry

namespace ProjectionAreaBrightness

abbrev ThreeSpace := ProjectionAreaMixedGeometry.V 3
abbrev ThreeBody := ProjectionAreaMixedGeometry.Body 3

/-- The actual mixed-volume brightness functional. -/
def brightness (L : ThreeBody) (v : ThreeSpace) : ℝ :=
  3 * ProjectionAreaMixedGeometry.mixed3 (segmentBody 0 v) L L

theorem mixed3_add_first (A B C D : ThreeBody) :
    mixed3 (A + B) C D = mixed3 A C D + mixed3 B C D := by
  simpa only [mixed3, Matrix.vecCons, Fin.update_cons_zero] using
    mixedVolume_add volume ![A, C, D] 0 A B

theorem mixed3_translate_first (A B C : ThreeBody) (p : ThreeSpace) :
    mixed3 (translateBody p A) B C = mixed3 A B C := by
  have h := mixedVolume_translate volume ![A, B, C] ![p, 0, 0]
  have he : (fun i : Fin 3 => translateBody (![p, 0, 0] i) (![A, B, C] i)) =
      ![translateBody p A, B, C] := by
    funext i
    fin_cases i <;> simp
  simpa only [mixed3, he] using h

theorem brightness_nonneg (L : ThreeBody) (v : ThreeSpace) :
    0 ≤ brightness L v := by
  exact mul_nonneg (by norm_num)
    (mixedVolume_nonnegative volume ![segmentBody 0 v, L, L])

@[simp]
theorem brightness_zero (L : ThreeBody) : brightness L 0 = 0 := by
  have hsegment : segmentBody (0 : ThreeSpace) 0 = 0 := by
    apply ConvexBody.ext
    change segment ℝ (0 : ThreeSpace) 0 = {0}
    simp
  have hmixed : mixed3 (0 : ThreeBody) L L = 0 := by
    simpa only [mixed3, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_zero_arg volume ![(0 : ThreeBody), L, L] (0 : Fin 3)
  rw [brightness, hsegment, hmixed, mul_zero]

theorem brightness_neg (L : ThreeBody) (v : ThreeSpace) :
    brightness L (-v) = brightness L v := by
  have hsegment : segmentBody (0 : ThreeSpace) (-v) =
      translateBody (-v) (segmentBody 0 v) := by
    rw [translate_segmentBody, add_zero, neg_add_cancel]
    apply ConvexBody.ext
    exact segment_symm ℝ 0 (-v)
  rw [brightness, brightness, hsegment, mixed3_translate_first]

theorem body_support_add (A B : ThreeBody) (f : ThreeSpace →L[ℝ] ℝ) :
    BodySupport.support (A + B) f = BodySupport.support A f + BodySupport.support B f := by
  change OAI.Paper092.SupportGeometry.support ((A : Set ThreeSpace) + (B : Set ThreeSpace)) f =
    OAI.Paper092.SupportGeometry.support (A : Set ThreeSpace) f +
      OAI.Paper092.SupportGeometry.support (B : Set ThreeSpace) f
  exact OAI.Paper092.SupportGeometry.support_add A.isCompact A.nonempty
    B.isCompact B.nonempty f

theorem body_support_segment (v : ThreeSpace) (f : ThreeSpace →L[ℝ] ℝ) :
    BodySupport.support (segmentBody 0 v) f = max 0 (f v) := by
  change OAI.Paper092.SupportGeometry.support (segment ℝ (0 : ThreeSpace) v) f = _
  rw [OAI.Paper092.SupportGeometry.support_segment, map_zero]

set_option maxHeartbeats 800000 in
/-- Scalar Hlawka in positive-part form. The affine terms cancel when
`max 0 x` is expressed as `(x + |x|) / 2`. -/
private theorem positive_part_hlawka (a b c : ℝ) :
    max 0 (a + b) + max 0 (b + c) + max 0 (c + a) ≤
      max 0 a + max 0 b + max 0 c + max 0 (a + b + c) := by
  simp only [max_def]
  split_ifs <;> linarith

/-- The Minkowski-sum inclusion underlying Hlawka's inequality. -/
theorem segment_hlawka_inclusion (r s t : ThreeSpace) :
    segmentBody 0 (r + s) + segmentBody 0 (s + t) + segmentBody 0 (t + r) ≤
      segmentBody 0 r + segmentBody 0 s + segmentBody 0 t + segmentBody 0 (r + s + t) := by
  intro x hx
  apply (BodySupport.mem_iff_le_support _).mpr
  intro f
  apply (BodySupport.le_support _ f hx).trans
  simp only [body_support_add, body_support_segment, map_add]
  exact positive_part_hlawka (f r) (f s) (f t)

/-- Hlawka's inequality for actual mixed volumes of arbitrary compact convex
bodies. No interior or smoothness hypothesis is needed for this inequality. -/
theorem brightness_hlawka (L : ThreeBody) (r s t : ThreeSpace) :
    brightness L (r + s) + brightness L (s + t) + brightness L (t + r) ≤
      brightness L r + brightness L s + brightness L t + brightness L (r + s + t) := by
  have h := mixed3_mono_first _ _ L L (segment_hlawka_inclusion r s t)
  simp only [mixed3_add_first] at h
  dsimp only [brightness]
  linarith

/-- Full dimension makes the brightness functional positive in every nonzero
direction. Equality in the first mixed-volume monotonicity statement would
force `L + [0,v] = L`, whose support functions force `v = 0`. -/
theorem brightness_pos (L : ThreeBody)
    (hint : (interior (L : Set ThreeSpace)).Nonempty)
    (v : ThreeSpace) (hv : v ≠ 0) : 0 < brightness L v := by
  by_contra hpos
  have hnonpos : brightness L v ≤ 0 := le_of_not_gt hpos
  have hmixed : mixed3 (segmentBody 0 v) L L = 0 := by
    have hnonneg := mixedVolume_nonnegative volume ![segmentBody 0 v, L, L]
    change 0 ≤ mixed3 (segmentBody 0 v) L L at hnonneg
    dsimp only [brightness] at hnonpos
    linarith
  have hcontain : L ≤ L + segmentBody 0 v := by
    intro x hx
    change x ∈ (L : Set ThreeSpace) + (segmentBody 0 v : Set ThreeSpace)
    exact ⟨x, hx, 0, left_mem_segment ℝ 0 v, add_zero x⟩
  have hequal : L + segmentBody 0 v = L := by
    apply equal_body_of_mixed3_first L (L + segmentBody 0 v) hcontain hint
    rw [mixed3_add_first, mixed3_diagonal, hmixed, add_zero]
  have hsupport (f : ThreeSpace →L[ℝ] ℝ) : max 0 (f v) = 0 := by
    have h := congrArg (fun B : ThreeBody => BodySupport.support B f) hequal
    rw [body_support_add, body_support_segment] at h
    linarith
  apply hv
  funext i
  have hp := hsupport (ContinuousLinearMap.proj i)
  have hn := hsupport (-ContinuousLinearMap.proj i)
  change max 0 (v i) = 0 at hp
  change max 0 (-v i) = 0 at hn
  have hle : v i ≤ 0 := (le_max_right 0 (v i)).trans hp.le
  have hge : -v i ≤ 0 := (le_max_right 0 (-v i)).trans hn.le
  change v i = 0
  linarith

/-- The six prescribed values arising from a rank-three boundary quartet
contradict Hlawka whenever the indicated remaining direction is nonzero. -/
theorem brightness_six_obstruction (L : ThreeBody)
    (hint : (interior (L : Set ThreeSpace)).Nonempty)
    (x y z : ThreeSpace) (a b : ℝ)
    (hx : brightness L x = a) (hy : brightness L y = b)
    (hz : brightness L z = a + b)
    (hzx : brightness L (z + x) = b)
    (hzy : brightness L (z - y) = a)
    (hxy : brightness L (x + y) = a + b)
    (hne : x - y + z ≠ 0) : False := by
  have h := brightness_hlawka L (z + x) (y - z) (-x)
  have h₁ : (z + x) + (y - z) = x + y := by abel
  have h₂ : (y - z) + -x = -(x - y + z) := by abel
  have h₃ : -x + (z + x) = z := by abel
  have h₄ : (z + x) + (y - z) + -x = y := by abel
  have h₅ : y - z = -(z - y) := by abel
  rw [h₄, h₁, h₂, h₃, h₅] at h
  simp only [brightness_neg, hx, hy, hz, hzx, hzy, hxy] at h
  have hpositive := brightness_pos L hint (x - y + z) hne
  linarith

end ProjectionAreaBrightness

#print axioms ProjectionAreaBrightness.brightness_hlawka
#print axioms ProjectionAreaBrightness.brightness_pos

end
end
end Source_Hlawka

/-! ## 3. BoundaryInterior -/

section Source_BoundaryInterior

@[expose] public section

/-!
# Full dimension of a positive boundary quartet

This optional development establishes the literal full-dimensionality
assertion of Lemma 2.1. A putative affine relation has no zero coefficient.
After a coordinatewise affine change it is the relation `∑ i, x i = 0`.
The six projected areas are then values of the genuine three-dimensional
mixed-volume brightness functional. Their rank-three equalities violate
Hlawka's inequality and strict positivity.
-/

noncomputable section

open Set MeasureTheory Matrix Module
open scoped BigOperators Pointwise
open VolumePolynomials (segmentBody coe_segmentBody map_segmentBody mapBody coe_mapBody
  mixedVolume mixedVolume_diagonal mixedVolume_map_linear)
open ProjectionAreaRankThree ProjectionAreaBoundaryKernel
open ProjectionAreaMixedGeometry ProjectionAreaTransforms
open ProjectionAreaBrightness

namespace ProjectionAreaFullInterior

/-- A relation with equal absolute coefficients forces opposite entries of
a positive boundary quartet to agree. One of the resulting three entries
is the sum of the other two. -/
theorem opposite_equalities_of_relationBounds_one (P : PositiveHollowMatrix 4)
    (hrank : P.entries.rank ≤ 3)
    (h : RelationBounds P.entries (fun _ => 1)) :
    P.entries 0 1 = P.entries 2 3 ∧
    P.entries 0 2 = P.entries 1 3 ∧
    P.entries 0 3 = P.entries 1 2 ∧
    (P.entries 0 1 = P.entries 0 2 + P.entries 0 3 ∨
      P.entries 0 2 = P.entries 0 1 + P.entries 0 3 ∨
      P.entries 0 3 = P.entries 0 1 + P.entries 0 2) := by
  let a := P.entries 0 1
  let b := P.entries 0 2
  let c := P.entries 0 3
  let d := P.entries 1 2
  let e := P.entries 1 3
  let f := P.entries 2 3
  have ha : 0 < a := P.positive 0 1 (by decide)
  have hb : 0 < b := P.positive 0 2 (by decide)
  have hc : 0 < c := P.positive 0 3 (by decide)
  have hd : 0 < d := P.positive 1 2 (by decide)
  have he : 0 < e := P.positive 1 3 (by decide)
  have hf : 0 < f := P.positive 2 3 (by decide)
  have hmat : P.entries = hollowMatrix4 a b c d e f := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hollowMatrix4, a, b, c, d, e, f, P.hollow]
    all_goals exact P.symmetric _ _
  let A := Real.sqrt (a * f)
  let B := Real.sqrt (b * e)
  let C := Real.sqrt (c * d)
  have hboundary : ∃ k, BoundaryEquality A B C k := by
    rcases P.four_root_boundary hrank 0 1 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) with hh | hh | hh
    · exact ⟨0, hh⟩
    · exact ⟨1, hh⟩
    · exact ⟨2, hh⟩
  obtain ⟨k, hk⟩ := hboundary
  obtain ⟨s, hs, h01, h02, h03, h12, h13, h23⟩ :=
    ProjectionAreaPositiveDiagonal.normalize_positive_six_areas a b c d e f ha hb hc hd he hf
  have hscaled : (fun i j : Fin 4 => s i * s j * P.entries i j) =
      hollowMatrix4 A B C C B A := by
    rw [hmat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hollowMatrix4] <;>
      dsimp [A, B, C] <;> nlinarith only [h01, h02, h03, h12, h13, h23]
  have hbounds := relationBounds_diagonal_scale P.entries (fun _ => 1) s hs h
  rw [hscaled] at hbounds
  have hueq := normalized_relationBounds_equal A B C
    (Real.sqrt_pos.mpr (mul_pos ha hf)) (Real.sqrt_pos.mpr (mul_pos hb he))
    (Real.sqrt_pos.mpr (mul_pos hc hd)) k hk (fun i => 1 / s i) hbounds
  have hse (i : Fin 4) : s i = s 0 := by
    simpa only [one_div, _root_.inv_inj] using hueq i
  have hs0 : s 0 * s 0 ≠ 0 := mul_ne_zero (hs 0).ne' (hs 0).ne'
  have haf : a = f := by
    apply mul_left_cancel₀ hs0
    simpa only [hse] using h01.trans h23.symm
  have hbe : b = e := by
    apply mul_left_cancel₀ hs0
    simpa only [hse] using h02.trans h13.symm
  have hcd : c = d := by
    apply mul_left_cancel₀ hs0
    simpa only [hse] using h03.trans h12.symm
  refine ⟨haf, hbe, hcd, ?_⟩
  have hA : A = a := by dsimp [A]; rw [← haf, Real.sqrt_mul_self ha.le]
  have hB : B = b := by dsimp [B]; rw [← hbe, Real.sqrt_mul_self hb.le]
  have hC : C = c := by dsimp [C]; rw [← hcd, Real.sqrt_mul_self hc.le]
  fin_cases k
  · exact Or.inl (by simpa [BoundaryEquality, hA, hB, hC, a, b, c] using hk)
  · exact Or.inr (Or.inl (by simpa [BoundaryEquality, hA, hB, hC, a, b, c] using hk))
  · exact Or.inr (Or.inr (by simpa [BoundaryEquality, hA, hB, hC, a, b, c] using hk))

/-- The standard graph of the coordinate-sum-zero hyperplane. -/
def graphLinear : V 3 →ₗ[ℝ] V 4 where
  toFun x := ![x 0, x 1, x 2, -x 0 - x 1 - x 2]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

def graphMap : V 3 →L[ℝ] V 4 := graphLinear.toContinuousLinearMap

def graphBody (L : Body 3) : Body 4 := mapBody graphMap L

theorem graph_delete (x : V 3) : deleteCoord (3 : Fin 4) (graphMap x) = x := by
  ext i
  fin_cases i <;> simp [deleteCoord, graphMap, graphLinear, Fin.succAbove]

theorem graph_of_sum_zero (x : V 4) (hx : ∑ i, x i = 0) :
    graphMap (deleteCoord (3 : Fin 4) x) = x := by
  have hs : x 0 + x 1 + x 2 + x 3 = 0 := by
    simpa only [Fin.sum_univ_four] using hx
  ext i
  fin_cases i <;> simp [deleteCoord, graphMap, graphLinear, Fin.succAbove] <;> linarith

theorem graphBody_delete (K : Body 4) (hK : ∀ x ∈ K, ∑ i, x i = 0) :
    graphBody (deleteBody (3 : Fin 4) K) = K := by
  apply ConvexBody.ext
  change graphMap '' (deleteCoord 3 '' (K : Set (V 4))) = (K : Set (V 4))
  rw [Set.image_image]
  apply Set.ext
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [graph_of_sum_zero y (hK y hy)] using hy
  · intro hx
    exact ⟨x, hx, graph_of_sum_zero x (hK x hx)⟩

/-- Standard coordinate directions in the three-dimensional graph domain. -/
def axis (i : Fin 3) : V 3 := Pi.single i 1

theorem coordinateSegment_eq_segmentBody (i : Fin 3) :
    ProjectionAreaMixedGeometry.coordinateSegment i = segmentBody 0 (axis i) := by
  apply ConvexBody.ext
  rw [ProjectionAreaMixedGeometry.coe_coordinateSegment, coe_segmentBody, segment_eq_image]
  congr 1
  funext s
  ext j
  by_cases h : i = j
  · subst j; simp [axis]
  · simp [axis, Pi.single_apply, h, Ne.symm h]

theorem brightness_coordinate (L : Body 3) (i : Fin 3) :
    brightness L (axis i) = volume.real (deleteBody i L : Set (V 2)) := by
  have h := mixedVolume_coordinateSegment i ![L, L]
  have he : (fun r => deleteBody i ((![L, L] : Fin 2 → Body 3) r)) =
      (fun _ : Fin 2 => deleteBody i L) := by
    funext r
    fin_cases r <;> rfl
  rw [he, mixedVolume_diagonal volume (finrank_fin_fun ℝ)] at h
  norm_num only at h
  simpa only [brightness, mixed3, Matrix.vecCons, coordinateSegment_eq_segmentBody] using h

theorem brightness_map (L : Body 3) (F : V 3 →L[ℝ] V 3) (v : V 3) :
    brightness (mapBody F L) (F v) =
      |LinearMap.det F.toLinearMap| * brightness L v := by
  have h := mixedVolume_map_linear volume F ![segmentBody 0 v, L, L]
  have he : (fun i : Fin 3 => mapBody F ((![segmentBody 0 v, L, L] : Fin 3 → Body 3) i)) =
      ![segmentBody 0 (F v), mapBody F L, mapBody F L] := by
    funext i
    fin_cases i <;> simp [map_segmentBody]
  rw [he] at h
  dsimp only [brightness, mixed3]
  rw [h]
  ring

/-- The six coordinate pairs, in the usual upper-triangular order. -/
def pairLeft : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
def pairRight : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- Each frame has determinant of absolute value one; its first two
coordinates are the corresponding projection of `graphMap`. -/
def frameMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℝ :=
  ![!![1, 0, 0; 0, 1, 0; 0, 0, 1],
    !![1, 0, 0; 0, 0, 1; 0, 1, 0],
    !![1, 0, 0; -1, -1, -1; 0, 1, 0],
    !![0, 1, 0; 0, 0, 1; 1, 0, 0],
    !![0, 1, 0; -1, -1, -1; 1, 0, 0],
    !![0, 0, 1; -1, -1, -1; 1, 0, 0]]

def frameMap (k : Fin 6) : V 3 →L[ℝ] V 3 :=
  (Matrix.toLin' (frameMatrix k)).toContinuousLinearMap

def projectionDirection : Fin 6 → V 3 :=
  ![axis 2, axis 1, axis 1 - axis 2, axis 0, axis 0 - axis 2, axis 0 - axis 1]

theorem frame_det (k : Fin 6) : |LinearMap.det (frameMap k).toLinearMap| = 1 := by
  fin_cases k <;>
    norm_num [frameMap, frameMatrix, LinearMap.det_toLin', Matrix.det_fin_three]

theorem frame_direction (k : Fin 6) : frameMap k (projectionDirection k) = axis 2 := by
  ext i
  fin_cases k <;> fin_cases i <;>
    norm_num [frameMap, frameMatrix, projectionDirection, axis, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply]

theorem frame_projection (k : Fin 6) (x : V 3) :
    deleteCoord (2 : Fin 3) (frameMap k x) =
      projectN (pairLeft k) (pairRight k) (graphMap x) := by
  ext i
  fin_cases k <;> fin_cases i <;>
    simp [frameMap, frameMatrix, pairLeft, pairRight, deleteCoord, Fin.succAbove,
      graphMap, graphLinear, projectN, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three] <;> ring

/-- All six projection areas of the graph body are literal values of the
mixed-volume brightness functional, with no unspecified scale factors. -/
theorem graph_area_brightness (L : Body 3) (k : Fin 6) :
    coordinateAreaMatrix (graphBody L) (pairLeft k) (pairRight k) =
      brightness L (projectionDirection k) := by
  have h := brightness_map L (frameMap k) (projectionDirection k)
  rw [frame_direction, frame_det, one_mul, brightness_coordinate] at h
  have he : (deleteBody (2 : Fin 3) (mapBody (frameMap k) L) : Set (V 2)) =
      projectN (pairLeft k) (pairRight k) '' (graphBody L : Set (V 4)) := by
    simp only [deleteBody, graphBody, coe_mapBody, Set.image_image]
    congr 1
    funext x
    exact frame_projection k x
  rw [he] at h
  exact h

/-- The graph of a full-dimensional three-dimensional body cannot have a
positive area matrix of rank at most three. -/
theorem no_positive_boundary_sum_zero (K : Body 4)
    (hpositive : ∀ i j, i ≠ j → 0 < coordinateAreaMatrix K i j)
    (hrank : (coordinateAreaMatrix K).rank ≤ 3)
    (hsum : ∀ x ∈ K, ∑ i, x i = 0) : False := by
  let L := deleteBody (3 : Fin 4) K
  have hL : (interior (L : Set (V 3))).Nonempty :=
    triple_projection_interior K hpositive hrank 3
  have hgraph : graphBody L = K := graphBody_delete K hsum
  let P : PositiveHollowMatrix 4 :=
    ⟨coordinateAreaMatrix K, coordinateAreaMatrix_hollow K,
      coordinateAreaMatrix_symmetric K, hpositive⟩
  have hbounds : RelationBounds P.entries (fun _ => 1) := by
    simpa only [abs_one] using relationBounds_of_affine_relation K (fun _ => 1) 0
      (by simpa only [one_mul] using hsum)
  obtain ⟨hoppA, hoppB, hoppC, hsumABC⟩ :=
    opposite_equalities_of_relationBounds_one P hrank hbounds
  let A := coordinateAreaMatrix K 0 1
  let B := coordinateAreaMatrix K 0 2
  let C := coordinateAreaMatrix K 0 3
  have hbrightness (k : Fin 6) :
      coordinateAreaMatrix K (pairLeft k) (pairRight k) =
        brightness L (projectionDirection k) := by
    rw [← hgraph]
    exact graph_area_brightness L k
  have hA : brightness L (axis 2) = A := (hbrightness 0).symm
  have hB : brightness L (axis 1) = B := (hbrightness 1).symm
  have hC : brightness L (axis 1 - axis 2) = C := (hbrightness 2).symm
  have hC' : brightness L (axis 0) = C := (hbrightness 3).symm.trans hoppC.symm
  have hB' : brightness L (axis 0 - axis 2) = B := (hbrightness 4).symm.trans hoppB.symm
  have hA' : brightness L (axis 0 - axis 1) = A := (hbrightness 5).symm.trans hoppA.symm
  have hreverse (x y : V 3) : brightness L (y - x) = brightness L (x - y) := by
    rw [show y - x = -(x - y) by abel, brightness_neg]
  change A = B + C ∨ B = A + C ∨ C = A + B at hsumABC
  rcases hsumABC with he | he | he
  · apply brightness_six_obstruction L hL (-axis 1) (axis 0) (axis 2) B C
    · simpa only [brightness_neg] using hB
    · exact hC'
    · exact hA.trans he
    · simpa only [sub_eq_add_neg] using (hreverse (axis 1) (axis 2)).trans hC
    · exact (hreverse (axis 0) (axis 2)).trans hB'
    · simpa only [sub_eq_add_neg, add_comm] using hA'.trans he
    · intro hz
      have hz0 := congrFun hz 0
      norm_num [axis, Pi.single_apply] at hz0
  · apply brightness_six_obstruction L hL (-axis 2) (axis 0) (axis 1) A C
    · simpa only [brightness_neg] using hA
    · exact hC'
    · exact hB.trans he
    · simpa only [sub_eq_add_neg] using hC
    · exact (hreverse (axis 0) (axis 1)).trans hA'
    · simpa only [sub_eq_add_neg, add_comm] using hB'.trans he
    · intro hz
      have hz0 := congrFun hz 0
      norm_num [axis, Pi.single_apply] at hz0
  · apply brightness_six_obstruction L hL (-axis 1) (axis 2) (axis 0) B A
    · simpa only [brightness_neg] using hB
    · exact hA
    · exact hC'.trans (he.trans (add_comm A B))
    · simpa only [sub_eq_add_neg] using hA'
    · exact hB'
    · simpa only [sub_eq_add_neg, add_comm] using
        ((hreverse (axis 1) (axis 2)).trans hC).trans (he.trans (add_comm A B))
    · intro hz
      have hz0 := congrFun hz 0
      norm_num [axis, Pi.single_apply] at hz0

/-- Actual coordinatewise affine image used to normalize a nontrivial
hyperplane relation. Negative coefficients are allowed. -/
def affineBody (K : Body 4) (p a : V 4) : Body 4 where
  carrier := ProjectionAreaRectangleObstruction.affineCoordinates p a '' (K : Set (V 4))
  convex' := K.convex.affine_image (ProjectionAreaRectangleObstruction.affineCoordinates p a)
  nonempty' := K.nonempty.image _
  isCompact' := K.isCompact.image
    (ProjectionAreaRectangleObstruction.continuous_affineCoordinates p a)

theorem coordinateAreaMatrix_affineBody (K : Body 4) (p a : V 4) :
    coordinateAreaMatrix (affineBody K p a) =
      ProjectionAreaReplication.replicateArray id (fun i => |a i|) (coordinateAreaMatrix K) := by
  ext i j
  change coordinateAreaMatrix (affineBody K p a) i j =
    |a i| * |a j| * coordinateAreaMatrix K i j
  rw [← pairArea_eq_coordinateAreaMatrix, ← pairArea_eq_coordinateAreaMatrix]
  change ProjectionAreaRectangleObstruction.pairArea
    (ProjectionAreaRectangleObstruction.affineCoordinates p a '' (K : Set (V 4))) i j = _
  rw [ProjectionAreaRectangleObstruction.pairArea_affineCoordinates]
  rw [abs_mul]

/-- Literal full-dimensionality conclusion of Lemma 2.1, expressed directly
using the actual six coordinate projection areas of the convex body. -/
theorem positive_boundary_interior (K : Body 4)
    (hpositive : ∀ i j, i ≠ j → 0 < coordinateAreaMatrix K i j)
    (hrank : (coordinateAreaMatrix K).rank ≤ 3) :
    (interior (K : Set (V 4))).Nonempty := by
  by_contra hint
  obtain ⟨f, hf, c, hc⟩ := exists_affine_relation_of_empty_interior K hint
  let a : V 4 := fun i => f (Pi.single i 1)
  have hrel : ∀ x ∈ K, ∑ i, a i * x i = c := by
    intro x hx
    rw [← linearForm_eq_sum_coordinates f x]
    exact hc x hx
  let P : PositiveHollowMatrix 4 :=
    ⟨coordinateAreaMatrix K, coordinateAreaMatrix_hollow K,
      coordinateAreaMatrix_symmetric K, hpositive⟩
  have hbounds : RelationBounds P.entries (fun i => |a i|) :=
    relationBounds_of_affine_relation K a c hrel
  have ha (i : Fin 4) : a i ≠ 0 := by
    intro hai
    have hzero := relationBounds_zero_of_one_zero P hrank (fun j => |a j|)
      hbounds i (by rw [hai, abs_zero])
    apply hf
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [linearForm_eq_sum_coordinates]
    apply Finset.sum_eq_zero
    intro j _
    have haj : a j = 0 := abs_eq_zero.mp (congrFun hzero j)
    exact mul_eq_zero_of_left haj _
  obtain ⟨p, hp⟩ := K.nonempty
  let G := affineBody K p a
  have hGpositive : ∀ i j, i ≠ j → 0 < coordinateAreaMatrix G i j := by
    intro i j hij
    rw [show G = affineBody K p a from rfl, coordinateAreaMatrix_affineBody]
    exact mul_pos (mul_pos (abs_pos.mpr (ha i)) (abs_pos.mpr (ha j))) (hpositive i j hij)
  have hGrank : (coordinateAreaMatrix G).rank ≤ 3 := by
    rw [show G = affineBody K p a from rfl, coordinateAreaMatrix_affineBody]
    exact (ProjectionAreaReplication.rank_replicateArray_le id (fun i => |a i|)
      (coordinateAreaMatrix K)).trans hrank
  have hGsum : ∀ x ∈ G, ∑ i, x i = 0 := by
    rintro x ⟨y, hy, rfl⟩
    change ∑ i, a i * (y i - p i) = 0
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hrel y hy, hrel p hp, sub_self]
  exact no_positive_boundary_sum_zero G hGpositive hGrank hGsum

/-- Determinant-zero form of the same literal geometric result. -/
theorem positive_boundary_interior_of_det_zero (K : Body 4)
    (hpositive : ∀ i j, i ≠ j → 0 < coordinateAreaMatrix K i j)
    (hdet : (coordinateAreaMatrix K).det = 0) :
    (interior (K : Set (V 4))).Nonempty :=
  positive_boundary_interior K hpositive (four_rank_le_three_of_det_zero _ hdet)

/-- The paper's boundary equality is an equivalent sufficient hypothesis;
the rank bound in the preceding theorem is derived here. -/
theorem positive_boundary_interior_of_equality (K : Body 4)
    (hpositive : ∀ i j, i ≠ j → 0 < coordinateAreaMatrix K i j)
    (k : Fin 3)
    (hboundary : BoundaryEquality
      (Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 3))
      (Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 3))
      (Real.sqrt (coordinateAreaMatrix K 0 3 * coordinateAreaMatrix K 1 2)) k) :
    (interior (K : Set (V 4))).Nonempty := by
  let P : PositiveHollowMatrix 4 :=
    ⟨coordinateAreaMatrix K, coordinateAreaMatrix_hollow K,
      coordinateAreaMatrix_symmetric K, hpositive⟩
  exact positive_boundary_interior K hpositive
    (rank_le_three_of_boundary_equality P k hboundary)

end ProjectionAreaFullInterior

#print axioms ProjectionAreaFullInterior.positive_boundary_interior
#print axioms ProjectionAreaFullInterior.positive_boundary_interior_of_equality

end
end
end Source_BoundaryInterior

/-! ## 4. Density -/

section Source_Density

@[expose] public section

/-!
# Strict realizations are dense in the escape cone

This short interface makes the density assertion at the end of Section 4
explicit. The approximation theorem used below is already proved in the
escape construction. The set is defined by the strict inequalities themselves;
membership does not assume either realizability or an approximation property.

The weight vector is explicitly nonzero. This matters in dimension zero,
where a universally positive function on `Fin 0` is still the zero function.
With this convention the closure identity holds in every dimension.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace ProjectionAreaPaper

open ProjectionAreaTopology ProjectionAreaEscape

/-- Positive hollow symmetric arrays with a nonzero positive weight vector
satisfying every strict weighted triangle inequality on distinct labels. -/
def strictWeightedLocus (n : ℕ) : Set (AreaArray n) :=
  {q | (∀ i, q i i = 0) ∧ (∀ i j, q i j = q j i) ∧
    (∀ i j, i ≠ j → 0 < q i j) ∧
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ w ≠ 0 ∧
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        w k * q i j < w j * q i k + w i * q j k}

/-- Strict inequalities give a witness for the nonstrict escape cone. -/
theorem strictWeightedLocus_subset_escapeCone (n : ℕ) :
    strictWeightedLocus n ⊆ EscapeCone n := by
  rintro q ⟨hdiag, hsym, hpos, w, hw, hwne, hstrict⟩
  refine ⟨hdiag, hsym, ?_, w, fun i => (hw i).le, hwne, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      exact (hdiag i).ge
    · exact (hpos i j hij).le
  · intro i j k hij hik hjk
    exact (hstrict i j k hij hik hjk).le

/-- The density sentence following Theorem 4.1, including every zero pattern
in the limiting array and every possible zero coordinate of an escape witness. -/
theorem closure_strictWeightedLocus (n : ℕ) :
    closure (strictWeightedLocus n) = EscapeCone n := by
  apply Set.Subset.antisymm
  · exact closure_minimal (strictWeightedLocus_subset_escapeCone n)
      (escapeCone_isClosed n)
  · rintro q ⟨hdiag, hsym, hnonneg, w, hw, hwne, htri⟩
    obtain ⟨Q, W, hlim, hQsym, hQdiag, hQpos, hWpos, hstrict⟩ :=
      exists_strict_weighted_approximation q w hnonneg hsym hdiag hw hwne htri
    have hlabel : ∃ i, w i ≠ 0 := by
      by_contra h
      push Not at h
      exact hwne (funext h)
    obtain ⟨i, _⟩ := hlabel
    apply mem_closure_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro m
    refine ⟨hQdiag m, hQsym m, hQpos m, W m, hWpos m, ?_, hstrict m⟩
    intro hzero
    have hpositive := hWpos m i
    simpa only [hzero, Pi.zero_apply, lt_self_iff_false] using hpositive

/-- Every strict array is an exact projection-area array. This is an actual
convex-body realization, obtained from the finite-hull theorem. -/
theorem strictWeightedLocus_subset_realizationLocus (n : ℕ) :
    strictWeightedLocus n ⊆ realizationLocus n := by
  rintro q ⟨hdiag, hsym, hpos, w, hw, hwne, hstrict⟩
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    apply hwne
    ext i
    exact Fin.elim0 i
  obtain ⟨S, _, hcompact, hconvex, hnonempty, _, harea, _⟩ :=
    ProjectionAreaStrict.strict_weighted_realization hn q w hsym hdiag
      hpos hw hstrict 0
  refine ⟨euclideanBodyOfSet (convexHull ℝ (S : Set (Fin n → ℝ)))
    hcompact hconvex hnonempty, ?_⟩
  rw [coordinateAreas_euclideanBodyOfSet]
  exact funext fun i => funext fun j => harea i j

/-- A single statement combining density with exact realizability of every
approximating strict array. -/
theorem closure_realizable_strictWeightedLocus (n : ℕ) :
    closure (realizationLocus n ∩ strictWeightedLocus n) = EscapeCone n := by
  rw [Set.inter_eq_right.mpr (strictWeightedLocus_subset_realizationLocus n)]
  exact closure_strictWeightedLocus n

end ProjectionAreaPaper

#print axioms ProjectionAreaPaper.closure_strictWeightedLocus
#print axioms ProjectionAreaPaper.strictWeightedLocus_subset_realizationLocus
#print axioms ProjectionAreaPaper.closure_realizable_strictWeightedLocus

end
end
end Source_Density

/-! ## 5. SeminormLimit -/

section Source_SeminormLimit

@[expose] public section

/-!
# A unit-vector seminorm representation of escaping projection areas

This supplements the escape-cone theorem with the literal representation in
Lemma 3.1 of the paper.  The proof uses the already verified finite width
construction: evaluation on its vertices defines a linear map into a finite
sup-norm space.  Pulling back that ordinary norm gives an actual Mathlib
`Seminorm`; normalizing the weight vector then gives a Euclidean unit vector.

The representation is proved for every member of the escape cone, including
all zero patterns, before it is applied to an escaping sequence of bodies.
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace ProjectionAreaEscape

variable {n : ℕ}

/-- Twice evaluation against each vertex of the prescribed-width polytope.
The factor two converts the half-width attained by a vertex into the width. -/
def widthEvaluation (q : Fin n → Fin n → ℝ) (w : Fin n → ℝ) (a : Fin n) :
    (Fin n → ℝ) →ₗ[ℝ] (WidthVertexIndex n → ℝ) where
  toFun x t := 2 * dotProduct x (widthVertex q w a t)
  map_add' x y := by
    ext t
    simp only [Pi.add_apply, add_dotProduct, mul_add]
  map_smul' c x := by
    ext t
    simp only [Pi.smul_apply, smul_dotProduct, smul_eq_mul, RingHom.id_apply]
    ring

theorem widthEvaluation_pair
    (q : Fin n → Fin n → ℝ) (w : Fin n → ℝ) (a : Fin n)
    (i j : Fin n) (t : WidthVertexIndex n) :
    widthEvaluation q w a
        (w i • Pi.single j 1 - w j • Pi.single i 1) t =
      2 * pairFunctional w i j (widthVertex q w a t) := by
  change 2 * dotProduct
    (w i • (Pi.single j 1 : Fin n → ℝ) - w j • Pi.single i 1)
    (widthVertex q w a t) = _
  simp only [sub_dotProduct, smul_dotProduct, single_dotProduct, smul_eq_mul,
    one_mul, pairFunctional, LinearMap.coe_mk, AddHom.coe_mk]

/-- The pullback of a finite-dimensional sup norm.  This definition carries
all the standard seminorm laws, rather than encoding the desired conclusion. -/
def widthSeminorm (q : Fin n → Fin n → ℝ) (w : Fin n → ℝ) (a : Fin n) :
    Seminorm ℝ (Fin n → ℝ) :=
  (normSeminorm ℝ (WidthVertexIndex n → ℝ)).comp (widthEvaluation q w a)

theorem widthSeminorm_pair
    (q : Fin n → Fin n → ℝ) (w : Fin n → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (hsym : ∀ i j, q i j = q j i)
    (hdiag : ∀ i, q i i = 0) (hw : ∀ i, 0 ≤ w i)
    (htri : ∀ i j k, w k * q i j ≤ w j * q i k + w i * q j k)
    (a : Fin n) (ha : 0 < w a) (i j : Fin n) :
    widthSeminorm q w a
      (w i • Pi.single j 1 - w j • Pi.single i 1) = q i j := by
  change ‖widthEvaluation q w a
    (w i • Pi.single j 1 - w j • Pi.single i 1)‖ = q i j
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (hq i j)).2
    intro t
    rw [widthEvaluation_pair, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hbound := widthVertex_bound q w hq hsym hw htri a ha t i j
    linarith
  · obtain ⟨t, ht⟩ := widthVertex_attains q w hq hsym hdiag hw htri a ha i j
    have hvalue : widthEvaluation q w a
        (w i • Pi.single j 1 - w j • Pi.single i 1) t = q i j := by
      rw [widthEvaluation_pair, ht]
      ring
    have hnorm := norm_le_pi_norm
      (widthEvaluation q w a (w i • Pi.single j 1 - w j • Pi.single i 1)) t
    simpa only [hvalue, Real.norm_eq_abs, abs_of_nonneg (hq i j)] using hnorm

end ProjectionAreaEscape

namespace ProjectionAreaPaper

open ProjectionAreaTopology ProjectionAreaEscape

/-- The usual coordinate unit vector in the Euclidean coordinate space. -/
def coordinateBasisVector {n : ℕ} (i : Fin n) : CoordinateSpace n :=
  PiLp.single 2 i 1

@[simp]
theorem coordinateBasisVector_apply {n : ℕ} (i j : Fin n) :
    coordinateBasisVector i j = if j = i then 1 else 0 := by
  simp [coordinateBasisVector]

/-- A stronger existence form of Lemma 3.1: every escape-cone array has a
seminorm representation with a Euclidean unit vector.  The constructed vector
is nonnegative, and its absolute coordinates are explicit triangle weights. -/
theorem unit_seminorm_of_escapeCone {n : ℕ} (q : AreaArray n)
    (hqEscape : q ∈ EscapeCone n) :
    ∃ v : CoordinateSpace n, ∃ N : Seminorm ℝ (CoordinateSpace n),
      ‖v‖ = 1 ∧ (∀ i, 0 ≤ v i) ∧
      (∀ i j, q i j = N
        (v i • coordinateBasisVector j - v j • coordinateBasisVector i)) ∧
      WeightedTriangleWitness q (fun i => |v i|) := by
  classical
  rcases hqEscape with ⟨hdiag, hsym, hq, w, hw, hwne, htri⟩
  have hpos : ∃ a, 0 < w a := by
    by_contra! h
    apply hwne
    ext a
    exact le_antisymm (h a) (hw a)
  obtain ⟨a, ha⟩ := hpos
  have htriAll := weighted_triangle_all_indices q w hq hsym hdiag hw htri
  let e := ProjectionAreaStrict.asEuclidean n
  let r : ℝ := ‖e w‖
  have hew : e w ≠ 0 := by
    intro h
    apply hwne
    apply e.injective
    simpa only [map_zero] using h
  have hr : 0 < r := norm_pos_iff.mpr hew
  let v : CoordinateSpace n := r⁻¹ • e w
  let N : Seminorm ℝ (CoordinateSpace n) :=
    (widthSeminorm q w a).comp (r • e.symm.toLinearMap)
  have hvcoord (i : Fin n) : v i = r⁻¹ * w i := by
    rfl
  have hrv (i : Fin n) : r * v i = w i := by
    rw [hvcoord, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  have hvnorm : ‖v‖ = 1 := by
    change ‖r⁻¹ • e w‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hvnonneg (i : Fin n) : 0 ≤ v i := by
    rw [hvcoord]
    exact mul_nonneg (inv_nonneg.mpr hr.le) (hw i)
  have heunit (i : Fin n) : e.symm (coordinateBasisVector i) = Pi.single i 1 := by
    rfl
  have hpair (i j : Fin n) :
      (r • e.symm.toLinearMap)
          (v i • coordinateBasisVector j - v j • coordinateBasisVector i) =
        w i • Pi.single j 1 - w j • Pi.single i 1 := by
    change r • e.symm
      (v i • coordinateBasisVector j - v j • coordinateBasisVector i) = _
    rw [map_sub, map_smul, map_smul, heunit, heunit,
      smul_sub, smul_smul, smul_smul, hrv, hrv]
  refine ⟨v, N, hvnorm, hvnonneg, ?_, ?_⟩
  · intro i j
    change q i j = widthSeminorm q w a
      ((r • e.symm.toLinearMap)
        (v i • coordinateBasisVector j - v j • coordinateBasisVector i))
    rw [hpair]
    exact (widthSeminorm_pair q w hq hsym hdiag hw htriAll a ha i j).symm
  · refine ⟨fun i => abs_nonneg _, ?_, ?_⟩
    · intro hzero
      apply hwne
      ext i
      simp only [Pi.zero_apply]
      have hi : |v i| = 0 := congrFun hzero i
      have hvi : v i = 0 := abs_eq_zero.mp hi
      rw [← hrv i, hvi, mul_zero]
    · intro i j k hij hik hjk
      change |v k| * q i j ≤ |v j| * q i k + |v i| * q j k
      rw [abs_of_nonneg (hvnonneg k), abs_of_nonneg (hvnonneg j),
        abs_of_nonneg (hvnonneg i)]
      have h := mul_le_mul_of_nonneg_left (htri i j k hij hik hjk)
        (inv_nonneg.mpr hr.le)
      simpa only [hvcoord, mul_add, mul_assoc] using h

/-- Lemma 3.1 of the paper, for the ordinary areas and Euclidean diameters
of an actual sequence of nonempty compact convex bodies. -/
theorem escaping_limit_seminorm {n : ℕ}
    (K : ℕ → CoordinateBody n) (q : AreaArray n)
    (harea : Tendsto (fun m => coordinateAreas (K m)) atTop (𝓝 q))
    (hdiam : Tendsto (fun m => Metric.diam
      (K m : Set (CoordinateSpace n))) atTop atTop) :
    ∃ v : CoordinateSpace n, ∃ N : Seminorm ℝ (CoordinateSpace n),
      ‖v‖ = 1 ∧ (∀ i, 0 ≤ v i) ∧
      (∀ i j, q i j = N
        (v i • coordinateBasisVector j - v j • coordinateBasisVector i)) ∧
      WeightedTriangleWitness q (fun i => |v i|) :=
  unit_seminorm_of_escapeCone q
    (ProjectionAreaEscapeNormalization.divergingDiameterLimits_subset_escapeCone n
      ⟨K, harea, hdiam⟩)

end ProjectionAreaPaper

end
end
end Source_SeminormLimit

/-! ## 6. CircleMetric -/

section Source_CircleMetric

@[expose] public section

/-!
# Circle realizations of positive metric matrices of rank three

This is a literal geometric companion to Lemma 5.1. The earlier algebraic
development supplies the bound of four labels and the rectangle distance
identities. Here the points are constructed in the actual Euclidean plane,
their squared distances are checked, and a circle of positive radius is
exhibited. With four labels their range is exactly the four corners of a
nondegenerate Euclidean rectangle.

The generated additional module also records the complete theorem types
and their transitive axiom dependencies.
-/

noncomputable section

open Matrix Set

namespace ProjectionAreaCircleMetric

open ProjectionAreaRankThree

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A point with the indicated Cartesian coordinates in the Euclidean plane. -/
def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

@[simp] theorem point_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] theorem point_one (x y : ℝ) : point x y 1 = y := rfl

theorem point_dist_sq (x y u v : ℝ) :
    dist (point x y) (point u v) ^ 2 = (x - u) ^ 2 + (y - v) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq]

/-- The four actual corners of a rectangle, in cyclic order. -/
def rectanglePoints (a b : ℝ) : Fin 4 → Plane :=
  ![point 0 0, point a 0, point a b, point 0 b]

/-- A concrete nondegenerate rectangle. The existential placement theorem
below is free to choose the coordinate origin and the two axis directions. -/
def IsRectangleSet (S : Set Plane) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ S = Set.range (rectanglePoints a b)

private theorem injective_of_squared_distances {n : ℕ}
    (D : PositiveMetricMatrix n) (p : Fin n → Plane)
    (hdist : ∀ i j, dist (p i) (p j) ^ 2 = D.entries i j) :
    Function.Injective p := by
  intro i j hij
  by_contra hne
  have hp := D.positive i j hne
  have hz : D.entries i j = 0 := by
    rw [← hdist i j, hij]
    simp
  linarith

/-- Positive three-point metric data admit noncollinear Cartesian coordinates
with those data as squared distances. -/
private theorem triangle_coordinates {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a ≤ b + c) (hbac : b ≤ a + c) (hcab : c ≤ a + b) :
    ∃ s x t : ℝ, 0 < s ∧ 0 < t ∧
      s ^ 2 = a ∧ x ^ 2 + t ^ 2 = b ∧ (s - x) ^ 2 + t ^ 2 = c := by
  let z : ℝ := (a + b - c) / 2
  have hz : 2 * z = a + b - c := by dsimp [z]; ring
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hza : z ≤ a := by dsimp [z]; linarith
  have hzb : z ≤ b := by dsimp [z]; linarith
  have hzsq : z ^ 2 < a * b := by
    by_cases hlt : z < a
    · calc
        z ^ 2 = z * z := by ring
        _ ≤ z * b := mul_le_mul_of_nonneg_left hzb hz0
        _ < a * b := mul_lt_mul_of_pos_right hlt hb
    · have heq : z = a := le_antisymm hza (le_of_not_gt hlt)
      have hltb : z < b := by linarith
      have hzp : 0 < z := by rw [heq]; exact ha
      calc
        z ^ 2 = z * z := by ring
        _ < z * b := mul_lt_mul_of_pos_left hltb hzp
        _ = a * b := by rw [heq]
  let s : ℝ := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.mpr ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  let x : ℝ := z / s
  have hxs : x * s = z := by
    dsimp [x]
    exact div_mul_cancel₀ _ hs.ne'
  have hx2 : x ^ 2 * a = z ^ 2 := by
    calc
      x ^ 2 * a = x ^ 2 * s ^ 2 := by rw [hs2]
      _ = (x * s) ^ 2 := by ring
      _ = z ^ 2 := by rw [hxs]
  have hheight : 0 < b - x ^ 2 := by
    have hmul : 0 < a * (b - x ^ 2) := by nlinarith
    exact (mul_pos_iff_of_pos_left ha).mp hmul
  let t : ℝ := Real.sqrt (b - x ^ 2)
  have ht : 0 < t := Real.sqrt_pos.mpr hheight
  have ht2 : t ^ 2 = b - x ^ 2 := Real.sq_sqrt hheight.le
  refine ⟨s, x, t, hs, ht, hs2, ?_, ?_⟩ <;> nlinarith

/-- The circumcenter is written explicitly, so no noncollinearity or
circumcenter-existence theorem is left as an assumption. -/
private theorem triangle_points_on_circle (s x t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ∃ center : Plane, ∃ radius : ℝ, 0 < radius ∧
      ∀ i : Fin 3, dist ((![point 0 0, point s 0, point x t] : Fin 3 → Plane) i)
        center = radius := by
  let h : ℝ := (x ^ 2 + t ^ 2 - s * x) / (2 * t)
  let center : Plane := point (s / 2) h
  let radius : ℝ := dist (point 0 0) center
  have hr : 0 < radius := by
    apply dist_pos.mpr
    intro heq
    have heq0 := congrArg (fun p : Plane => p 0) heq
    change 0 = s / 2 at heq0
    linarith
  have hheight : 2 * t * h = x ^ 2 + t ^ 2 - s * x := by
    dsimp [h]
    field_simp [ht.ne'] <;> ring
  refine ⟨center, radius, hr, ?_⟩
  intro i
  apply (sq_eq_sq₀ (dist_nonneg) (show 0 ≤ radius from hr.le)).mp
  change dist ((![point 0 0, point s 0, point x t] : Fin 3 → Plane) i)
      center ^ 2 = dist (point 0 0) center ^ 2
  fin_cases i <;> simp [center, point_dist_sq] <;> nlinarith

/-- The three-label case, with a genuine circle of positive radius. -/
theorem three_point_circle_realization (D : PositiveMetricMatrix 3) :
    ∃ p : Fin 3 → Plane, ∃ center : Plane, ∃ radius : ℝ,
      0 < radius ∧ Function.Injective p ∧
      (∀ i, dist (p i) center = radius) ∧
      ∀ i j, dist (p i) (p j) ^ 2 = D.entries i j := by
  obtain ⟨s, x, t, hs, ht, hs2, hxt2, hst2⟩ := triangle_coordinates
    (D.positive 0 1 (by decide)) (D.positive 0 2 (by decide))
    (D.positive 1 2 (by decide))
    (by simpa only [D.symmetric 2 1] using D.triangle 0 1 2)
    (D.triangle 0 2 1)
    (by simpa only [D.symmetric 1 0] using D.triangle 1 2 0)
  let p : Fin 3 → Plane := ![point 0 0, point s 0, point x t]
  have hdist : ∀ i j, dist (p i) (p j) ^ 2 = D.entries i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [p, point_dist_sq, D.hollow] <;>
      nlinarith [D.symmetric 1 0, D.symmetric 2 0, D.symmetric 2 1]
  obtain ⟨center, radius, hr, hcircle⟩ := triangle_points_on_circle s x t hs ht
  exact ⟨p, center, radius, hr, injective_of_squared_distances D p hdist,
    hcircle, hdist⟩

private theorem rectangle_points_on_circle (a b : ℝ) (ha : 0 < a) :
    ∃ center : Plane, ∃ radius : ℝ, 0 < radius ∧
      ∀ i, dist (rectanglePoints a b i) center = radius := by
  let center : Plane := point (a / 2) (b / 2)
  let radius : ℝ := dist (point 0 0) center
  have hr : 0 < radius := by
    apply dist_pos.mpr
    intro heq
    have heq0 := congrArg (fun p : Plane => p 0) heq
    change 0 = a / 2 at heq0
    linarith
  refine ⟨center, radius, hr, ?_⟩
  intro i
  apply (sq_eq_sq₀ (dist_nonneg) (show 0 ≤ radius from hr.le)).mp
  change dist (rectanglePoints a b i) center ^ 2 = dist (point 0 0) center ^ 2
  fin_cases i <;> simp [rectanglePoints, center, point_dist_sq] <;> ring

private theorem rectangle_result (D : PositiveMetricMatrix 4)
    (a b : ℝ) (e : Equiv.Perm (Fin 4)) (ha : 0 < a) (hb : 0 < b)
    (hdist : ∀ i j,
      dist (rectanglePoints a b (e i)) (rectanglePoints a b (e j)) ^ 2 = D.entries i j) :
    ∃ p : Fin 4 → Plane, ∃ center : Plane, ∃ radius : ℝ,
      0 < radius ∧ Function.Injective p ∧
      (∀ i, dist (p i) center = radius) ∧
      (∀ i j, dist (p i) (p j) ^ 2 = D.entries i j) ∧
      IsRectangleSet (Set.range p) := by
  let p : Fin 4 → Plane := fun i => rectanglePoints a b (e i)
  obtain ⟨center, radius, hr, hc⟩ := rectangle_points_on_circle a b ha
  refine ⟨p, center, radius, hr, injective_of_squared_distances D p hdist,
    fun i => hc (e i), hdist, a, b, ha, hb, ?_⟩
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp [p]⟩

/-- The four-label case is realized by the actual four corners of a
nondegenerate rectangle, with a checked circumcircle and all distances. -/
theorem four_point_rectangle_realization (D : PositiveMetricMatrix 4)
    (hrank : D.entries.rank ≤ 3) :
    ∃ p : Fin 4 → Plane, ∃ center : Plane, ∃ radius : ℝ,
      0 < radius ∧ Function.Injective p ∧
      (∀ i, dist (p i) center = radius) ∧
      (∀ i j, dist (p i) (p j) ^ 2 = D.entries i j) ∧
      IsRectangleSet (Set.range p) := by
  obtain ⟨h01, h02, h03, hdiagonal⟩ := D.four_rectangle hrank
    0 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hsym10 := D.symmetric 1 0
  have hsym20 := D.symmetric 2 0
  have hsym30 := D.symmetric 3 0
  have hsym21 := D.symmetric 2 1
  have hsym31 := D.symmetric 3 1
  have hsym32 := D.symmetric 3 2
  rcases hdiagonal with hdiagonal | hdiagonal | hdiagonal
  · let a := Real.sqrt (D.entries 0 2)
    let b := Real.sqrt (D.entries 0 3)
    have ha : 0 < a := Real.sqrt_pos.mpr (D.positive 0 2 (by decide))
    have hb : 0 < b := Real.sqrt_pos.mpr (D.positive 0 3 (by decide))
    have ha2 : a ^ 2 = D.entries 0 2 := Real.sq_sqrt (D.positive 0 2 (by decide)).le
    have hb2 : b ^ 2 = D.entries 0 3 := Real.sq_sqrt (D.positive 0 3 (by decide)).le
    apply rectangle_result D a b (Equiv.swap 1 2) ha hb
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Equiv.swap_apply_def, rectanglePoints, point_dist_sq, D.hollow,
        hsym10, hsym20, hsym30, hsym21, hsym31, hsym32,
        ← h01, ← h02, ← h03, ha2, hb2, hdiagonal]
  · let a := Real.sqrt (D.entries 0 1)
    let b := Real.sqrt (D.entries 0 3)
    have ha : 0 < a := Real.sqrt_pos.mpr (D.positive 0 1 (by decide))
    have hb : 0 < b := Real.sqrt_pos.mpr (D.positive 0 3 (by decide))
    have ha2 : a ^ 2 = D.entries 0 1 := Real.sq_sqrt (D.positive 0 1 (by decide)).le
    have hb2 : b ^ 2 = D.entries 0 3 := Real.sq_sqrt (D.positive 0 3 (by decide)).le
    apply rectangle_result D a b (Equiv.refl _) ha hb
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rectanglePoints, point_dist_sq, D.hollow,
        hsym10, hsym20, hsym30, hsym21, hsym31, hsym32,
        ← h01, ← h02, ← h03, ha2, hb2, hdiagonal]
  · let a := Real.sqrt (D.entries 0 1)
    let b := Real.sqrt (D.entries 0 2)
    have ha : 0 < a := Real.sqrt_pos.mpr (D.positive 0 1 (by decide))
    have hb : 0 < b := Real.sqrt_pos.mpr (D.positive 0 2 (by decide))
    have ha2 : a ^ 2 = D.entries 0 1 := Real.sq_sqrt (D.positive 0 1 (by decide)).le
    have hb2 : b ^ 2 = D.entries 0 2 := Real.sq_sqrt (D.positive 0 2 (by decide)).le
    apply rectangle_result D a b (Equiv.swap 2 3) ha hb
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Equiv.swap_apply_def, rectanglePoints, point_dist_sq, D.hollow,
        hsym10, hsym20, hsym30, hsym21, hsym31, hsym32,
        ← h01, ← h02, ← h03, ha2, hb2, hdiagonal]

/-- Lemma 5.1 in full: a positive hollow symmetric metric matrix of rank
three is exactly the squared-distance matrix of at most four distinct points
on a circle in the Euclidean plane; with four labels, the chosen points are
the vertices of a nondegenerate rectangle. -/
theorem rank_three_circle_realization {n : ℕ} (D : PositiveMetricMatrix n)
    (hrank : D.entries.rank = 3) :
    n ≤ 4 ∧ ∃ p : Fin n → Plane, ∃ center : Plane, ∃ radius : ℝ,
      0 < radius ∧ Function.Injective p ∧
      (∀ i, dist (p i) center = radius) ∧
      (∀ i j, dist (p i) (p j) ^ 2 = D.entries i j) ∧
      (n = 4 → IsRectangleSet (Set.range p)) := by
  have hnlow : 3 ≤ n := by
    calc
      3 = D.entries.rank := hrank.symm
      _ ≤ n := by simpa using Matrix.rank_le_card_width D.entries
  have hnhigh : n ≤ 4 := by
    by_contra hn
    have h := D.rank_at_least_four (by omega : 5 ≤ n)
    omega
  refine ⟨hnhigh, ?_⟩
  rcases (show n = 3 ∨ n = 4 by omega) with hn | hn
  · subst n
    obtain ⟨p, center, radius, hr, hinj, hcircle, hdist⟩ :=
      three_point_circle_realization D
    refine ⟨p, center, radius, hr, hinj, hcircle, hdist, ?_⟩
    intro h
    norm_num at h
  · subst n
    obtain ⟨p, center, radius, hr, hinj, hcircle, hdist, hrectangle⟩ :=
      four_point_rectangle_realization D hrank.le
    exact ⟨p, center, radius, hr, hinj, hcircle, hdist, fun _ => hrectangle⟩

end ProjectionAreaCircleMetric

#print axioms ProjectionAreaCircleMetric.three_point_circle_realization
#print axioms ProjectionAreaCircleMetric.four_point_rectangle_realization
#print axioms ProjectionAreaCircleMetric.rank_three_circle_realization

end
end
end Source_CircleMetric

/-! ## 7. ZeroDimension -/

section Source_ZeroDimension

@[expose] public section

/-!
# The positive-dimension condition in the large-diameter theorem

Every subset of the zero-dimensional Euclidean space has diameter zero.
The positive-entry and strict weighted-triangle hypotheses alone are
vacuous when their coordinate index type is empty. Consequently Theorem
4.1 needs its explicitly stated positive-dimension convention.
-/

noncomputable section

open Set MeasureTheory
open ProjectionAreaTopology

namespace ProjectionAreaZeroDimension

/-- Zero-dimensional convex bodies, including all allowed degenerate
bodies, have ordinary Euclidean diameter zero. -/
theorem coordinateBody_zero_diameter (K : CoordinateBody 0) :
    Metric.diam (K : Set (CoordinateSpace 0)) = 0 := by
  apply Metric.diam_subsingleton
  intro x _ y _
  ext i
  exact Fin.elim0 i

/-- There cannot be bodies of arbitrarily large diameter in dimension zero. -/
theorem no_arbitrarily_large_zero_dimensional_bodies :
    ¬ ∀ R : ℝ, ∃ K : CoordinateBody 0,
      R < Metric.diam (K : Set (CoordinateSpace 0)) := by
  intro h
  obtain ⟨K, hK⟩ := h 0
  rw [coordinateBody_zero_diameter] at hK
  exact (lt_irrefl (0 : ℝ)) hK

/-- The empty coordinate data satisfy every displayed algebraic hypothesis
of the strict realization theorem, but have no arbitrarily large-diameter
realizations. This checks precisely why `0 < d` is necessary. -/
theorem strict_empty_data_counterexample :
    ∃ q : AreaArray 0, ∃ w : Fin 0 → ℝ,
      (∀ i j, q i j = q j i) ∧
      (∀ i, q i i = 0) ∧
      (∀ i j, i ≠ j → 0 < q i j) ∧
      (∀ i, 0 < w i) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        w k * q i j < w j * q i k + w i * q j k) ∧
      ¬ (∀ R : ℝ, ∃ K : CoordinateBody 0,
        coordinateAreas K = q ∧ R < Metric.diam (K : Set (CoordinateSpace 0))) := by
  refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro h
    apply no_arbitrarily_large_zero_dimensional_bodies
    intro R
    obtain ⟨K, _, hK⟩ := h R
    exact ⟨K, hK⟩

end ProjectionAreaZeroDimension

#print axioms ProjectionAreaZeroDimension.coordinateBody_zero_diameter
#print axioms ProjectionAreaZeroDimension.strict_empty_data_counterexample

end
end
end Source_ZeroDimension

/-! ## 8. LocalCompatibility -/

section Source_LocalCompatibility

@[expose] public section

set_option autoImplicit false

/-!
# Compatibility from positivity on the two boundary quartets

This is a strengthening of Proposition 2.3's positive-area formulation.
Only the six areas on each specified quartet are assumed positive. The
area between the two nonshared labels, and all areas involving other
ambient labels, are unrestricted.

The geometric argument is the existing fiber-hull proof. Its first
contradiction is restated with the two local positivity hypotheses that
the proof actually uses. Coordinate permutation and projection then give
the arbitrary-label statement in the Euclidean body model.
-/

noncomputable section

open Set MeasureTheory Module Matrix
open scoped Pointwise BigOperators Topology
open ProjectionAreaRankThree ProjectionAreaBoundaryKernel
open ProjectionAreaRectangleObstruction

namespace ProjectionAreaMixedGeometry

/-- All off-diagonal entries of the named quartet are positive.
For an injective selection of labels in a symmetric actual area array,
these are exactly the six coordinate-plane projection areas. -/
def PositiveOnQuartet {n : ℕ} (q : Matrix (Fin n) (Fin n) ℝ)
    (ι : Fin 4 → Fin n) : Prop :=
  ∀ i j, i ≠ j → 0 < q (ι i) (ι j)

/-- The local positivity predicate is literally positivity of the area
matrix of the selected four-dimensional projection. -/
theorem positiveOnQuartet_coordinateAreaMatrix_iff {n : ℕ} (K : Body n)
    (ι : Fin 4 → Fin n) :
    PositiveOnQuartet (coordinateAreaMatrix K) ι ↔
      ∀ i j, i ≠ j → 0 < coordinateAreaMatrix (selectBody ι K) i j := by
  simp only [PositiveOnQuartet, coordinateAreaMatrix_selectBody, Matrix.submatrix_apply]

/-- The incompatible pair `01 | 23` and `04 | 12` is impossible using
positivity only on the two quartet projections `0123` and `0124`. -/
theorem incompatible_boundary_quartets_first_third_of_local_positivity
    (K : Body 5)
    (hApositive : ∀ i j : Fin 4, i ≠ j →
      0 < coordinateAreaMatrix (deleteBody (4 : Fin 5) K) i j)
    (hBpositive : ∀ i j : Fin 4, i ≠ j →
      0 < coordinateAreaMatrix (deleteBody (3 : Fin 5) K) i j)
    (hfirst : Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 3) =
      Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 3) +
        Real.sqrt (coordinateAreaMatrix K 0 3 * coordinateAreaMatrix K 1 2))
    (hthird : Real.sqrt (coordinateAreaMatrix K 0 4 * coordinateAreaMatrix K 1 2) =
      Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 4) +
        Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 4)) : False := by
  let A : Body 4 := deleteBody 4 K
  let B : Body 4 := deleteBody 3 K
  let P : PositiveHollowMatrix 4 :=
    ⟨coordinateAreaMatrix A, coordinateAreaMatrix_hollow A,
      coordinateAreaMatrix_symmetric A, hApositive⟩
  let Q : PositiveHollowMatrix 4 :=
    ⟨coordinateAreaMatrix B, coordinateAreaMatrix_hollow B,
      coordinateAreaMatrix_symmetric B, hBpositive⟩
  have hPboundary : Real.sqrt (P.entries 0 1 * P.entries 2 3) =
      Real.sqrt (P.entries 0 2 * P.entries 1 3) +
        Real.sqrt (P.entries 0 3 * P.entries 1 2) := by
    simpa [P, A, coordinateAreaMatrix_deleteBody, Matrix.submatrix_apply,
      Fin.succAbove] using hfirst
  have hQboundary : Real.sqrt (Q.entries 0 3 * Q.entries 1 2) =
      Real.sqrt (Q.entries 0 1 * Q.entries 2 3) +
        Real.sqrt (Q.entries 0 2 * Q.entries 1 3) := by
    simpa [Q, B, coordinateAreaMatrix_deleteBody, Matrix.submatrix_apply,
      Fin.succAbove] using hthird
  have hPrank := rank_le_three_of_boundary_equality P 0 hPboundary
  have hQrank := rank_le_three_of_boundary_equality Q 2 hQboundary
  obtain ⟨a, ha0, ha1, ha2, ha3⟩ := exists_complementary_kernel_first_pair P hPboundary
  obtain ⟨b, hb0, hb1, hb2, hb3⟩ := exists_complementary_kernel_third_pair Q hQboundary
  have hleft : fiberHull (deleteBody 3 A) 0 1 (by decide) = deleteBody 3 A := by
    apply deletion_fiberHull_of_kernel A a.coeff 3 0 1 (by decide) ha3
    · intro r hr0 hr1
      fin_cases r
      · exact (hr0 rfl).elim
      · exact (hr1 rfl).elim
      · exact ha2.le
      · exact ha3.le
    · exact kernel_pairing_of_complementary_kernel A P rfl a
    · exact triple_projection_interior_of_rank_le_three A P rfl hPrank 3
  have hright : fiberHull (deleteBody 3 B) 1 2 (by decide) = deleteBody 3 B := by
    apply deletion_fiberHull_of_kernel B b.coeff 3 1 2 (by decide) hb3
    · intro r hr1 hr2
      fin_cases r
      · exact hb0.le
      · exact (hr1 rfl).elim
      · exact (hr2 rfl).elim
      · exact hb3.le
    · exact kernel_pairing_of_complementary_kernel B Q rfl b
    · exact triple_projection_interior_of_rank_le_three B Q rfl hQrank 3
  have hproduct : fiberHull (deleteBody 0 A) 1 2 (by decide) = deleteBody 0 A := by
    apply deletion_fiberHull_of_kernel A a.neg.coeff 0 1 2 (by decide) (neg_pos.mpr ha0)
    · intro r hr2 hr3
      fin_cases r
      · exact (neg_pos.mpr ha0).le
      · exact (neg_pos.mpr ha1).le
      · exact (hr2 rfl).elim
      · exact (hr3 rfl).elim
    · exact kernel_pairing_of_complementary_kernel A P rfl a.neg
    · exact triple_projection_interior_of_rank_le_three A P rfl hPrank 0
  have hcommon : deleteBody (3 : Fin 4) A = deleteBody (3 : Fin 4) B :=
    shared_three_deletions K
  have hright' : fiberHull (deleteBody 3 A) 1 2 (by decide) = deleteBody 3 A := by
    rw [hcommon]
    exact hright
  have hprism : IndependentCoordinate (deleteBody 3 A : Set (V 3)) 1 :=
    middle_prism_independent (deleteBody 3 A) hleft hright'
      (deleteBody_interior_nonempty 1 (deleteBody 3 A)
        (triple_projection_interior_of_rank_le_three A P rfl hPrank 3))
  apply boundary_prism_obstruction A
    (fun i j hij => by rw [pairArea_eq_coordinateAreaMatrix]; exact hApositive i j hij)
    _ hproduct hprism
  simp only [pairArea_eq_coordinateAreaMatrix]
  exact P.four_det_eq_zero hPrank 0 1 2 3

/-- Swapping coordinates `0` and `1` preserves each quartet and rules out
the other incompatible matching `02 | 14`. -/
theorem incompatible_boundary_quartets_first_second_of_local_positivity
    (K : Body 5)
    (hApositive : ∀ i j : Fin 4, i ≠ j →
      0 < coordinateAreaMatrix (deleteBody (4 : Fin 5) K) i j)
    (hBpositive : ∀ i j : Fin 4, i ≠ j →
      0 < coordinateAreaMatrix (deleteBody (3 : Fin 5) K) i j)
    (hfirst : Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 3) =
      Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 3) +
        Real.sqrt (coordinateAreaMatrix K 0 3 * coordinateAreaMatrix K 1 2))
    (hsecond : Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 4) =
      Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 4) +
        Real.sqrt (coordinateAreaMatrix K 0 4 * coordinateAreaMatrix K 1 2)) : False := by
  let e : Equiv.Perm (Fin 5) := Equiv.swap 0 1
  let t : Equiv.Perm (Fin 4) := Equiv.swap 0 1
  let L : Body 5 := selectBody e K
  have he4 (i : Fin 4) :
      e ((4 : Fin 5).succAbove i) = (4 : Fin 5).succAbove (t i) := by
    fin_cases i <;> decide
  have he3 (i : Fin 4) :
      e ((3 : Fin 5).succAbove i) = (3 : Fin 5).succAbove (t i) := by
    fin_cases i <;> decide
  have hLpositiveA (i j : Fin 4) (hij : i ≠ j) :
      0 < coordinateAreaMatrix (deleteBody (4 : Fin 5) L) i j := by
    simpa only [L, coordinateAreaMatrix_deleteBody, coordinateAreaMatrix_selectBody,
      Matrix.submatrix_apply, he4] using
      hApositive (t i) (t j) (fun h => hij (t.injective h))
  have hLpositiveB (i j : Fin 4) (hij : i ≠ j) :
      0 < coordinateAreaMatrix (deleteBody (3 : Fin 5) L) i j := by
    simpa only [L, coordinateAreaMatrix_deleteBody, coordinateAreaMatrix_selectBody,
      Matrix.submatrix_apply, he3] using
      hBpositive (t i) (t j) (fun h => hij (t.injective h))
  apply incompatible_boundary_quartets_first_third_of_local_positivity
    L hLpositiveA hLpositiveB
  · simpa [L, e, coordinateAreaMatrix_selectBody, Matrix.submatrix,
      Equiv.swap_apply_def, coordinateAreaMatrix_symmetric K 1 0, mul_comm, add_comm] using hfirst
  · simpa [L, e, coordinateAreaMatrix_selectBody, Matrix.submatrix,
      Equiv.swap_apply_def, coordinateAreaMatrix_symmetric K 1 0, mul_comm, add_comm] using hsecond

/-- Compatibility on five coordinates under positivity only on `0123`
and `0124`. No hypothesis concerns the area on the omitted pair `34`. -/
theorem boundary_quartets_compatible_five_of_local_positivity
    (K : Body 5)
    (hApositive : ∀ i j : Fin 4, i ≠ j →
      0 < coordinateAreaMatrix (deleteBody (4 : Fin 5) K) i j)
    (hBpositive : ∀ i j : Fin 4, i ≠ j →
      0 < coordinateAreaMatrix (deleteBody (3 : Fin 5) K) i j)
    (hfirst : Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 3) =
      Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 3) +
        Real.sqrt (coordinateAreaMatrix K 0 3 * coordinateAreaMatrix K 1 2))
    (hboundary :
      Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 4) =
        Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 4) +
          Real.sqrt (coordinateAreaMatrix K 0 4 * coordinateAreaMatrix K 1 2) ∨
      Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 4) =
        Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 4) +
          Real.sqrt (coordinateAreaMatrix K 0 4 * coordinateAreaMatrix K 1 2) ∨
      Real.sqrt (coordinateAreaMatrix K 0 4 * coordinateAreaMatrix K 1 2) =
        Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 4) +
          Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 4)) :
    Real.sqrt (coordinateAreaMatrix K 0 1 * coordinateAreaMatrix K 2 4) =
      Real.sqrt (coordinateAreaMatrix K 0 2 * coordinateAreaMatrix K 1 4) +
        Real.sqrt (coordinateAreaMatrix K 0 4 * coordinateAreaMatrix K 1 2) := by
  rcases hboundary with h | h | h
  · exact h
  · exact (incompatible_boundary_quartets_first_second_of_local_positivity
      K hApositive hBpositive hfirst h).elim
  · exact (incompatible_boundary_quartets_first_third_of_local_positivity
      K hApositive hBpositive hfirst h).elim

/-- The arbitrary-label form: positivity is restricted to the selected
quartets, with no rank or positivity condition on the ambient array. -/
theorem boundary_quartets_compatible_of_local_positivity {n : ℕ} (K : Body n)
    (σ : Fin 5 → Fin n) (_hσ : Function.Injective σ)
    (hpositive_first : PositiveOnQuartet (coordinateAreaMatrix K) ![σ 0, σ 1, σ 2, σ 3])
    (hpositive_second : PositiveOnQuartet (coordinateAreaMatrix K) ![σ 0, σ 1, σ 2, σ 4])
    (hfirst : Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 1) *
        coordinateAreaMatrix K (σ 2) (σ 3)) =
      Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 2) * coordinateAreaMatrix K (σ 1) (σ 3)) +
        Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 3) * coordinateAreaMatrix K (σ 1) (σ 2)))
    (hboundary :
      Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 1) * coordinateAreaMatrix K (σ 2) (σ 4)) =
        Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 2) * coordinateAreaMatrix K (σ 1) (σ 4)) +
          Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 4) * coordinateAreaMatrix K (σ 1) (σ 2)) ∨
      Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 2) * coordinateAreaMatrix K (σ 1) (σ 4)) =
        Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 1) * coordinateAreaMatrix K (σ 2) (σ 4)) +
          Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 4) * coordinateAreaMatrix K (σ 1) (σ 2)) ∨
      Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 4) * coordinateAreaMatrix K (σ 1) (σ 2)) =
        Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 1) * coordinateAreaMatrix K (σ 2) (σ 4)) +
          Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 2) * coordinateAreaMatrix K (σ 1) (σ 4))) :
    Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 1) * coordinateAreaMatrix K (σ 2) (σ 4)) =
      Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 2) * coordinateAreaMatrix K (σ 1) (σ 4)) +
        Real.sqrt (coordinateAreaMatrix K (σ 0) (σ 4) * coordinateAreaMatrix K (σ 1) (σ 2)) := by
  let L := selectBody σ K
  have hσ4 (i : Fin 4) :
      σ ((4 : Fin 5).succAbove i) = ![σ 0, σ 1, σ 2, σ 3] i := by
    fin_cases i <;> rfl
  have hσ3 (i : Fin 4) :
      σ ((3 : Fin 5).succAbove i) = ![σ 0, σ 1, σ 2, σ 4] i := by
    fin_cases i <;> rfl
  have hLpositiveA (i j : Fin 4) (hij : i ≠ j) :
      0 < coordinateAreaMatrix (deleteBody (4 : Fin 5) L) i j := by
    simpa only [L, coordinateAreaMatrix_deleteBody, coordinateAreaMatrix_selectBody,
      Matrix.submatrix_apply, hσ4] using hpositive_first i j hij
  have hLpositiveB (i j : Fin 4) (hij : i ≠ j) :
      0 < coordinateAreaMatrix (deleteBody (3 : Fin 5) L) i j := by
    simpa only [L, coordinateAreaMatrix_deleteBody, coordinateAreaMatrix_selectBody,
      Matrix.submatrix_apply, hσ3] using hpositive_second i j hij
  have h := boundary_quartets_compatible_five_of_local_positivity
    L hLpositiveA hLpositiveB
    (by simpa only [L, coordinateAreaMatrix_selectBody, Matrix.submatrix_apply] using hfirst)
    (by simpa only [L, coordinateAreaMatrix_selectBody, Matrix.submatrix_apply] using hboundary)
  simpa only [L, coordinateAreaMatrix_selectBody, Matrix.submatrix_apply] using h

end ProjectionAreaMixedGeometry

namespace ProjectionAreaPaper

open ProjectionAreaTopology ProjectionAreaMixedGeometry

/-- Proposition 2.3 strengthened to positivity only on the two actual
boundary-quartet projections. Ambient dimension and the five distinct
labels are arbitrary; the square-root equality is the same conclusion
as `boundary_compatibility`. -/
theorem boundary_compatibility_of_local_positivity {n : ℕ} (K : CoordinateBody n)
    (σ : Fin 5 → Fin n) (hσ : Function.Injective σ)
    (hpositive_first : PositiveOnQuartet (coordinateAreas K) ![σ 0, σ 1, σ 2, σ 3])
    (hpositive_second : PositiveOnQuartet (coordinateAreas K) ![σ 0, σ 1, σ 2, σ 4])
    (hfirst : Real.sqrt (coordinateAreas K (σ 0) (σ 1) * coordinateAreas K (σ 2) (σ 3)) =
      Real.sqrt (coordinateAreas K (σ 0) (σ 2) * coordinateAreas K (σ 1) (σ 3)) +
        Real.sqrt (coordinateAreas K (σ 0) (σ 3) * coordinateAreas K (σ 1) (σ 2)))
    (hboundary :
      Real.sqrt (coordinateAreas K (σ 0) (σ 1) * coordinateAreas K (σ 2) (σ 4)) =
        Real.sqrt (coordinateAreas K (σ 0) (σ 2) * coordinateAreas K (σ 1) (σ 4)) +
          Real.sqrt (coordinateAreas K (σ 0) (σ 4) * coordinateAreas K (σ 1) (σ 2)) ∨
      Real.sqrt (coordinateAreas K (σ 0) (σ 2) * coordinateAreas K (σ 1) (σ 4)) =
        Real.sqrt (coordinateAreas K (σ 0) (σ 1) * coordinateAreas K (σ 2) (σ 4)) +
          Real.sqrt (coordinateAreas K (σ 0) (σ 4) * coordinateAreas K (σ 1) (σ 2)) ∨
      Real.sqrt (coordinateAreas K (σ 0) (σ 4) * coordinateAreas K (σ 1) (σ 2)) =
        Real.sqrt (coordinateAreas K (σ 0) (σ 1) * coordinateAreas K (σ 2) (σ 4)) +
          Real.sqrt (coordinateAreas K (σ 0) (σ 2) * coordinateAreas K (σ 1) (σ 4))) :
    Real.sqrt (coordinateAreas K (σ 0) (σ 1) * coordinateAreas K (σ 2) (σ 4)) =
      Real.sqrt (coordinateAreas K (σ 0) (σ 2) * coordinateAreas K (σ 1) (σ 4)) +
        Real.sqrt (coordinateAreas K (σ 0) (σ 4) * coordinateAreas K (σ 1) (σ 2)) := by
  have hpos_first : PositiveOnQuartet (coordinateAreaMatrix (asPiBody K))
      ![σ 0, σ 1, σ 2, σ 3] := by
    simpa only [coordinateAreaMatrix_asPiBody] using hpositive_first
  have hpos_second : PositiveOnQuartet (coordinateAreaMatrix (asPiBody K))
      ![σ 0, σ 1, σ 2, σ 4] := by
    simpa only [coordinateAreaMatrix_asPiBody] using hpositive_second
  simpa only [coordinateAreaMatrix_asPiBody] using
    boundary_quartets_compatible_of_local_positivity (asPiBody K) σ hσ
      hpos_first hpos_second
      (by simpa only [coordinateAreaMatrix_asPiBody] using hfirst)
      (by simpa only [coordinateAreaMatrix_asPiBody] using hboundary)

end ProjectionAreaPaper

#print axioms ProjectionAreaMixedGeometry.incompatible_boundary_quartets_first_third_of_local_positivity
#print axioms ProjectionAreaMixedGeometry.boundary_quartets_compatible_of_local_positivity
#print axioms ProjectionAreaPaper.boundary_compatibility_of_local_positivity

end
end
end Source_LocalCompatibility

/-!
## Additional statement and axiom audit

This reporting code inspects actual kernel declarations. It does not supply
proofs or axioms. The completed source build and the original principal audit
are separate requirements for a release.
-/

set_option maxHeartbeats 0 in
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  if Lean.debug.skipKernelTC.get (← Lean.getOptions) then
    throwError "The ordinary Lean kernel checker must be enabled"
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let compiledProjectModules : Array Lean.Name := #[]
  let moduleOf (name : Lean.Name) : Lean.Name :=
    match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let expandedProjectModules := compiledProjectModules.push env.mainModule
  let required : Array Lean.Name := #[
    `ProjectionAreaExamples.hexagonPoint_norm,
    `ProjectionAreaExamples.hexagonMatrix_eq_sq_dist,
    `ProjectionAreaExamples.hexagonPoint_injective,
    `ProjectionAreaExamples.hexagon_rank,
    `ProjectionAreaExamples.hexagon_obstruction,
    `ProjectionAreaExamples.hexagon_has_no_escape_weights,
    `ProjectionAreaPaper.closure_strictWeightedLocus,
    `ProjectionAreaPaper.strictWeightedLocus_subset_realizationLocus,
    `ProjectionAreaPaper.closure_realizable_strictWeightedLocus,
    `ProjectionAreaPaper.unit_seminorm_of_escapeCone,
    `ProjectionAreaPaper.escaping_limit_seminorm,
    `ProjectionAreaCircleMetric.rank_three_circle_realization,
    `ProjectionAreaExamples.hexagon_quadratic_form,
    `ProjectionAreaExamples.hexagon_signature,
    `ProjectionAreaBrightness.brightness_hlawka,
    `ProjectionAreaBrightness.brightness_pos,
    `ProjectionAreaFullInterior.positive_boundary_interior,
    `ProjectionAreaFullInterior.positive_boundary_interior_of_det_zero,
    `ProjectionAreaFullInterior.positive_boundary_interior_of_equality,
    `ProjectionAreaZeroDimension.coordinateBody_zero_diameter,
    `ProjectionAreaZeroDimension.strict_empty_data_counterexample,
    `ProjectionAreaPaper.boundary_compatibility_of_local_positivity,
    `ProjectionAreaMixedGeometry.positiveOnQuartet_coordinateAreaMatrix_iff]
  let defining : Array Lean.Name := #[
    `ProjectionAreaExamples.hexagonMatrix,
    `ProjectionAreaExamples.hexagonPoint,
    `ProjectionAreaPaper.strictWeightedLocus,
    `ProjectionAreaEscape.widthEvaluation,
    `ProjectionAreaEscape.widthSeminorm,
    `ProjectionAreaPaper.coordinateBasisVector,
    `ProjectionAreaCircleMetric.Plane,
    `ProjectionAreaRankThree.PositiveMetricMatrix,
    `ProjectionAreaRankThree.PositiveMetricMatrix.mk,
    `ProjectionAreaCircleMetric.point,
    `ProjectionAreaCircleMetric.rectanglePoints,
    `ProjectionAreaCircleMetric.IsRectangleSet,
    `ProjectionAreaBrightness.brightness,
    `ProjectionAreaBoundaryKernel.BoundaryEquality,
    `ProjectionAreaMixedGeometry.PositiveOnQuartet]
  let mut statements : Array Lean.Json := #[]
  for name in required do
    let some ci := env.find? name
      | throwError "Required additional theorem is missing: {name}"
    unless ci.isTheorem do
      throwError "Required entry is not a kernel theorem: {name}"
    unless (ci.value? (allowOpaque := true)).isSome do
      throwError "Actual proof body is unavailable for required theorem: {name}"
    unless (← Lean.Elab.Command.liftTermElabM <| Lean.Meta.isProp ci.type) do
      throwError "Required entry is not a proposition: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    let prettyType ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.ppExpr ci.type
    statements := statements.push <| Lean.Json.mkObj [
      ("name", Lean.toJson name.toString),
      ("module", Lean.toJson (moduleOf name).toString),
      ("compiled_project_stage", Lean.toJson (compiledProjectModules.contains (moduleOf name))),
      ("proof_body_available", Lean.toJson true),
      ("type", Lean.toJson prettyType.pretty),
      ("complete_type_expression", Lean.toJson (reprStr ci.type)),
      ("axioms", Lean.toJson (axioms.map Lean.Name.toString))]
  let mut definitions : Array Lean.Json := #[]
  for name in defining do
    let some ci := env.find? name
      | throwError "Defining mathematical constant is missing: {name}"
    let prettyType ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.ppExpr ci.type
    let mut row := [
      ("name", Lean.toJson name.toString),
      ("module", Lean.toJson (moduleOf name).toString),
      ("compiled_project_stage", Lean.toJson (compiledProjectModules.contains (moduleOf name))),
      ("type", Lean.toJson prettyType.pretty),
      ("complete_type_expression", Lean.toJson (reprStr ci.type))]
    if let some value := ci.value? (allowOpaque := true) then
      let prettyValue ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.ppExpr value
      row := row ++ [("value", Lean.toJson prettyValue.pretty),
        ("complete_value_expression", Lean.toJson (reprStr value))]
    definitions := definitions.push (Lean.Json.mkObj row)
  let mut pending : List Lean.Name := (required ++ defining).toList
  let mut seen : Lean.NameSet := {}
  let mut nodes : Array Lean.Json := #[]
  let mut foundAxioms : Lean.NameSet := {}
  while !pending.isEmpty do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      unless seen.contains name do
        seen := seen.insert name
        let some ci := env.find? name
          | throwError "A logical dependency cannot be inspected: {name}"
        let imported := (env.getModuleIdxFor? name).isSome
        let moduleName := moduleOf name
        let compiledStage := imported && compiledProjectModules.contains moduleName
        let importedBoundary := imported && !compiledStage
        let mut boundaryAxioms : Array Lean.Name := #[]
        let dependencies ← if importedBoundary then do
          -- Stop at checked external and recovered-basis declarations. Stock
          -- Lean supplies their exported transitive axiom metadata; an exported
          -- theorem signature is not a newly assumed mathematical axiom.
          boundaryAxioms ← Lean.collectAxioms name
          for ax in boundaryAxioms do
            unless allowed.contains ax do
              throwError "Unapproved imported transitive axiom in {name}: {ax}"
            foundAxioms := foundAxioms.insert ax
          pure []
        else do
          -- Explicit `import all` loads each compiled project stage's full
          -- ConstantInfo records. In private scope this traverses actual proof
          -- bodies, including private helpers, across the stage boundaries.
          if ci.isUnsafe || ci.isPartial then
            throwError "An unsafe or partial declaration occurs in the logical graph: {name}"
          if ci.isAxiom then
            foundAxioms := foundAxioms.insert name
            unless allowed.contains name do
              throwError "Unapproved axiom in the transitive graph: {name}"
          pure ci.getUsedConstantsAsSet.toList
        pending := dependencies ++ pending
        nodes := nodes.push <| Lean.Json.mkObj [
          ("name", Lean.toJson name.toString),
          ("module", Lean.toJson moduleName.toString),
          ("is_theorem", Lean.toJson ci.isTheorem),
          ("compiled_project_stage", Lean.toJson compiledStage),
          ("proof_body_available", Lean.toJson ((ci.value? (allowOpaque := true)).isSome)),
          ("imported_checked_boundary", Lean.toJson importedBoundary),
          ("imported_transitive_axioms", Lean.toJson (boundaryAxioms.map Lean.Name.toString)),
          ("is_local_axiom", Lean.toJson (!importedBoundary && ci.isAxiom)),
          ("dependencies", Lean.toJson (dependencies.map Lean.Name.toString))]
  let graph := Lean.Json.mkObj [
    ("roots", Lean.toJson ((required ++ defining).map Lean.Name.toString)),
    ("expanded_project_modules", Lean.toJson (expandedProjectModules.map Lean.Name.toString)),
    ("allowed_axioms", Lean.toJson (allowed.map Lean.Name.toString)),
    ("encountered_axioms", Lean.toJson (foundAxioms.toList.map Lean.Name.toString)),
    ("node_count", Lean.toJson nodes.size),
    ("nodes", Lean.Json.arr nodes)]
  let report := Lean.Json.mkObj [
    ("scope", Lean.toJson "Actual checked additional statements and definitions. The graph expands the proof bodies of AdditionalResults, with the independently checked original project and pinned libraries as its boundary. The original principal proof graph is separately recorded in dependency-graph.json."),
    ("required_separate_gate", Lean.toJson "Require complete successful ordinary compiler runs for every compiled project stage and the final module, bound to the current source and artifact hashes. This audit output alone is not a successful verification."),
    ("expanded_project_modules", Lean.toJson (expandedProjectModules.map Lean.Name.toString)),
    ("required_statements", Lean.Json.arr statements),
    ("defining_constants", Lean.Json.arr definitions),
    ("allowed_axioms", Lean.toJson (allowed.map Lean.Name.toString)),
    ("dependency_node_count", Lean.toJson nodes.size)]
  Lean.Elab.Command.liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/additional-dependency-graph.json" graph.pretty
  Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/additional-statements-and-axioms.json" report.pretty
  Lean.logInfo m!"ADDITIONAL AUDIT PASSED: {required.size} kernel theorems, {nodes.size} transitive logical declarations; only the standard axioms."
