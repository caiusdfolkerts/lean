module
public import PureGP.Core
public import PureGP.Relations
public import PureGP.SupportCore
public import Init.Prelude
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Papers.GaleKernelBasis
public import Papers.RationalityTenRestrictedColumns
public import Papers.RationalKernelCharts
public import Papers.ActualHomogeneousFaceRanks
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Lean.Elab.Tactic.Omega
public import Papers.FiniteProjectionBoundary
public import Papers.FiniteProjectionData
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# The three-term relation for ordinary five-row determinants

No independence of the common three rows, or of the four additional labels,
is assumed. A nonsingular chart is used only in the first lemma. The global
theorem either obtains such a chart from one of the three relevant minors,
or reduces immediately to zero. 
-/

/-! Canonical source bundle; each original file retains its own scopes. -/

/- The pure sign-propagation foundation is imported from PureGP.Core. -/

section BundlePart1
/- Source: Papers/GPRealSign.lean -/






@[expose] public section

/-!
# Real signs interpreted by the finite GP checker

The finite three-valued signs are the signs of ordinary real numbers.
The permitted three-product patterns follow from their real sum being zero.

-/

noncomputable section
namespace Papers.RationalityTen.PureGP

def realSign (x : ℝ) : Sign :=
  if x < 0 then .negative else if x = 0 then .zero else .positive

@[simp] theorem realSign_of_negative {x : ℝ} (h : x < 0) : realSign x = .negative := by
  simp [realSign, h]

@[simp] theorem realSign_zero : realSign 0 = .zero := by simp [realSign]

@[simp] theorem realSign_of_positive {x : ℝ} (h : 0 < x) : realSign x = .positive := by
  simp [realSign, not_lt_of_ge h.le, ne_of_gt h]

theorem realSign_negate (x : ℝ) : realSign (-x) = (realSign x).negate := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [realSign_of_negative h, realSign_of_positive (neg_pos.mpr h)]
    rfl
  · simp [Sign.negate]
  · rw [realSign_of_positive h, realSign_of_negative (neg_neg_of_pos h)]
    rfl

theorem realSign_multiply (x y : ℝ) :
    realSign (x * y) = (realSign x).multiply (realSign y) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [realSign_of_negative hx, realSign_of_negative hy,
        realSign_of_positive (mul_pos_of_neg_of_neg hx hy)]
      rfl
    · simp [Sign.multiply, realSign_of_negative hx]
    · rw [realSign_of_negative hx, realSign_of_positive hy,
        realSign_of_negative (mul_neg_of_neg_of_pos hx hy)]
      rfl
  · simp [Sign.multiply]
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [realSign_of_positive hx, realSign_of_negative hy,
        realSign_of_negative (mul_neg_of_pos_of_neg hx hy)]
      rfl
    · simp [Sign.multiply, realSign_of_positive hx]
    · rw [realSign_of_positive hx, realSign_of_positive hy,
        realSign_of_positive (mul_pos hx hy)]
      rfl

theorem realSign_positive_scale (x t : ℝ) (ht : 0 < t) : realSign (t * x) = realSign x := by
  rw [realSign_multiply, realSign_of_positive ht]
  cases realSign x <;> rfl

def realWithNegation (negate : Bool) (x : ℝ) : ℝ := if negate then -x else x

theorem realSign_withNegation (b : Bool) (x : ℝ) :
    realSign (realWithNegation b x) = Sign.withNegation b (realSign x) := by
  cases b
  · rfl
  · exact realSign_negate x

private theorem sum_zero_signs_allowed (x y z : ℝ) (h : x + y + z = 0) :
    Bool.or
      (Bool.and (realSign x).isZero (Bool.and (realSign y).isZero (realSign z).isZero))
      (Bool.and
        (Bool.or (realSign x).isNegative
          (Bool.or (realSign y).isNegative (realSign z).isNegative))
        (Bool.or (realSign x).isPositive
          (Bool.or (realSign y).isPositive (realSign z).isPositive))) = true := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy <;>
      rcases lt_trichotomy z 0 with hz | rfl | hz
  all_goals
    simp_all only [realSign_of_negative, realSign_zero, realSign_of_positive,
      Sign.isZero, Sign.isNegative, Sign.isPositive, Bool.and_false,
      Bool.and_true, Bool.or_false, Bool.or_true]
  all_goals linarith

/-- The exact boolean GP rule follows from the ordinary real polynomial
identity, including zero terms. -/
theorem gpAllowed_of_real_identity (negations : Triple Bool) (x : Six ℝ)
    (h : realWithNegation negations.a (x.a * x.b) +
      realWithNegation negations.b (x.c * x.d) +
      realWithNegation negations.c (x.e * x.f) = 0) :
    gpAllowed negations
      ⟨realSign x.a, realSign x.b, realSign x.c,
        realSign x.d, realSign x.e, realSign x.f⟩ = true := by
  have hs := sum_zero_signs_allowed _ _ _ h
  simp only [realSign_withNegation, realSign_multiply] at hs
  exact hs

def Relation.RealIdentity (relation : Relation) (values : Nat → ℝ) : Prop :=
  realWithNegation relation.negations.a
      (values relation.indices.a * values relation.indices.b) +
    realWithNegation relation.negations.b
      (values relation.indices.c * values relation.indices.d) +
    realWithNegation relation.negations.c
      (values relation.indices.e * values relation.indices.f) = 0

theorem Relation.allowed_realSigns (relation : Relation) (values : Nat → ℝ)
    (h : relation.RealIdentity values) :
    relation.allowed (fun i => realSign (values i)) = true :=
  gpAllowed_of_real_identity relation.negations
    ⟨values relation.indices.a, values relation.indices.b,
      values relation.indices.c, values relation.indices.d,
      values relation.indices.e, values relation.indices.f⟩ h

theorem realWithNegation_mul (b : Bool) (t x : ℝ) :
    realWithNegation b (t * x) = t * realWithNegation b x := by
  cases b <;> simp [realWithNegation]

theorem Relation.RealIdentity.scale {relation : Relation} {values : Nat → ℝ}
    (h : relation.RealIdentity values) (t : ℝ) :
    relation.RealIdentity (fun i => t * values i) := by
  have hprod (x y : ℝ) : (t * x) * (t * y) = (t * t) * (x * y) := by ring
  unfold Relation.RealIdentity at h ⊢
  simp only [hprod, realWithNegation_mul]
  simp only [realWithNegation_mul] at h
  rw [← mul_add, ← mul_add, h, mul_zero]

end Papers.RationalityTen.PureGP

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/RationalityTenSupportDeterminantStandalone.lean -/










@[expose] public section

/-!
# Support comparisons for actual homogeneous determinants

This file is an uncompiled proof draft, prepared while the execution
environment was unavailable. No declaration in it is certified by a build.
The hypotheses use ordinary vectors and their ordinary scalar products.
-/

namespace Papers.RationalityTen.SupportDeterminantStandalone

open Matrix
open scoped BigOperators

abbrev V := Fin 5 → ℝ

def pairing (x y : V) : ℝ := ∑ k, x k * y k

@[simp] theorem pairing_add_left (x y z : V) :
    pairing (x + y) z = pairing x z + pairing y z := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

@[simp] theorem pairing_smul_left (a : ℝ) (x y : V) :
    pairing (a • x) y = a * pairing x y := by
  simp [pairing, Finset.mul_sum, mul_assoc]

@[simp] theorem pairing_add_right (x y z : V) :
    pairing x (y + z) = pairing x y + pairing x z := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

@[simp] theorem pairing_smul_right (a : ℝ) (x y : V) :
    pairing x (a • y) = a * pairing x y := by
  simp [pairing, Finset.mul_sum, mul_left_comm, mul_assoc]

@[simp] theorem pairing_zero_right (x : V) : pairing x 0 = 0 := by
  simp [pairing]

@[simp] theorem pairing_neg_right (x y : V) :
    pairing x (-y) = -pairing x y := by
  simp [pairing, Finset.sum_neg_distrib]

theorem det_zero_of_annihilator
    (A : Matrix (Fin 5) (Fin 5) ℝ) (u : V)
    (hu : u ≠ 0) (h : ∀ i, pairing (A i) u = 0) :
    A.det = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨u, hu, ?_⟩
  ext i
  exact h i

/-- Replacing the sole row outside a supporting hyperplane. -/
theorem replacement_identity
    (A : Matrix (Fin 5) (Fin 5) ℝ) (i : Fin 5) (w u : V)
    (hu : u ≠ 0)
    (hrows : ∀ j, j ≠ i → pairing (A j) u = 0) :
    (A.updateRow i w).det * pairing (A i) u =
      A.det * pairing w u := by
  let z : V := pairing (A i) u • w + (-pairing w u) • A i
  have hz : ∀ j, pairing ((A.updateRow i z) j) u = 0 := by
    intro j
    by_cases hj : j = i
    · subst j
      rw [Matrix.updateRow_self]
      simp only [z, pairing_add_left, pairing_smul_left]
      ring
    · simpa only [Matrix.updateRow_ne hj] using hrows j hj
  have hdet := det_zero_of_annihilator (A.updateRow i z) u hu hz
  rw [show z = pairing (A i) u • w + (-pairing w u) • A i from rfl,
    Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.det_updateRow_smul] at hdet
  have hself : A.updateRow i (A i) = A := by
    ext j k
    by_cases hj : j = i <;> simp [Matrix.updateRow_apply, hj]
  rw [hself] at hdet
  nlinarith

/-- A positive scalar relates two numbers, including simultaneous zeros. -/
def PosRatio (x y : ℝ) : Prop := ∃ t : ℝ, 0 < t ∧ y = t * x

namespace PosRatio

theorem refl (x : ℝ) : PosRatio x x := ⟨1, by norm_num, by ring⟩

theorem trans {x y z : ℝ} (hxy : PosRatio x y) (hyz : PosRatio y z) :
    PosRatio x z := by
  obtain ⟨s, hs, rfl⟩ := hxy
  obtain ⟨t, ht, rfl⟩ := hyz
  exact ⟨t * s, mul_pos ht hs, by ring⟩

theorem symm {x y : ℝ} (h : PosRatio x y) : PosRatio y x := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t⁻¹, inv_pos.mpr ht, by field_simp [ne_of_gt ht]⟩

theorem neg {x y : ℝ} (h : PosRatio x y) : PosRatio (-x) (-y) := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t, ht, by ring⟩

theorem nonzero {x y : ℝ} (h : PosRatio x y) (hx : x ≠ 0) : y ≠ 0 := by
  obtain ⟨t, ht, rfl⟩ := h
  exact mul_ne_zero (ne_of_gt ht) hx

theorem product_pos {a x y : ℝ} (hx : PosRatio a x) (hy : PosRatio a y)
    (ha : a ≠ 0) : 0 < x * y := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  have hp := mul_pos (mul_pos hs ht) (sq_pos_of_ne_zero ha)
  nlinarith

end PosRatio

theorem replacement_posRatio
    (A : Matrix (Fin 5) (Fin 5) ℝ) (i : Fin 5) (w u : V)
    (hrows : ∀ j, j ≠ i → pairing (A j) u = 0)
    (hi : 0 < pairing (A i) u) (hw : 0 < pairing w u) :
    PosRatio A.det (A.updateRow i w).det := by
  have hu : u ≠ 0 := by
    intro h
    simp [h] at hi
  have heq := replacement_identity A i w u hu hrows
  refine ⟨pairing w u / pairing (A i) u, div_pos hw hi, ?_⟩
  apply (mul_right_cancel₀ (ne_of_gt hi))
  calc
    (A.updateRow i w).det * pairing (A i) u = A.det * pairing w u := heq
    _ = (pairing w u / pairing (A i) u * A.det) * pairing (A i) u := by
      field_simp

abbrev Labels := Fin 10

def rowMatrix (p : Labels → V) (r : Fin 5 → Labels) :
    Matrix (Fin 5) (Fin 5) ℝ := fun i => p (r i)

def minor (p : Labels → V) (r : Fin 5 → Labels) : ℝ :=
  (rowMatrix p r).det

theorem minor_permute (p : Labels → V) (r : Fin 5 → Labels)
    (σ : Equiv.Perm (Fin 5)) :
    minor p (r ∘ σ) = (Equiv.Perm.sign σ : ℝ) * minor p r := by
  exact Matrix.det_permute σ (rowMatrix p r)

def appendLabel (r : Fin 4 → Labels) (x : Labels) : Fin 5 → Labels :=
  ![r 0, r 1, r 2, r 3, x]

theorem common_support_posRatio
    (p : Labels → V) (u : V) (r : Fin 4 → Labels) (x y : Labels)
    (hr : ∀ i, pairing (p (r i)) u = 0)
    (hx : 0 < pairing (p x) u) (hy : 0 < pairing (p y) u) :
    PosRatio (minor p (appendLabel r x)) (minor p (appendLabel r y)) := by
  have hm : (rowMatrix p (appendLabel r x)).updateRow 4 (p y) =
      rowMatrix p (appendLabel r y) := by
    ext i j
    fin_cases i <;> simp [rowMatrix, appendLabel, Matrix.updateRow_apply]
  change PosRatio (rowMatrix p (appendLabel r x)).det
    (rowMatrix p (appendLabel r y)).det
  rw [← hm]
  apply replacement_posRatio (u := u)
  · intro j hj
    fin_cases j <;> simp_all [rowMatrix, appendLabel]
  · simpa [rowMatrix, appendLabel] using hx
  · exact hy

theorem two_supports_zero
    (p : Labels → V) (r : Fin 5 → Labels) (i : Fin 5) (a b : V)
    (ha : ∀ j, j ≠ i → pairing (p (r j)) a = 0)
    (hb : ∀ j, j ≠ i → pairing (p (r j)) b = 0)
    (hia : 0 < pairing (p (r i)) a)
    (z : V) (hza : pairing z a = 0) (hzb : 0 < pairing z b) :
    minor p r = 0 := by
  let u : V := pairing (p (r i)) a • b + (-pairing (p (r i)) b) • a
  have huz : 0 < pairing z u := by
    simp only [u, pairing_add_right, pairing_smul_right, hza, mul_zero, add_zero]
    exact mul_pos hia hzb
  have hu : u ≠ 0 := by
    intro h
    simp [h] at huz
  apply det_zero_of_annihilator (rowMatrix p r) u hu
  intro j
  by_cases hj : j = i
  · subst j
    simp [u, rowMatrix] <;> ring
  · simp [u, rowMatrix, ha j hj, hb j hj]

end Papers.RationalityTen.SupportDeterminantStandalone

end
end BundlePart2

section BundlePart3
/- Source: Papers/ActualGaleRanks.lean -/








@[expose] public section

/-!
# Actual Gale coordinates and complementary rank witnesses

The Gale matrix is a basis of the kernel of the actual homogeneous vertex
matrix.  Every rank statement below concerns those actual coordinates.
In particular, the four-space complementary to a quadrilateral contains
exactly the six complementary labels: each of the four other Gale vectors
is outside it.  This uses independence of three distinct extreme vertices,
not a general-position hypothesis.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity.ActualGale

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeIncidenceConfiguration Papers.ActualThreeVertexIndependence

def labelSpan {n r : ℕ} (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) :
    Submodule ℝ (Fin r → ℝ) := Submodule.span ℝ (p '' (↑S : Set (Fin n)))

theorem rank_mono {n r : ℕ} (p : Fin n → Fin r → ℝ)
    {S T : Finset (Fin n)} (hST : S ⊆ T) : subsetRank p S ≤ subsetRank p T :=
  Submodule.finrank_mono (Submodule.span_mono (Set.image_mono hST))

theorem rank_le_ambient {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : subsetRank p S ≤ r := by
  have h := (Submodule.span ℝ (p '' (↑S : Set (Fin n)))).finrank_le
  change finrank ℝ (Submodule.span ℝ (p '' (↑S : Set (Fin n)))) ≤ r
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using h

theorem rank_insert_of_notMem {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) (i : Fin n) (hi : p i ∉ labelSpan p S) :
    subsetRank p (insert i S) = subsetRank p S + 1 := by
  unfold subsetRank
  rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert, sup_comm]
  exact Submodule.finrank_sup_span_singleton hi

theorem independent_of_rank {n r k : ℕ} (p : Fin n → Fin r → ℝ)
    (b : Fin k → Fin n) (h : subsetRank p (Finset.univ.image b) = k) :
    LinearIndependent ℝ (fun j => p (b j)) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  have hrange : Set.range (fun j => p (b j)) =
      p '' (↑(Finset.univ.image b) : Set (Fin n)) := by
    ext v
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨b j, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨i, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  change Fintype.card (Fin k) =
    finrank ℝ (Submodule.span ℝ (Set.range (fun j => p (b j))))
  rw [Fintype.card_fin, hrange]
  exact h.symm

theorem outside_actual_face_notMem {d n : ℕ} (P : ConvexPolytope d)
    (lab : Fin n ≃ P.vertices) (F : PolytopeFace P)
    (T : Finset (Fin n)) (hT : T ⊆ actualFaceLabels P lab F)
    (i : Fin n) (hi : i ∉ actualFaceLabels P lab F) :
    vertexCoordinates P lab i ∉ labelSpan (vertexCoordinates P lab) T := by
  obtain ⟨f, hf⟩ := exists_supportsFace P F.isFace
  let a := coefficientVector f
  have hvalue (j : Fin n) : a ⬝ᵥ vertexCoordinates P lab j = f (lab j).val :=
    coefficient_dot_homogeneous f (lab j).val
  have hker : labelSpan (vertexCoordinates P lab) T ≤ (dotLinear a).ker := by
    apply Submodule.span_le.mpr
    rintro v ⟨j, hj, rfl⟩
    change a ⬝ᵥ vertexCoordinates P lab j = 0
    rw [hvalue]
    exact hf.eq_zero ((mem_actualFaceLabels P lab F j).mp (hT hj))
  intro hmem
  have hz : f (lab i).val = 0 := by
    rw [← hvalue]
    exact hker hmem
  apply hi
  apply (mem_actualFaceLabels P lab F i).mpr
  exact (hf.mem_iff _).mpr ⟨subset_convexHull ℝ _ (lab i).property, hz⟩

theorem actual_face_rank_insert {d n : ℕ} (P : ConvexPolytope d)
    (lab : Fin n ≃ P.vertices) (F : PolytopeFace P)
    (i : Fin n) (hi : i ∉ actualFaceLabels P lab F) :
    subsetRank (vertexCoordinates P lab) (insert i (actualFaceLabels P lab F)) =
      faceDim F.carrier + 2 := by
  rw [rank_insert_of_notMem _ _ _
    (outside_actual_face_notMem P lab F _ (Finset.Subset.refl _) i hi),
    actualFaceLabels_rank]

structure Coordinates (P : ConvexPolytope 4) (lab : Fin 10 ≃ P.vertices) where
  vectors : Matrix (Fin 10) (Fin 5) ℝ
  spanning : Spans vectors
  kernel_range : vectors.mulVecLin.range =
    (Matrix.of (vertexCoordinates P lab)).transpose.mulVecLin.ker

theorem coordinates_exist (P : ConvexPolytope 4) (lab : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim) : Nonempty (Coordinates P lab) := by
  let A : Matrix (Fin 5) (Fin 10) ℝ := (Matrix.of (vertexCoordinates P lab)).transpose
  have hrank : A.rank = 5 := by
    change (Matrix.of (vertexCoordinates P lab)).transpose.rank = 5
    rw [Matrix.rank_transpose]
    exact (spans_iff_matrix_rank _).mp (vertexCoordinates_spans P lab hP)
  have hrows : LinearIndependent ℝ A.row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa [Set.finrank, Matrix.rank_eq_finrank_span_row] using hrank.symm
  obtain ⟨k, B, hdim, hB, hAB, hexact⟩ := exists_gale_matrix A hrows
  have hk : k = 5 := by omega
  subst k
  exact ⟨⟨B, hB, hexact⟩⟩

namespace Coordinates

variable {P : ConvexPolytope 4} {lab : Fin 10 ≃ P.vertices}

/-- Rank duality is proved from the kernel construction, with no supplied
dual matroid or abstract rank axiom. -/
theorem complementary_rank (G : Coordinates P lab) (S : Finset (Fin 10)) :
    subsetRank (vertexCoordinates P lab) S + 5 = S.card + subsetRank G.vectors Sᶜ := by
  let A : Matrix (Fin 5) (Fin 10) ℝ := (Matrix.of (vertexCoordinates P lab)).transpose
  have hinj : Function.Injective G.vectors.mulVecLin :=
    Papers.RationalKernelCharts.mulVec_injective_of_spanning_rows G.spanning
  have h := Papers.RationalityTen.gale_subset_rank_identity A.mulVecLin G.vectors.mulVecLin
    hinj G.kernel_range S
  rw [restricted_columns_range] at h
  have hright :
      finrank ℝ ((Papers.RationalityTen.outsideRestriction (K := ℝ) S).comp
        G.vectors.mulVecLin).range = subsetRank G.vectors Sᶜ := by
    let C : Matrix {i : Fin 10 // i ∉ S} (Fin 5) ℝ :=
      Matrix.of (fun i j => G.vectors i.val j)
    have hC : (Papers.RationalityTen.outsideRestriction (K := ℝ) S).comp
        G.vectors.mulVecLin = C.mulVecLin := by ext x i; rfl
    rw [hC]
    change C.rank = _
    have hrange : Set.range C.row = G.vectors '' (↑Sᶜ : Set (Fin 10)) := by
      ext v
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, by simpa using i.property, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, by simpa using hi⟩, rfl⟩
    rw [Matrix.rank_eq_finrank_span_row, hrange]
    rfl
  rw [hright] at h
  have hAcol : A.col = vertexCoordinates P lab := rfl
  rw [hAcol] at h
  have hfive : finrank ℝ (Fin 5 → ℝ) = 5 := by simp
  rw [hfive] at h
  exact h

theorem rank_eq_of_primal_complement_rank (G : Coordinates P lab)
    (S : Finset (Fin 10)) (h : subsetRank (vertexCoordinates P lab) Sᶜ = 5) :
    subsetRank G.vectors S = S.card := by
  have hd := G.complementary_rank Sᶜ
  have hc := Finset.card_compl S
  have hle : S.card ≤ 10 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ S
  simp only [compl_compl, Fintype.card_fin] at hd hc
  omega

theorem quadrilateral_rank (G : Coordinates P lab) (R : Face P 2)
    (hcard : (actualFaceLabels P lab R.val).card = 4) :
    subsetRank G.vectors (actualFaceLabels P lab R.val)ᶜ = 4 := by
  have hd := G.complementary_rank (actualFaceLabels P lab R.val)
  rw [actualFaceLabels_rank, R.property, hcard] at hd
  omega

theorem outside_quadrilateral_hyperplane (G : Coordinates P lab) (R : Face P 2)
    (hcard : (actualFaceLabels P lab R.val).card = 4)
    (i : Fin 10) (hi : i ∈ actualFaceLabels P lab R.val) :
    G.vectors i ∉ labelSpan G.vectors (actualFaceLabels P lab R.val)ᶜ := by
  let Q := actualFaceLabels P lab R.val
  have hQ : Q.card = 4 := hcard
  have hiQ : i ∈ Q := hi
  have hsmall : (Q.erase i).card = 3 := by rw [Finset.card_erase_of_mem hiQ, hQ]
  have hvertices : P.vertices.card = 10 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe] using
      (Nat.card_congr lab).symm
  have hli := vertexCoordinates_small_independent P lab (by omega) (Q.erase i) (by omega)
  have hprimal : subsetRank (vertexCoordinates P lab) (Q.erase i) = 3 := by
    have hh := finrank_span_eq_card hli
    rw [range_finset_family, Fintype.card_coe, hsmall] at hh
    exact hh
  have hd := G.complementary_rank (Q.erase i)
  have hc : (Q.erase i)ᶜ = insert i Qᶜ := by
    ext j
    by_cases hji : j = i <;> simp [hji]
  rw [hprimal, hsmall, hc] at hd
  have hnew : subsetRank G.vectors (insert i Qᶜ) = 5 := by omega
  have hold : subsetRank G.vectors Qᶜ = 4 := G.quadrilateral_rank R hcard
  intro hmem
  have heq : labelSpan G.vectors (insert i Qᶜ) = labelSpan G.vectors Qᶜ := by
    change Submodule.span ℝ ((fun j => G.vectors j) '' (↑(insert i Qᶜ) : Set (Fin 10))) =
      Submodule.span ℝ ((fun j => G.vectors j) '' (↑Qᶜ : Set (Fin 10)))
    rw [Finset.coe_insert, Set.image_insert_eq]
    change G.vectors i ∈ Submodule.span ℝ
      ((fun j => G.vectors j) '' (↑Qᶜ : Set (Fin 10))) at hmem
    exact Submodule.span_insert_eq_span hmem
  have hr := congrArg (fun W : Submodule ℝ (Fin 5 → ℝ) => finrank ℝ W) heq
  change subsetRank G.vectors (insert i Qᶜ) = subsetRank G.vectors Qᶜ at hr
  omega

end Coordinates
end Papers.RationalityTen.ChirotopeDensity.ActualGale

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/GPActualSupportSigns.lean -/








@[expose] public section

/-!
# Actual facet supports supply the GP initial signs

These lemmas use ordinary real determinants. Four rows on a common facet
and two outside rows give a positive determinant ratio, including the
possibility that both determinants vanish. Permutations supply the exact
sign recorded in the finite support graph. Facet and polygon rank bounds
supply the zero nodes; one triangular-face/facet/outside flag supplies a
nonzero anchor. No triangulation or generic-position condition occurs.


-/

noncomputable section
namespace Papers.RationalityTen.GPActualSupportSigns

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeIncidenceConfiguration
open Papers.RationalityTen.ChirotopeDensity
open Papers.RationalityTen.ChirotopeDensity.ActualGale
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Papers.RationalityTen.SupportDeterminantStandalone
open Papers.RationalityTen.PureGP

theorem positive_ratio_sign {x y : ℝ} (h : PosRatio x y) (scale : ℝ) :
    realSign (scale * y) = realSign (scale * x) := by
  obtain ⟨t, ht, rfl⟩ := h
  rw [show scale * (t * x) = t * (scale * x) by ring]
  exact realSign_positive_scale _ _ ht

/-- This is the signed edge rule consumed by the finite initializer.
All combinatorial equalities in the hypotheses are finite tuple or
permutation-sign checks. -/
theorem signed_support_edge (p : Labels → V) (normal : V)
    (four : Fin 4 → Labels) (x y : Labels)
    (leftRows rightRows : Fin 5 → Labels)
    (leftPerm rightPerm : Equiv.Perm (Fin 5)) (negate : Bool)
    (hleft : appendLabel four x = leftRows ∘ leftPerm)
    (hright : appendLabel four y = rightRows ∘ rightPerm)
    (hparity : Equiv.Perm.sign rightPerm =
      (if negate then (-1 : ℤˣ) else 1) * Equiv.Perm.sign leftPerm)
    (hfour : ∀ i, pairing (p (four i)) normal = 0)
    (hx : 0 < pairing (p x) normal) (hy : 0 < pairing (p y) normal)
    (scale : ℝ) :
    realSign (scale * SupportDeterminantStandalone.minor p rightRows) =
      Sign.withNegation negate (realSign (scale * SupportDeterminantStandalone.minor p leftRows)) := by
  obtain ⟨t, ht, hxy⟩ := common_support_posRatio p normal four x y hfour hx hy
  rw [hleft, hright, minor_permute, minor_permute] at hxy
  have hnonzero : (Equiv.Perm.sign leftPerm : ℝ) ≠ 0 := by
    exact_mod_cast (Equiv.Perm.sign leftPerm).ne_zero
  have hparityR := congrArg (fun u : ℤˣ => (u : ℝ)) hparity
  cases negate
  · have hs : (Equiv.Perm.sign rightPerm : ℝ) = (Equiv.Perm.sign leftPerm : ℝ) := by
      simpa using hparityR
    rw [hs] at hxy
    have hvalue : SupportDeterminantStandalone.minor p rightRows = t * SupportDeterminantStandalone.minor p leftRows := by
      apply mul_left_cancel₀ hnonzero
      calc
        _ = t * ((Equiv.Perm.sign leftPerm : ℝ) * SupportDeterminantStandalone.minor p leftRows) := hxy
        _ = _ := by ring
    change realSign (scale * SupportDeterminantStandalone.minor p rightRows) = realSign (scale * SupportDeterminantStandalone.minor p leftRows)
    exact positive_ratio_sign ⟨t, ht, hvalue⟩ scale
  · have hs : (Equiv.Perm.sign rightPerm : ℝ) = -(Equiv.Perm.sign leftPerm : ℝ) := by
      simpa using hparityR
    rw [hs] at hxy
    have hvalue : SupportDeterminantStandalone.minor p rightRows = -(t * SupportDeterminantStandalone.minor p leftRows) := by
      apply mul_left_cancel₀ hnonzero
      calc
        _ = - (-(Equiv.Perm.sign leftPerm : ℝ) * SupportDeterminantStandalone.minor p rightRows) := by ring
        _ = -(t * ((Equiv.Perm.sign leftPerm : ℝ) * SupportDeterminantStandalone.minor p leftRows)) :=
          congrArg Neg.neg hxy
        _ = _ := by ring
    rw [hvalue, show scale * -(t * SupportDeterminantStandalone.minor p leftRows) =
      -(t * (scale * SupportDeterminantStandalone.minor p leftRows)) by ring,
      realSign_negate, realSign_positive_scale _ _ ht]
    rfl

theorem rowMatrix_rank (p : Labels → V) (rows : Fin 5 → Labels) :
    (rowMatrix p rows).rank = subsetRank p (Finset.univ.image rows) := by
  have hrange : Set.range (rowMatrix p rows).row =
      p '' (↑(Finset.univ.image rows) : Set Labels) := by
    ext v
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨rows i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨j, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [Matrix.rank_eq_finrank_span_row, hrange]
  rfl

theorem minor_zero_of_rank_le_four (p : Labels → V) (rows : Fin 5 → Labels)
    (h : subsetRank p (Finset.univ.image rows) ≤ 4) : SupportDeterminantStandalone.minor p rows = 0 := by
  by_contra hn
  have hr := Matrix.rank_of_det_ne_zero (A := rowMatrix p rows) hn
  rw [rowMatrix_rank, Fintype.card_fin] at hr
  omega

theorem minor_nonzero_of_rank_five (p : Labels → V) (rows : Fin 5 → Labels)
    (h : subsetRank p (Finset.univ.image rows) = 5) : SupportDeterminantStandalone.minor p rows ≠ 0 := by
  have hli : LinearIndependent ℝ (rowMatrix p rows).row :=
    independent_of_rank p rows h
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp hli)).ne_zero

theorem rank_insert_le (p : Labels → V) (S : Finset Labels) (i : Labels) :
    subsetRank p (insert i S) ≤ subsetRank p S + 1 := by
  by_cases hi : p i ∈ labelSpan p S
  · have heq : labelSpan p (insert i S) = labelSpan p S := by
      unfold labelSpan
      rw [Finset.coe_insert, Set.image_insert_eq]
      exact Submodule.span_insert_eq_span hi
    have hr := congrArg (fun W : Submodule ℝ V => finrank ℝ W) heq
    change subsetRank p (insert i S) = subsetRank p S at hr
    omega
  · rw [rank_insert_of_notMem p S i hi]

variable {P : ConvexPolytope 4} {lab : Fin 10 ≃ VertexType P} {B : Boundary 9}

theorem actual_support_edge (hB : RealizesBoundary P lab B)
    (F : Finset Labels) (hF : F ∈ B.facets)
    (four : Fin 4 → Labels) (x y : Labels)
    (leftRows rightRows : Fin 5 → Labels)
    (leftPerm rightPerm : Equiv.Perm (Fin 5)) (negate : Bool)
    (hleft : appendLabel four x = leftRows ∘ leftPerm)
    (hright : appendLabel four y = rightRows ∘ rightPerm)
    (hparity : Equiv.Perm.sign rightPerm =
      (if negate then (-1 : ℤˣ) else 1) * Equiv.Perm.sign leftPerm)
    (hfour : ∀ i, four i ∈ F) (hx : x ∉ F) (hy : y ∉ F)
    (scale : ℝ) :
    realSign (scale * SupportDeterminantStandalone.minor (vertexCoordinates P lab) rightRows) =
      Sign.withNegation negate
        (realSign (scale * SupportDeterminantStandalone.minor (vertexCoordinates P lab) leftRows)) := by
  let G := hB.facetFor ⟨F, hF⟩
  have hlabels : actualFaceLabels P lab ⟨G.val.val, G.property.1⟩ = F :=
    hB.facetFor_labels ⟨F, hF⟩
  have hs := actualFacetLabels_strictSupport P lab G
  rw [hlabels] at hs
  apply signed_support_edge (vertexCoordinates P lab)
    (coefficientVector (chosenFacetForm P G)) four x y leftRows rightRows
    leftPerm rightPerm negate hleft hright hparity
  · intro i
    simpa only [pairing, dotProduct, mul_comm] using hs.1 (four i) (hfour i)
  · simpa only [pairing, dotProduct, mul_comm] using hs.2 x hx
  · simpa only [pairing, dotProduct, mul_comm] using hs.2 y hy

theorem actual_facet_zero (hP : P.IsFullDim) (hB : RealizesBoundary P lab B)
    (F : Finset Labels) (hF : F ∈ B.facets) (rows : Fin 5 → Labels)
    (hrows : ∀ i, rows i ∈ F) : SupportDeterminantStandalone.minor (vertexCoordinates P lab) rows = 0 := by
  let G := hB.facetFor ⟨F, hF⟩
  have hlabels : actualFaceLabels P lab ⟨G.val.val, G.property.1⟩ = F :=
    hB.facetFor_labels ⟨F, hF⟩
  have hdim : faceDim G.val.val = 3 := by
    have h := G.property.2
    rw [hP] at h
    omega
  have hrank : subsetRank (vertexCoordinates P lab) F = 4 := by
    rw [← hlabels, actualFaceLabels_rank, hdim]
  apply minor_zero_of_rank_le_four (vertexCoordinates P lab) rows
  apply (rank_mono (vertexCoordinates P lab) ?_).trans hrank.le
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact hrows j

theorem actual_polygon_plus_point_zero (hB : RealizesBoundary P lab B)
    (R : Finset Labels) (hR : R ∈ B.polygons) (v : Labels)
    (rows : Fin 5 → Labels) (hrows : ∀ i, rows i ∈ insert v R) :
    SupportDeterminantStandalone.minor (vertexCoordinates P lab) rows = 0 := by
  let G := hB.polygonFor ⟨R, hR⟩
  have hlabels : actualFaceLabels P lab G.val = R := hB.polygonFor_labels ⟨R, hR⟩
  have hrank : subsetRank (vertexCoordinates P lab) R = 3 := by
    rw [← hlabels, actualFaceLabels_rank, G.property]
  have hins := rank_insert_le (vertexCoordinates P lab) R v
  rw [hrank] at hins
  apply minor_zero_of_rank_le_four (vertexCoordinates P lab) rows
  apply (rank_mono (vertexCoordinates P lab) ?_).trans hins
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact hrows j

theorem actual_flag_anchor_nonzero (hB : RealizesBoundary P lab B)
    (R F : Finset Labels) (hR : R ∈ B.polygons) (hF : F ∈ B.facets)
    (inner outside : Labels) (hi : inner ∉ R) (hout : outside ∉ F)
    (hinside : insert inner R ⊆ F) (rows : Fin 5 → Labels)
    (hrows : Finset.univ.image rows = insert outside (insert inner R)) :
    SupportDeterminantStandalone.minor (vertexCoordinates P lab) rows ≠ 0 := by
  let Q := hB.polygonFor ⟨R, hR⟩
  have hQ : actualFaceLabels P lab Q.val = R := hB.polygonFor_labels ⟨R, hR⟩
  have hfour : subsetRank (vertexCoordinates P lab) (insert inner R) = 4 := by
    have h := actual_face_rank_insert P lab Q.val inner (by rwa [hQ])
    rw [hQ, Q.property] at h
    exact h
  let G := hB.facetFor ⟨F, hF⟩
  have hG : actualFaceLabels P lab ⟨G.val.val, G.property.1⟩ = F :=
    hB.facetFor_labels ⟨F, hF⟩
  have hn : vertexCoordinates P lab outside ∉
      labelSpan (vertexCoordinates P lab) (insert inner R) := by
    apply outside_actual_face_notMem P lab ⟨G.val.val, G.property.1⟩ _
    · rwa [hG]
    · rwa [hG]
  apply minor_nonzero_of_rank_five (vertexCoordinates P lab) rows
  rw [hrows, rank_insert_of_notMem _ _ _ hn, hfour]

def normalizedAssignment (p : Labels → V) (rows : Nat → Fin 5 → Labels)
    (anchor : Nat) : Nat → Sign :=
  fun i => realSign ((SupportDeterminantStandalone.minor p (rows anchor))⁻¹ * SupportDeterminantStandalone.minor p (rows i))

theorem normalizedAssignment_anchor (p : Labels → V) (rows : Nat → Fin 5 → Labels)
    (anchor : Nat) (hanchor : SupportDeterminantStandalone.minor p (rows anchor) ≠ 0) :
    normalizedAssignment p rows anchor anchor = .positive := by
  unfold normalizedAssignment
  rw [inv_mul_cancel₀ hanchor]
  exact realSign_of_positive zero_lt_one

end Papers.RationalityTen.GPActualSupportSigns

end
end
end BundlePart4

/- The pure sign-propagation foundation is imported from PureGP.Relations. -/

/- The pure sign-propagation foundation is imported from PureGP.SupportCore. -/

section BundlePart7
/- Source: Papers/GPFiniteGeometryData.lean -/






@[expose] public section

/-!
# Finite data connecting support and GP certificates to labelled rows

All proof fields in this module are equalities or memberships of finite
tuples, permutations, or face masks. Their real determinant meaning is
proved separately. The actual geometry cannot be supplied as a hidden
rank or sign assumption inside these finite data.
-/

namespace Papers.RationalityTen.GPFiniteGeometry

open Papers.RationalityTen.PureGP
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection

abbrev Label := Fin 10

def labelOfNat (n : Nat) : Label := ⟨n % 10, Nat.mod_lt _ (by decide)⟩

noncomputable def minorRows (index : Nat) : Fin 5 → Label :=
  ![labelOfNat (Data.subset index).a, labelOfNat (Data.subset index).b,
    labelOfNat (Data.subset index).c, labelOfNat (Data.subset index).d,
    labelOfNat (Data.subset index).e]

def relationIndex (R : Relation) : Fin 6 → Nat :=
  ![R.indices.a, R.indices.b, R.indices.c, R.indices.d, R.indices.e, R.indices.f]

def pluckerRows (common : Fin 3 → Label) (outside : Fin 4 → Label) :
    Fin 6 → Fin 5 → Label :=
  ![![common 0, common 1, common 2, outside 0, outside 1],
    ![common 0, common 1, common 2, outside 2, outside 3],
    ![common 0, common 1, common 2, outside 0, outside 2],
    ![common 0, common 1, common 2, outside 1, outside 3],
    ![common 0, common 1, common 2, outside 0, outside 3],
    ![common 0, common 1, common 2, outside 1, outside 2]]

def unitFactor (negate : Bool) : ℤˣ := if negate then -1 else 1

structure RelationTupleWitness (R : Relation) where
  «prefix» : Fin 3 → Label
  outside : Fin 4 → Label
  permutation : Fin 6 → Equiv.Perm (Fin 5)
  rows_correct : ∀ j, pluckerRows «prefix» outside j =
    minorRows (relationIndex R j) ∘ permutation j
  parity_first : Equiv.Perm.sign (permutation 0) * Equiv.Perm.sign (permutation 1) =
    unitFactor R.negations.a
  parity_second : -(Equiv.Perm.sign (permutation 2) * Equiv.Perm.sign (permutation 3)) =
    unitFactor R.negations.b
  parity_third : Equiv.Perm.sign (permutation 4) * Equiv.Perm.sign (permutation 5) =
    unitFactor R.negations.c

structure SupportWitness (B : Boundary 9) (edge : SupportEdge) where
  facet : Finset Label
  four : Fin 4 → Label
  left : Label
  right : Label
  leftPerm : Equiv.Perm (Fin 5)
  rightPerm : Equiv.Perm (Fin 5)
  facet_mem : facet ∈ B.facets
  four_mem : ∀ j, four j ∈ facet
  left_outside : left ∉ facet
  right_outside : right ∉ facet
  left_rows : ![four 0, four 1, four 2, four 3, left] =
    minorRows edge.source ∘ leftPerm
  right_rows : ![four 0, four 1, four 2, four 3, right] =
    minorRows edge.target ∘ rightPerm
  parity : Equiv.Perm.sign rightPerm = unitFactor edge.negate * Equiv.Perm.sign leftPerm

structure SupportDatum where
  facet : Finset Label
  four : Fin 4 → Label
  left : Label
  right : Label
  leftPerm : Equiv.Perm (Fin 5)
  rightPerm : Equiv.Perm (Fin 5)

def SupportDatum.Valid (D : SupportDatum) (B : Boundary 9) (edge : SupportEdge) : Prop :=
  D.facet ∈ B.facets ∧ (∀ j, D.four j ∈ D.facet) ∧
  D.left ∉ D.facet ∧ D.right ∉ D.facet ∧
  ![D.four 0, D.four 1, D.four 2, D.four 3, D.left] =
    minorRows edge.source ∘ D.leftPerm ∧
  ![D.four 0, D.four 1, D.four 2, D.four 3, D.right] =
    minorRows edge.target ∘ D.rightPerm ∧
  Equiv.Perm.sign D.rightPerm = unitFactor edge.negate * Equiv.Perm.sign D.leftPerm

noncomputable instance (D : SupportDatum) (B : Boundary 9) (edge : SupportEdge) :
    Decidable (D.Valid B edge) := by unfold SupportDatum.Valid; infer_instance

def SupportDatum.toWitness (D : SupportDatum) (B : Boundary 9) (edge : SupportEdge)
    (h : D.Valid B edge) : SupportWitness B edge :=
  ⟨D.facet, D.four, D.left, D.right, D.leftPerm, D.rightPerm,
    h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

inductive ZeroWitness (B : Boundary 9) (index : Nat)
  | facet (F : Finset Label) (hF : F ∈ B.facets)
      (hrows : ∀ j, minorRows index j ∈ F)
  | polygon (R : Finset Label) (hR : R ∈ B.polygons) (v : Label)
      (hrows : ∀ j, minorRows index j ∈ insert v R)

structure ZeroDatum where
  polygon : Bool
  face : Finset Label
  point : Label

def ZeroDatum.Valid (D : ZeroDatum) (B : Boundary 9) (index : Nat) : Prop :=
  if D.polygon then
    D.face ∈ B.polygons ∧ ∀ j, minorRows index j ∈ insert D.point D.face
  else D.face ∈ B.facets ∧ ∀ j, minorRows index j ∈ D.face

noncomputable instance (D : ZeroDatum) (B : Boundary 9) (index : Nat) :
    Decidable (D.Valid B index) := by unfold ZeroDatum.Valid; infer_instance

def ZeroDatum.toWitness (D : ZeroDatum) (B : Boundary 9) (index : Nat)
    (h : D.Valid B index) : ZeroWitness B index := by
  cases hp : D.polygon
  · have hh : D.face ∈ B.facets ∧ ∀ j, minorRows index j ∈ D.face := by
      simpa [ZeroDatum.Valid, hp] using h
    exact .facet D.face hh.1 hh.2
  · have hh : D.face ∈ B.polygons ∧ ∀ j, minorRows index j ∈ insert D.point D.face := by
      simpa [ZeroDatum.Valid, hp] using h
    exact .polygon D.face hh.1 D.point hh.2

structure AnchorWitness (B : Boundary 9) (index : Nat) where
  triangle : Finset Label
  facet : Finset Label
  inner : Label
  outside : Label
  triangle_mem : triangle ∈ B.polygons
  triangle_card : triangle.card = 3
  facet_mem : facet ∈ B.facets
  inner_outside : inner ∉ triangle
  outside_facet : outside ∉ facet
  inside_facet : insert inner triangle ⊆ facet
  rows_correct : Finset.univ.image (minorRows index) = insert outside (insert inner triangle)

structure BoundaryWitness (B : Boundary 9) (anchor : Nat)
    (edge : Nat → SupportEdge) (edgeCount : Nat) (zero : Nat → Nat) (zeroCount : Nat) where
  anchor_witness : AnchorWitness B anchor
  support_witness : ∀ i : Fin edgeCount, SupportWitness B (edge i.val)
  zero_witness : ∀ i : Fin zeroCount, ZeroWitness B (zero i.val)

end Papers.RationalityTen.GPFiniteGeometry

end
end BundlePart7

section BundlePart8
/- Source: Papers/GrassmannPluckerFive.lean -/










/-!
# The three-term relation for ordinary five-row determinants

No independence of the common three rows, or of the four additional labels,
is assumed. A nonsingular chart is used only in the first lemma. The global
theorem either obtains such a chart from one of the three relevant minors,
or reduces immediately to zero. 
-/

@[expose] public section
noncomputable section
namespace Papers.GrassmannPluckerFive

open Matrix
open scoped BigOperators

abbrev Row := Fin 5 → ℝ

def rowMatrix {ι : Type*} (p : ι → Row) (rows : Fin 5 → ι) :
    Matrix (Fin 5) (Fin 5) ℝ := fun i j => p (rows i) j

def minor {ι : Type*} (p : ι → Row) (rows : Fin 5 → ι) : ℝ :=
  (rowMatrix p rows).det

def bracket {ι : Type*} (p : ι → Row) (S : Fin 3 → ι) (a b : ι) : ℝ :=
  minor p ![S 0, S 1, S 2, a, b]

theorem bracket_swap {ι : Type*} (p : ι → Row) (S : Fin 3 → ι) (a b : ι) :
    bracket p S b a = -bracket p S a b := by
  have heq : rowMatrix p ![S 0, S 1, S 2, b, a] =
      (rowMatrix p ![S 0, S 1, S 2, a, b]).submatrix
        (Equiv.swap (3 : Fin 5) 4) id := by
    ext i j
    fin_cases i <;> simp [rowMatrix, Matrix.submatrix_apply, Equiv.swap_apply_def]
  unfold bracket minor
  rw [heq, Matrix.det_permute]
  simp [Equiv.Perm.sign_swap (show (3 : Fin 5) ≠ 4 by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem three_term_of_first_ne_zero {ι : Type*}
    (p : ι → Row) (S : Fin 3 → ι) (a b c d : ι)
    (hab : bracket p S a b ≠ 0) :
    bracket p S a b * bracket p S c d -
      bracket p S a c * bracket p S b d +
      bracket p S a d * bracket p S b c = 0 := by
  let rows : Fin 5 → ι := ![S 0, S 1, S 2, a, b]
  let B : Matrix (Fin 5) (Fin 5) ℝ := rowMatrix p rows
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr hab
  let q : ι → Row := fun i => p i ᵥ* B⁻¹
  have hbase : rowMatrix q rows = (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    change B * B⁻¹ = 1
    exact B.mul_nonsing_inv hB
  have hS0 : q (S 0) = ![1, 0, 0, 0, 0] := by
    funext j
    have h := congrFun (congrFun hbase 0) j
    fin_cases j <;> simpa [rowMatrix, rows, Matrix.one_apply] using h
  have hS1 : q (S 1) = ![0, 1, 0, 0, 0] := by
    funext j
    have h := congrFun (congrFun hbase 1) j
    fin_cases j <;> simpa [rowMatrix, rows, Matrix.one_apply] using h
  have hS2 : q (S 2) = ![0, 0, 1, 0, 0] := by
    funext j
    have h := congrFun (congrFun hbase 2) j
    fin_cases j <;> simpa [rowMatrix, rows, Matrix.one_apply] using h
  have ha : q a = ![0, 0, 0, 1, 0] := by
    funext j
    have h := congrFun (congrFun hbase 3) j
    fin_cases j <;> simpa [rowMatrix, rows, Matrix.one_apply] using h
  have hb : q b = ![0, 0, 0, 0, 1] := by
    funext j
    have h := congrFun (congrFun hbase 4) j
    fin_cases j <;> simpa [rowMatrix, rows, Matrix.one_apply] using h
  have hchange (r : Fin 5 → ι) : minor q r = minor p r * B⁻¹.det := by
    change (rowMatrix p r * B⁻¹).det = _
    exact Matrix.det_mul _ _
  have hbracket (v w : ι) : bracket q S v w = bracket p S v w * B⁻¹.det :=
    hchange ![S 0, S 1, S 2, v, w]
  have hscale : B⁻¹.det ≠ 0 := (B.isUnit_nonsing_inv_det hB).ne_zero
  have hab' : bracket q S a b = 1 := by
    change (rowMatrix q rows).det = 1
    rw [hbase, Matrix.det_one]
  have hac : bracket q S a c = q c 4 := by
    norm_num [bracket, minor, rowMatrix, hS0, hS1, hS2, ha,
      Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
      Fin.sum_univ_succ]
  have had : bracket q S a d = q d 4 := by
    norm_num [bracket, minor, rowMatrix, hS0, hS1, hS2, ha,
      Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
      Fin.sum_univ_succ]
  have hbc : bracket q S b c = -q c 3 := by
    norm_num [bracket, minor, rowMatrix, hS0, hS1, hS2, hb,
      Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
      Fin.sum_univ_succ]
  have hbd : bracket q S b d = -q d 3 := by
    norm_num [bracket, minor, rowMatrix, hS0, hS1, hS2, hb,
      Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
      Fin.sum_univ_succ]
  have hcd : bracket q S c d = q c 3 * q d 4 - q c 4 * q d 3 := by
    norm_num [bracket, minor, rowMatrix, hS0, hS1, hS2,
      Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
      Fin.sum_univ_succ] <;> ring
  have hrelation : bracket q S a b * bracket q S c d -
      bracket q S a c * bracket q S b d +
      bracket q S a d * bracket q S b c = 0 := by
    rw [hab', hac, had, hbc, hbd, hcd]
    ring
  simp only [hbracket] at hrelation
  have hscaled : (bracket p S a b * bracket p S c d -
      bracket p S a c * bracket p S b d +
      bracket p S a d * bracket p S b c) * (B⁻¹.det) ^ 2 = 0 := by
    nlinarith only [hrelation]
  exact (mul_eq_zero.mp hscaled).resolve_right (pow_ne_zero 2 hscale)

/-- The ordinary three-term Grassmann--Pluecker identity for arbitrary
five-dimensional real rows, including every degenerate case. -/
theorem three_term {ι : Type*}
    (p : ι → Row) (S : Fin 3 → ι) (a b c d : ι) :
    bracket p S a b * bracket p S c d -
      bracket p S a c * bracket p S b d +
      bracket p S a d * bracket p S b c = 0 := by
  by_cases hab : bracket p S a b = 0
  · by_cases hac : bracket p S a c = 0
    · by_cases had : bracket p S a d = 0
      · simp [hab, hac, had]
      · have h := three_term_of_first_ne_zero p S a d b c had
        rw [bracket_swap p S c d, bracket_swap p S b d] at h
        nlinarith only [h]
    · have h := three_term_of_first_ne_zero p S a c b d hac
      rw [bracket_swap p S b c] at h
      nlinarith only [h]
  · exact three_term_of_first_ne_zero p S a b c d hab

end Papers.GrassmannPluckerFive

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/GPRelationGeometry.lean -/







@[expose] public section

/-!
# The finite GP relations are actual determinant identities

The tuple witness checks all six permutations and all three coefficient
signs. The resulting identity is the general three-term identity for
ordinary determinants, including degenerate common rows. Thus no abstract
oriented-matroid axiom is used as a hypothesis in the actual application.


-/

noncomputable section
namespace Papers.RationalityTen.GPFiniteGeometry

open Matrix
open Papers.RationalityTen.PureGP
open Papers.RationalityTen.SupportDeterminantStandalone

theorem realWithNegation_eq_unitFactor (b : Bool) (x : ℝ) :
    realWithNegation b x = (unitFactor b : ℝ) * x := by
  cases b <;> simp [realWithNegation, unitFactor]

theorem RelationTupleWitness.real_identity {R : Relation} (W : RelationTupleWitness R)
    (p : Label → Fin 5 → ℝ) :
    R.RealIdentity (fun i => minor p (minorRows i)) := by
  have hminor (j : Fin 6) : minor p (pluckerRows W.prefix W.outside j) =
      (Equiv.Perm.sign (W.permutation j) : ℝ) * minor p (minorRows (relationIndex R j)) := by
    rw [W.rows_correct j, minor_permute]
  have hfirst : (Equiv.Perm.sign (W.permutation 0) : ℝ) *
      (Equiv.Perm.sign (W.permutation 1) : ℝ) = (unitFactor R.negations.a : ℝ) := by
    simpa using congrArg (fun u : ℤˣ => (u : ℝ)) W.parity_first
  have hsecond : -((Equiv.Perm.sign (W.permutation 2) : ℝ) *
      (Equiv.Perm.sign (W.permutation 3) : ℝ)) = (unitFactor R.negations.b : ℝ) := by
    simpa using congrArg (fun u : ℤˣ => (u : ℝ)) W.parity_second
  have hthird : (Equiv.Perm.sign (W.permutation 4) : ℝ) *
      (Equiv.Perm.sign (W.permutation 5) : ℝ) = (unitFactor R.negations.c : ℝ) := by
    simpa using congrArg (fun u : ℤˣ => (u : ℝ)) W.parity_third
  have h := Papers.GrassmannPluckerFive.three_term p W.prefix
    (W.outside 0) (W.outside 1) (W.outside 2) (W.outside 3)
  change minor p (pluckerRows W.prefix W.outside 0) *
      minor p (pluckerRows W.prefix W.outside 1) -
    minor p (pluckerRows W.prefix W.outside 2) *
      minor p (pluckerRows W.prefix W.outside 3) +
    minor p (pluckerRows W.prefix W.outside 4) *
      minor p (pluckerRows W.prefix W.outside 5) = 0 at h
  simp only [hminor] at h
  unfold Relation.RealIdentity
  simp only [realWithNegation_eq_unitFactor]
  calc
    _ = ((Equiv.Perm.sign (W.permutation 0) : ℝ) *
          minor p (minorRows R.indices.a)) *
        ((Equiv.Perm.sign (W.permutation 1) : ℝ) *
          minor p (minorRows R.indices.b)) -
      ((Equiv.Perm.sign (W.permutation 2) : ℝ) *
          minor p (minorRows R.indices.c)) *
        ((Equiv.Perm.sign (W.permutation 3) : ℝ) *
          minor p (minorRows R.indices.d)) +
      ((Equiv.Perm.sign (W.permutation 4) : ℝ) *
          minor p (minorRows R.indices.e)) *
        ((Equiv.Perm.sign (W.permutation 5) : ℝ) *
          minor p (minorRows R.indices.f)) := by
      rw [← hfirst, ← hsecond, ← hthird]
      ring
    _ = 0 := h

theorem RelationTupleWitness.allowed_scaled {R : Relation} (W : RelationTupleWitness R)
    (p : Label → Fin 5 → ℝ) (scale : ℝ) :
    R.allowed (fun i => realSign (scale * minor p (minorRows i))) = true :=
  R.allowed_realSigns _ ((W.real_identity p).scale scale)

theorem all_used_relations_valid
    (W : ∀ i : Fin 252, RelationTupleWitness (Data.relation i.val))
    (p : Label → Fin 5 → ℝ) (scale : ℝ) :
    Data.ValidUsedRelations (fun i => realSign (scale * minor p (minorRows i))) := by
  intro i hi
  exact (W ⟨i, hi⟩).allowed_scaled p scale

end Papers.RationalityTen.GPFiniteGeometry

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/GPActualBoundaryExclusion.lean -/




@[expose] public section

/-!
# From a finite GP certificate to actual nonrealizability

All sign hypotheses consumed by the finite replay are conclusions about
actual real determinants. The finite tuple witnesses identify the GP
relations, and the support witnesses identify actual supporting faces.
The eventual literal case wrappers instantiate both finite inputs.


-/

noncomputable section
namespace Papers.RationalityTen.GPFiniteGeometry

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open Papers.RationalityTen.ChirotopeDensity
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Papers.RationalityTen.PureGP
open Papers.RationalityTen.SupportDeterminantStandalone
open Papers.RationalityTen.GPActualSupportSigns

variable {P : ConvexPolytope 4} {lab : Fin 10 ≃ VertexType P} {B : Boundary 9}

theorem SupportWitness.actual_holds {edge : SupportEdge} (W : SupportWitness B edge)
    (hB : RealizesBoundary P lab B) (scale : ℝ) :
    edge.Holds (fun i => realSign (scale * SupportDeterminantStandalone.minor (vertexCoordinates P lab) (minorRows i))) := by
  exact actual_support_edge hB W.facet W.facet_mem W.four W.left W.right
    (minorRows edge.source) (minorRows edge.target) W.leftPerm W.rightPerm edge.negate
    W.left_rows W.right_rows W.parity W.four_mem W.left_outside W.right_outside scale

theorem ZeroWitness.actual_zero {index : Nat} (W : ZeroWitness B index)
    (hP : P.IsFullDim) (hB : RealizesBoundary P lab B) (scale : ℝ) :
    realSign (scale * SupportDeterminantStandalone.minor (vertexCoordinates P lab) (minorRows index)) = .zero := by
  have hz : SupportDeterminantStandalone.minor (vertexCoordinates P lab) (minorRows index) = 0 := by
    cases W with
    | facet F hF hrows => exact actual_facet_zero hP hB F hF _ hrows
    | polygon R hR v hrows => exact actual_polygon_plus_point_zero hB R hR v _ hrows
  rw [hz, mul_zero, realSign_zero]

theorem AnchorWitness.actual_nonzero {anchor : Nat} (W : AnchorWitness B anchor)
    (hB : RealizesBoundary P lab B) : SupportDeterminantStandalone.minor (vertexCoordinates P lab) (minorRows anchor) ≠ 0 :=
  actual_flag_anchor_nonzero hB W.triangle W.facet W.triangle_mem W.facet_mem
    W.inner W.outside W.inner_outside W.outside_facet W.inside_facet _ W.rows_correct

/-- A complete actual-boundary exclusion. The two certificate arguments
are filled by ordinary finite proof objects in each literal case wrapper;
there are no real-coordinate, sign, rank or genericity hypotheses. -/
theorem BoundaryWitness.no_actual_realization
    (hP : P.IsFullDim) (hB : RealizesBoundary P lab B)
    {anchor edgeCount zeroCount : Nat} {edge : Nat → SupportEdge} {zero : Nat → Nat}
    (W : BoundaryWitness B anchor edge edgeCount zero zeroCount)
    (relations : ∀ i : Fin 252, RelationTupleWitness (Data.relation i.val))
    (contradiction : ∀ assignment : Nat → Sign,
      assignment anchor = .positive →
      (∀ i, i < edgeCount → (edge i).Holds assignment) →
      (∀ i, i < zeroCount → assignment (zero i) = .zero) →
      Data.ValidUsedRelations assignment → False) : False := by
  let p := vertexCoordinates P lab
  let scale := (SupportDeterminantStandalone.minor p (minorRows anchor))⁻¹
  let assignment : Nat → Sign := fun i => realSign (scale * SupportDeterminantStandalone.minor p (minorRows i))
  apply contradiction assignment
  · exact normalizedAssignment_anchor p minorRows anchor (W.anchor_witness.actual_nonzero hB)
  · intro i hi
    exact (W.support_witness ⟨i, hi⟩).actual_holds hB scale
  · intro i hi
    exact (W.zero_witness ⟨i, hi⟩).actual_zero hP hB scale
  · exact all_used_relations_valid relations p scale

end Papers.RationalityTen.GPFiniteGeometry

end
end
end BundlePart10
