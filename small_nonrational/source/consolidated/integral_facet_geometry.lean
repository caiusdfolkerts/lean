module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Powerset
public import Papers.RationalityTenFacetExtension
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum
public import Papers.IntegerFacetRawData
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Papers.RationalityTenFacetIntersection
public import Papers.ActualCoordinateRealizations

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/IntegerFacetCertificateData.lean -/




@[expose] public section

/-! Finite integer data checked by ordinary kernel reduction.
The real geometric soundness proof is in IntegerFacetCertificates. -/

open Matrix
open scoped BigOperators

namespace Papers.RationalWitnesses

abbrev IntegerConfiguration (n : ℕ) := Matrix (Fin n) (Fin 5) ℤ

structure FacetData (n : ℕ) where
  vertices : Finset (Fin n)
  normal : Fin 5 → ℤ
  rows : Fin 4 → Fin n
  columns : Fin 4 → Fin 5

def FacetData.Valid {n : ℕ} (w : IntegerConfiguration n) (F : FacetData n) : Prop :=
  F.normal ≠ 0 ∧
  (∀ i ∈ F.vertices, F.normal ⬝ᵥ w i = 0) ∧
  (∀ i ∉ F.vertices, 0 < F.normal ⬝ᵥ w i) ∧
  (∀ k, F.rows k ∈ F.vertices) ∧
  (w.submatrix F.rows F.columns).det ≠ 0

/-- A rational expression of every listed point in the span of three rows.
Each denominator is recorded as a nonzero integer, so the check uses no
division and does not assume that the three rows are independent. -/
structure LowRankData (n : ℕ) where
  vertices : Finset (Fin n)
  rows : Fin 3 → Fin n
  denominator : Fin n → ℤ
  coefficients : Matrix (Fin n) (Fin 3) ℤ

def LowRankData.Valid {n : ℕ} (w : IntegerConfiguration n)
    (L : LowRankData n) : Prop :=
  ∀ i ∈ L.vertices, L.denominator i ≠ 0 ∧
    ∀ j, L.denominator i * w i j =
      ∑ k, L.coefficients i k * w (L.rows k) j

def RelationValid {n : ℕ} (w : IntegerConfiguration n) (c : Fin n → ℤ) : Prop :=
  ∀ j, ∑ i, c i * w i j = 0

def RelationExcludes {n : ℕ} (c : Fin n → ℤ) (S : Finset (Fin n)) : Prop :=
  (∀ i ∉ S, 0 ≤ c i) ∧ ∃ i, i ∉ S ∧ 0 < c i

structure FacetCertificate (n f l c : ℕ) where
  spanningRows : Fin 5 → Fin n
  facets : Fin f → FacetData n
  lowRanks : Fin l → LowRankData n
  relations : Fin c → Fin n → ℤ

def FacetCertificate.Valid {n f l c : ℕ} (w : IntegerConfiguration n)
    (C : FacetCertificate n f l c) : Prop :=
  (w.submatrix C.spanningRows id).det ≠ 0 ∧
  (∀ k, (C.facets k).Valid w) ∧
  (∀ k, (C.lowRanks k).Valid w) ∧
  (∀ k, RelationValid w (C.relations k)) ∧
  ∀ S : Finset (Fin n),
    (∃ k, S = (C.facets k).vertices) ∨
    S.card ≤ 3 ∨ S = Finset.univ ∨
    (∃ k, S ⊆ (C.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (C.relations k) S

end Papers.RationalWitnesses

end
end BundlePart0

section BundlePart1
/- Source: Papers/IntegerFacetCertificates.lean -/








@[expose] public section

/-!
# Exact finite certificates for rational four-polytopes

The certificate data are integer matrices.  All finite arithmetic obligations
are decidable propositions; the geometric conclusion concerns the ordinary
real linear span and strict supporting hyperplanes from the polytope library.

Completeness does not assume an oriented-matroid realization theorem.  For
every unlisted subset, the certificate supplies either a span of dimension at
most three, or an explicit linear dependence whose coefficients outside the
subset are nonnegative and not all zero.  The latter contradicts a strictly
positive supporting normal by taking a scalar product with the dependence.
-/

open Matrix Module
open scoped BigOperators

namespace Papers.RationalWitnesses

open Papers.RationalityTen.ChirotopeDensity

def realConfiguration {n : ℕ} (w : IntegerConfiguration n) :
    Matrix (Fin n) (Fin 5) ℝ := fun i j => w i j

theorem cast_dotProduct (a b : Fin 5 → ℤ) :
    (fun j => (a j : ℝ)) ⬝ᵥ (fun j => (b j : ℝ)) = (a ⬝ᵥ b : ℤ) := by
  simp [dotProduct]

theorem cast_submatrix_det_ne_zero {n k : ℕ} (w : IntegerConfiguration n)
    (rows : Fin k → Fin n) (columns : Fin k → Fin 5)
    (h : (w.submatrix rows columns).det ≠ 0) :
    ((realConfiguration w).submatrix rows columns).det ≠ 0 := by
  have hcast : (((w.submatrix rows columns).det : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast h
  rw [Int.cast_det] at hcast
  exact hcast

theorem spans_of_spanning_minor {n : ℕ} (w : IntegerConfiguration n)
    (rows : Fin 5 → Fin n)
    (h : (w.submatrix rows id).det ≠ 0) :
    Spans (realConfiguration w) := by
  have hlower := Matrix.rank_submatrix_le (realConfiguration w) rows id
  have hminor := Matrix.rank_of_det_ne_zero
    (cast_submatrix_det_ne_zero w rows id h)
  have hupper := Matrix.rank_le_card_width (realConfiguration w)
  have hrank : (realConfiguration w).rank = 5 := by
    simp only [Fintype.card_fin] at hminor hupper
    omega
  exact (spans_iff_matrix_rank (realConfiguration w)).mpr hrank

theorem FacetData.facet {n : ℕ} {w : IntegerConfiguration n}
    (F : FacetData n) (hF : F.Valid w) :
    FacetMask (realConfiguration w) F.vertices := by
  classical
  obtain ⟨hn, hz, hp, hrows, hdet⟩ := hF
  let a : Fin 5 → ℝ := fun j => F.normal j
  have ha : a ≠ 0 := by
    intro h
    apply hn
    funext j
    have hj : (F.normal j : ℝ) = 0 := congrFun h j
    exact_mod_cast hj
  have hs : StrictSupport (realConfiguration w) F.vertices a := by
    constructor
    · intro i hi
      change (fun j => (F.normal j : ℝ)) ⬝ᵥ (fun j => (w i j : ℝ)) = 0
      rw [cast_dotProduct]
      exact_mod_cast hz i hi
    · intro i hi
      change 0 < (fun j => (F.normal j : ℝ)) ⬝ᵥ (fun j => (w i j : ℝ))
      rw [cast_dotProduct]
      exact_mod_cast hp i hi
  have hm : (maskRows (realConfiguration w) F.vertices).submatrix F.rows F.columns =
      (realConfiguration w).submatrix F.rows F.columns := by
    ext i j
    simp [maskRows, Matrix.submatrix_apply, hrows]
  have hlower := Matrix.rank_submatrix_le
    (maskRows (realConfiguration w) F.vertices) F.rows F.columns
  rw [hm] at hlower
  have hmRank : (maskRows (realConfiguration w) F.vertices).rank =
      subsetRank (realConfiguration w) F.vertices := maskRows_rank _ _
  rw [hmRank] at hlower
  have hminor := Matrix.rank_of_det_ne_zero
    (cast_submatrix_det_ne_zero w F.rows F.columns hdet)
  simp only [Fintype.card_fin] at hminor
  have hupper := subsetRank_add_one_le_of_annihilator
    (realConfiguration w) F.vertices a ha hs.1
  refine ⟨⟨F.rows 0, hrows 0⟩, ⟨a, hs⟩, ?_⟩
  omega

theorem subsetRank_mono' {n r : ℕ} (p : Fin n → Fin r → ℝ)
    {S T : Finset (Fin n)} (hST : S ⊆ T) : subsetRank p S ≤ subsetRank p T := by
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  exact Set.image_mono (Finset.coe_subset.mpr hST)

theorem subsetRank_le_card' {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : subsetRank p S ≤ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [subsetRank]
  | @insert i S hi ih =>
      have h := subsetRank_insert_le p S i
      rw [Finset.card_insert_of_notMem hi]
      omega

theorem LowRankData.rank_le_three {n : ℕ} {w : IntegerConfiguration n}
    (L : LowRankData n) (hL : L.Valid w) :
    subsetRank (realConfiguration w) L.vertices ≤ 3 := by
  let V := Submodule.span ℝ (Set.range (fun k => realConfiguration w (L.rows k)))
  have hle : Submodule.span ℝ (realConfiguration w '' (↑L.vertices : Set (Fin n))) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨hden, heq⟩ := hL i hi
    have hden' : (L.denominator i : ℝ) ≠ 0 := by exact_mod_cast hden
    apply (V.smul_mem_iff hden').mp
    have heq' : (L.denominator i : ℝ) • realConfiguration w i =
        ∑ k, (L.coefficients i k : ℝ) • realConfiguration w (L.rows k) := by
      ext j
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, realConfiguration]
      exact_mod_cast heq j
    rw [heq']
    apply Submodule.sum_mem
    intro k _
    exact V.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  have hbound : finrank ℝ V ≤ 3 := by
    exact (finrank_range_le_card (R := ℝ)
      (fun k : Fin 3 => realConfiguration w (L.rows k))).trans_eq (Fintype.card_fin 3)
  exact (Submodule.finrank_mono hle).trans hbound

theorem relation_excludes_support {n : ℕ} {w : IntegerConfiguration n}
    {c : Fin n → ℤ} (hc : RelationValid w c)
    {S : Finset (Fin n)} (hS : RelationExcludes c S) :
    ¬ ∃ a, StrictSupport (realConfiguration w) S a := by
  classical
  rintro ⟨a, ha⟩
  have hrel : ∑ i, (c i : ℝ) • realConfiguration w i = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realConfiguration,
      Pi.zero_apply]
    exact_mod_cast hc j
  have hsum : ∑ i, (c i : ℝ) * (a ⬝ᵥ realConfiguration w i) = 0 := by
    have h := congrArg (dotLinear a) hrel
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
    exact h
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (c i : ℝ) * (a ⬝ᵥ realConfiguration w i) := by
    intro i _
    by_cases hi : i ∈ S
    · rw [ha.1 i hi, mul_zero]
    · apply mul_nonneg
      · exact_mod_cast hS.1 i hi
      · exact (ha.2 i hi).le
  obtain ⟨i, hi, hpos⟩ := hS.2
  have hpos' : 0 < (c i : ℝ) := by exact_mod_cast hpos
  have hstrict : 0 < ∑ i, (c i : ℝ) * (a ⬝ᵥ realConfiguration w i) :=
    Finset.sum_pos' hnonneg ⟨i, Finset.mem_univ i, mul_pos hpos' (ha.2 i hi)⟩
  rw [hsum] at hstrict
  exact lt_irrefl 0 hstrict

/-- The complete list of facets, with real linear-algebraic and supporting
hyperplane semantics.  Every possible vertex subset is covered. -/
theorem FacetCertificate.facets_iff {n f l c : ℕ} {w : IntegerConfiguration n}
    (C : FacetCertificate n f l c) (hC : C.Valid w) (S : Finset (Fin n)) :
    FacetMask (realConfiguration w) S ↔ ∃ k, S = (C.facets k).vertices := by
  obtain ⟨hspan, hfacets, hlow, hrelations, hcover⟩ := hC
  constructor
  · intro hS
    rcases hcover S with h | hsmall | huniv | hlow' | hrelation
    · exact h
    · have hr := subsetRank_le_card' (realConfiguration w) S
      have hr' := hS.2.2
      omega
    · exact False.elim ((hS.ne_univ (spans_of_spanning_minor w C.spanningRows hspan)) huniv)
    · obtain ⟨k, hk⟩ := hlow'
      have hr := (subsetRank_mono' (realConfiguration w) hk).trans
        ((C.lowRanks k).rank_le_three (hlow k))
      have hr' := hS.2.2
      omega
    · obtain ⟨k, hk⟩ := hrelation
      exact False.elim (relation_excludes_support (hrelations k) hk hS.2.1)
  · rintro ⟨k, rfl⟩
    exact (C.facets k).facet (hfacets k)

end Papers.RationalWitnesses

end
end BundlePart1

section BundlePart2
/- Source: Papers/IntegerFacetRawBridge.lean -/






@[expose] public section

/-! Exact translation of the Init-only finite certificates into the same
Mathlib facet certificates used by the real geometric soundness theorem.
No Boolean check is accepted without this mathematical bridge. -/

open Matrix
open scoped BigOperators

namespace Papers.RationalWitnesses.Raw

def maskFinset {n : ℕ} (S : VertexMask n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => S i = true)

@[simp] theorem mem_maskFinset {n : ℕ} (S : VertexMask n) (i : Fin n) :
    i ∈ maskFinset S ↔ S i = true := by simp [maskFinset]

@[simp] theorem sumFin_eq_sum {n : ℕ} (f : Fin n → ℤ) : sumFin f = ∑ i, f i := by
  simp [sumFin, List.sum_ofFn]

@[simp] theorem card_eq_card_maskFinset {n : ℕ} (S : VertexMask n) :
    card S = (maskFinset S).card := by
  simp [card, maskFinset, List.sum_ofFn, Finset.sum_boole]

theorem minorValid_det_ne_zero {n k : ℕ} {w : Configuration n}
    {rows : Fin k → Fin n} {columns : Fin k → Fin 5}
    {d : ℤ} {B : Fin k → Fin k → ℤ}
    (h : MinorValid w rows columns d B) :
    (Matrix.submatrix w rows columns).det ≠ 0 := by
  have hmul : Matrix.submatrix w rows columns * Matrix.of B =
      d • (1 : Matrix (Fin k) (Fin k) ℤ) := by
    ext i j
    change (∑ t : Fin k, w (rows i) (columns t) * B t j) =
      d * (if i = j then 1 else 0)
    have hh : (∑ t : Fin k, w (rows i) (columns t) * B t j) =
        if i = j then d else 0 := by
      simpa only [sumFin_eq_sum] using h.2 i j
    by_cases hij : i = j
    · simp only [if_pos hij, mul_one] at hh ⊢
      exact hh
    · simp only [if_neg hij, mul_zero] at hh ⊢
      exact hh
  intro hz
  have hd := congrArg Matrix.det hmul
  simp only [Matrix.det_mul, hz, zero_mul, Matrix.det_smul, Matrix.det_one,
    Fintype.card_fin, mul_one] at hd
  exact (pow_ne_zero k h.1) hd.symm

def FacetData.toFacetData {n : ℕ} (F : FacetData n) :
    Papers.RationalWitnesses.FacetData n where
  vertices := maskFinset F.vertices
  normal := F.normal
  rows := F.rows
  columns := F.columns

theorem FacetData.valid_toFacetData {n : ℕ} {w : Configuration n}
    (F : FacetData n) (hF : F.Valid w) : F.toFacetData.Valid w := by
  obtain ⟨hn, hz, hp, hr, hm⟩ := hF
  refine ⟨?_, ?_, ?_, ?_, minorValid_det_ne_zero hm⟩
  · rintro hzero
    obtain ⟨j, hj⟩ := hn
    exact hj (congrFun hzero j)
  · intro i hi
    simpa [toFacetData, dotProduct, sumFin_eq_sum] using hz i ((mem_maskFinset _ _).mp hi)
  · intro i hi
    have hn' : F.vertices i ≠ true := by simpa [toFacetData] using hi
    simpa [toFacetData, dotProduct, sumFin_eq_sum] using hp i hn'
  · intro k
    exact (mem_maskFinset _ _).mpr (hr k)

def LowRankData.toLowRankData {n : ℕ} (L : LowRankData n) :
    Papers.RationalWitnesses.LowRankData n where
  vertices := maskFinset L.vertices
  rows := L.rows
  denominator := L.denominator
  coefficients := L.coefficients

theorem LowRankData.valid_toLowRankData {n : ℕ} {w : Configuration n}
    (L : LowRankData n) (hL : L.Valid w) : L.toLowRankData.Valid w := by
  intro i hi
  obtain ⟨hd, heq⟩ := hL i ((mem_maskFinset _ _).mp hi)
  refine ⟨hd, ?_⟩
  intro j
  simpa [toLowRankData, sumFin_eq_sum] using heq j

def FacetCertificate.toFacetCertificate {n f l c : ℕ}
    (C : FacetCertificate n f l c) : Papers.RationalWitnesses.FacetCertificate n f l c where
  spanningRows := C.spanningRows
  facets k := (C.facets k).toFacetData
  lowRanks k := (C.lowRanks k).toLowRankData
  relations := C.relations

theorem FacetCertificate.valid_toFacetCertificate {n f l c : ℕ}
    {w : Configuration n} (C : FacetCertificate n f l c) (hC : C.Valid w) :
    C.toFacetCertificate.Valid w := by
  obtain ⟨hs, hf, hl, hr, hc⟩ := hC
  refine ⟨minorValid_det_ne_zero hs,
    (fun k => (C.facets k).valid_toFacetData (hf k)),
    (fun k => (C.lowRanks k).valid_toLowRankData (hl k)), ?_, ?_⟩
  · intro k j
    simpa [Papers.RationalWitnesses.RelationValid, RelationValid,
      toFacetCertificate, sumFin_eq_sum] using hr k j
  · intro T
    let S : VertexMask n := fun i => decide (i ∈ T)
    have hS : maskFinset S = T := by ext i; simp [S]
    rcases hc S with h | h | h | h | h
    · obtain ⟨k, hk⟩ := h
      left
      refine ⟨k, ?_⟩
      rw [← hS]
      change maskFinset S = maskFinset (C.facets k).vertices
      exact congrArg maskFinset (funext hk)
    · right; left
      simpa only [card_eq_card_maskFinset, hS] using h
    · right; right; left
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      simpa [S] using h i
    · obtain ⟨k, hk⟩ := h
      right; right; right; left
      refine ⟨k, ?_⟩
      intro i hi
      apply (mem_maskFinset _ _).mpr
      exact hk i (by simpa [S] using hi)
    · obtain ⟨k, hn, hp⟩ := h
      right; right; right; right
      refine ⟨k, ?_, ?_⟩
      · intro i hi
        exact hn i (by simpa [S] using hi)
      · obtain ⟨i, hi, hp⟩ := hp
        exact ⟨i, by simpa [S] using hi, hp⟩

end Papers.RationalWitnesses.Raw

end
end BundlePart2

section BundlePart3
/- Source: Papers/IntegerFacetRealization.lean -/





@[expose] public section

/-!
# Rational realizations from exact integer facet certificates

Positive first coordinates put the certificate in an ordinary affine chart.
Positive row rescaling preserves all real spans and strict supporting signs.
The complete facet equality therefore induces the ordinary labelled face
order isomorphism.  The existing convex-hull construction then proves that
the new points are the actual extreme vertices of a rational realization.
-/

noncomputable section

open Matrix Module Set
open scoped BigOperators

namespace Papers.RationalWitnesses

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

private theorem span_image_rescale {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (s : Fin n → ℝ) (hs : ∀ i, s i ≠ 0)
    (T : Set (Fin n)) :
    Submodule.span ℝ ((fun i => s i • p i) '' T) = Submodule.span ℝ (p '' T) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    apply (Submodule.smul_mem_iff _ (hs i)).mp
    exact Submodule.subset_span ⟨i, hi, rfl⟩

def normalizedConfiguration {n : ℕ} (w : IntegerConfiguration n) :
    Matrix (Fin n) (Fin 5) ℝ := fun i j => (w i j : ℝ) / (w i 0 : ℝ)

theorem normalizedConfiguration_eq_rescale {n : ℕ} (w : IntegerConfiguration n) :
    normalizedConfiguration w = fun i => (w i 0 : ℝ)⁻¹ • realConfiguration w i := by
  ext i j
  simp [normalizedConfiguration, realConfiguration, div_eq_mul_inv, mul_comm]

theorem normalizedConfiguration_first {n : ℕ} (w : IntegerConfiguration n)
    (hw : ∀ i, 0 < w i 0) : ∀ i, normalizedConfiguration w i 0 = 1 := by
  intro i
  have h : (w i 0 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw i))
  simp [normalizedConfiguration, h]

theorem normalizedConfiguration_subsetRank {n : ℕ} (w : IntegerConfiguration n)
    (hw : ∀ i, 0 < w i 0) (T : Finset (Fin n)) :
    subsetRank (normalizedConfiguration w) T = subsetRank (realConfiguration w) T := by
  have hn : ∀ i, (w i 0 : ℝ)⁻¹ ≠ 0 := by
    intro i
    apply inv_ne_zero
    exact_mod_cast (ne_of_gt (hw i))
  unfold subsetRank
  rw [normalizedConfiguration_eq_rescale]
  exact congrArg (fun U : Submodule ℝ (Fin 5 → ℝ) => finrank ℝ U)
    (span_image_rescale (fun i => realConfiguration w i)
      (fun i => (w i 0 : ℝ)⁻¹) hn (↑T : Set (Fin n)))

theorem normalizedConfiguration_spans {n : ℕ} (w : IntegerConfiguration n)
    (hw : ∀ i, 0 < w i 0) (hp : Spans (realConfiguration w)) :
    Spans (normalizedConfiguration w) := by
  have hn : ∀ i, (w i 0 : ℝ)⁻¹ ≠ 0 := by
    intro i
    apply inv_ne_zero
    exact_mod_cast (ne_of_gt (hw i))
  have heq := span_image_rescale (fun i => realConfiguration w i)
    (fun i => (w i 0 : ℝ)⁻¹) hn Set.univ
  rw [Set.image_univ, Set.image_univ] at heq
  change Submodule.span ℝ (Set.range (normalizedConfiguration w)) = ⊤
  rw [normalizedConfiguration_eq_rescale, heq]
  exact hp

theorem normalizedConfiguration_support_iff {n : ℕ} (w : IntegerConfiguration n)
    (hw : ∀ i, 0 < w i 0) (T : Finset (Fin n)) (a : Fin 5 → ℝ) :
    StrictSupport (normalizedConfiguration w) T a ↔ StrictSupport (realConfiguration w) T a := by
  have hd (i) : (0 : ℝ) < (w i 0 : ℝ) := by exact_mod_cast hw i
  have heq (i) : a ⬝ᵥ normalizedConfiguration w i =
      (a ⬝ᵥ realConfiguration w i) / (w i 0 : ℝ) := by
    simp [normalizedConfiguration, realConfiguration, dotProduct, Finset.sum_div,
      mul_div_assoc]
  constructor
  · rintro ⟨hz, hp⟩
    constructor
    · intro i hi
      have h := hz i hi
      rw [heq, div_eq_zero_iff] at h
      exact h.resolve_right (ne_of_gt (hd i))
    · intro i hi
      have h := hp i hi
      rw [heq] at h
      exact (div_pos_iff_of_pos_right (hd i)).mp h
  · rintro ⟨hz, hp⟩
    constructor
    · intro i hi
      rw [heq, hz i hi, zero_div]
    · intro i hi
      rw [heq]
      exact div_pos (hp i hi) (hd i)

theorem normalizedConfiguration_facets_iff {n : ℕ} (w : IntegerConfiguration n)
    (hw : ∀ i, 0 < w i 0) (T : Finset (Fin n)) :
    FacetMask (normalizedConfiguration w) T ↔ FacetMask (realConfiguration w) T := by
  constructor
  · rintro ⟨hne, ⟨a, ha⟩, hr⟩
    refine ⟨hne, ⟨a, (normalizedConfiguration_support_iff w hw T a).mp ha⟩, ?_⟩
    simpa only [normalizedConfiguration_subsetRank w hw T] using hr
  · rintro ⟨hne, ⟨a, ha⟩, hr⟩
    refine ⟨hne, ⟨a, (normalizedConfiguration_support_iff w hw T a).mpr ha⟩, ?_⟩
    simpa only [normalizedConfiguration_subsetRank w hw T] using hr

theorem normalizedConfiguration_rational {n : ℕ} (w : IntegerConfiguration n) :
    Papers.RationalityTen.ChirotopeDensity.RationalCoordinates (normalizedConfiguration w) := by
  intro i j
  refine ⟨(w i j : ℚ) / (w i 0 : ℚ), ?_⟩
  simp [normalizedConfiguration]

/-- A certificate proves rational realizability for every actual full
four-polytope having exactly its labelled facets.  The only combinatorial
input is the facet-list correspondence supplied by the finite catalogue. -/
theorem rationallyRealizable_of_certificate {n f l c : ℕ}
    (P : ConvexPolytope 4) (e : Fin n ≃ P.vertices) (hP : P.IsFullDim)
    (w : IntegerConfiguration n) (C : FacetCertificate n f l c)
    (hC : C.Valid w) (hw : ∀ i, 0 < w i 0)
    (hfacets : ∀ T : Finset (Fin n),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (C.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P := by
  classical
  let p := vertexCoordinates P e
  let q := normalizedConfiguration w
  have hp : Spans p := vertexCoordinates_spans P e hP
  have hq : Spans q := normalizedConfiguration_spans w hw
    (spans_of_spanning_minor w C.spanningRows hC.1)
  have hpfirst : ∀ i, p i 0 = 1 := by intro i; rfl
  have hqfirst : ∀ i, q i 0 = 1 := normalizedConfiguration_first w hw
  have hf : ∀ T, FacetMask p T ↔ FacetMask q T := by
    intro T
    exact (hfacets T).trans ((C.facets_iff hC T).symm.trans
      (normalizedConfiguration_facets_iff w hw T).symm)
  have hequiv : LabelledPolytopeEquivalent p q :=
    ⟨actualFaceOrderIso_of_equal_facets p q hp hq hpfirst hqfirst hf,
      actualFaceOrderIso_preserves_labels p q hp hq hpfirst hqfirst hf⟩
  have hord : LabelledPolytopeEquivalent (ordinaryVertexCoordinates P e) (ordinaryPoints q) := by
    apply ordinary_equivalent_of_homogeneous
    simpa only [ordinaryVertexCoordinates_homogeneous,
      homogeneousPoints_ordinaryPoints q hqfirst] using hequiv
  obtain ⟨Q, φ, hvertices, _⟩ := actual_polytope_of_labelled_coordinates P e (ordinaryPoints q) hord
  refine ⟨Q, ⟨φ⟩, ?_⟩
  intro v hv j
  rw [hvertices] at hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  have hrat := rationalCoordinates_ordinaryPoints (normalizedConfiguration_rational w)
  exact hrat i j

end Papers.RationalWitnesses

end
end
end BundlePart3
