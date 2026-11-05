module

public import PaperVerification.RichardsonTautologicalRanks

/-!
# The full rank ideal of the actual tautological flag projections

The independent determinantal ideal on each ambient chart is generated
by minors of the actual tautological frame, viewed as genuine
structure-sheaf sections.  Its equality with the polynomial rank ideal
is proved before taking any quotient, radical, or geometric point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite Matrix
open scoped Matrix

namespace PaperVerification.SchubertRankIdeals

variable {R S : Type*} [CommRing R] [CommRing S] {s n : ℕ}

/-- Base change of the full restricted-minor ideal, over arbitrary
commutative rings. -/
theorem restrictedMinorIdeal_map (f : R →+* S)
    (A : Matrix (Fin s) (Fin n) R) (q : ℕ) (C : Set (Fin n)) :
    (restrictedMinorIdeal A q C).map f = restrictedMinorIdeal (A.map f) q C := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro z ⟨rows, cols, hcols, rfl⟩
    change f ((A.submatrix rows cols).det) ∈ restrictedMinorIdeal (A.map f) q C
    rw [f.map_det, RingHom.mapMatrix_apply]
    exact Ideal.subset_span ⟨rows, cols, hcols, rfl⟩
  · apply Ideal.span_le.mpr
    rintro z ⟨rows, cols, hcols, rfl⟩
    change ((A.submatrix rows cols).map f).det ∈ (restrictedMinorIdeal A q C).map f
    rw [← RingHom.mapMatrix_apply, ← f.map_det]
    exact Ideal.mem_map_of_mem f (Ideal.subset_span ⟨rows, cols, hcols, rfl⟩)

end PaperVerification.SchubertRankIdeals

namespace PaperVerification.AlternatingForms

variable {R S : Type*} [CommRing R] [CommRing S] {s n : ℕ}

theorem richardsonChartRankIdeal_map (f : R →+* S)
    (A : Matrix (Fin s) (Fin n) R) (α β : Fin s → Fin n) :
    (richardsonChartRankIdeal A α β).map f =
      richardsonChartRankIdeal (A.map f) α β := by
  simp only [richardsonChartRankIdeal, Ideal.map_iSup, Ideal.map_sup,
    SchubertRankIdeals.restrictedMinorIdeal_map]

variable {K : Type} [Field K] {t : ℕ}

/-- The matrix of the genuine ambient-coordinate projections on the
actual local basis of the tautological subbundle. -/
def ambientTautologicalFrameMatrix (p : PluckerIndex (t + 2) n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    Matrix (Fin (t + 2)) (Fin n) Γ(ambientGrassmannian (K := K) t n, U) :=
  fun i c ↦ tautologicalSectionCoordinates emptyAlternatingTuple U
    (tautologicalRowSection p emptyAlternatingTuple U hU i) c

theorem ambientTautologicalFrameMatrix_eq (p : PluckerIndex (t + 2) n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    ambientTautologicalFrameMatrix p U hU =
      (pluckerChartMatrix p).map (tautologicalLocalPolynomialHom p emptyAlternatingTuple U hU) := by
  funext i c
  exact congrFun (tautologicalRowSection_coordinates p emptyAlternatingTuple U hU i) c

/-- Full opposite-flag determinantal ideal in the actual section ring. -/
def ambientRichardsonIntrinsicChartIdeal (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    Ideal Γ(ambientGrassmannian (K := K) t n, U) :=
  richardsonChartRankIdeal (ambientTautologicalFrameMatrix p U hU) α β

/-- Exact equality of the actual tautological rank ideal and the
polynomial chart ideal, on every subopen of each chart. -/
theorem ambientRichardsonIntrinsicChartIdeal_eq_map (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    ambientRichardsonIntrinsicChartIdeal p α β U hU =
      (richardsonChartIdeal (K := K) p α β).map
        (tautologicalLocalPolynomialHom p emptyAlternatingTuple U hU) := by
  rw [ambientRichardsonIntrinsicChartIdeal, ambientTautologicalFrameMatrix_eq]
  exact (richardsonChartRankIdeal_map _ _ α β).symm

end PaperVerification.AlternatingForms
