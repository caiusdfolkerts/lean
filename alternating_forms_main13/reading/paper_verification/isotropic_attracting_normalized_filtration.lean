module

public import PaperVerification.IsotropicAttractingMinorFiltration
public import PaperVerification.HomogeneousQuotientCharts

/-!
# The actual normalized rings of the homogeneous filtration

Adding earlier Plücker coordinates to the original homogeneous isotropy
ideal, then taking the genuine pivot affine chart, gives exactly the
closed row-echelon cell already eliminated.  The comparison is an
isomorphism of the full coordinate rings, before taking radicals.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open MvPolynomial
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {s n t : ℕ}

/-- Any ordering refining Plücker weight has precisely these properties
for the set of indices strictly before a chosen pivot. -/
def EarlierSet (p : PluckerIndex s n) (E : Set (PluckerIndex s n)) : Prop :=
  (∀ I, pluckerWeight I < pluckerWeight p → I ∈ E) ∧
    ∀ I ∈ E, pluckerWeight I ≤ pluckerWeight p ∧ p ≠ I

/-- The original homogeneous coordinate ideal of the filtration stage. -/
def filtrationIdeal (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    Ideal (MvPolynomial (PluckerIndex (t+2) n) K) :=
  isotropicPluckerIdeal (canonicalForms c₁ c₂) ⊔ Ideal.span (X '' E)

theorem filtrationIdeal_isHomogeneous (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    (filtrationIdeal (K := K) E c₁ c₂).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex (t+2) n) K) := by
  apply (isotropicPluckerIdeal_isHomogeneous (canonicalForms c₁ c₂)).sup
  apply Ideal.homogeneous_span
  rintro _ ⟨I, hI, rfl⟩
  exact ⟨1, isHomogeneous_X K I⟩

theorem filtrationIdeal_mono {E F : Set (PluckerIndex (t+2) n)}
    (hEF : E ⊆ F) (c₁ c₂ : ℕ) :
    filtrationIdeal (K := K) E c₁ c₂ ≤ filtrationIdeal F c₁ c₂ :=
  sup_le_sup_left (Ideal.span_mono (Set.image_mono hEF)) _

/-- Exactly the earlier homogeneous coordinates become the entry ideal
of the row-echelon chart. Equal weights cause no extra equations. -/
theorem earlierVariables_map (p : PluckerIndex s n) (E : Set (PluckerIndex s n))
    (hE : EarlierSet p E) :
    (Ideal.span (X '' E : Set (MvPolynomial (PluckerIndex s n) K))).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        earlyMinorIdeal (K := K) p := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨I, hI, rfl⟩
    exact nonpivot_low_minor_mem_early p I (hE.2 I hI).1 (hE.2 I hI).2
  · apply Ideal.span_le.mpr
    rintro _ ⟨I, hI, rfl⟩
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨I, hE.1 I hI, rfl⟩)

variable [CharZero K]

/-- The full homogeneous filtration ideal maps to the literal full cell
ideal in the original matrix chart. -/
theorem filtrationIdeal_map_chart (p : PluckerIndex (t+2) n)
    (E : Set (PluckerIndex (t+2) n)) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    (filtrationIdeal (K := K) E c₁ c₂).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        fullCellIdeal (K := K) p c₁ c₂ := by
  rw [filtrationIdeal, Ideal.map_sup, isotropicPluckerIdeal_map_chart_eq,
    earlierVariables_map p E hE, earlyMinorIdeal_eq_negativeCoordinates]
  rfl

/-- Evaluate every original homogeneous Plücker coordinate on the
universal row-echelon cell, preserving every original isotropy equation. -/
def normalizedCellEvaluation (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    MvPolynomial (PluckerIndex (t+2) n) K →ₐ[K]
      (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂) :=
  (fullChartToCell p c₁ c₂).comp (matrixMinorEvaluation (pluckerChartMatrix p))

theorem normalizedCellEvaluation_surjective (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    Function.Surjective (normalizedCellEvaluation (K := K) p c₁ c₂) :=
  (fullChartToCell_surjective p c₁ c₂).comp (matrixMinorEvaluation_chart_surjective p)

/-- Exact kernel of the normalized coordinate evaluation. The only
additional relation is the genuine pivot normalization `X p = 1`. -/
theorem normalizedCellEvaluation_kernel (p : PluckerIndex (t+2) n)
    (E : Set (PluckerIndex (t+2) n)) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    RingHom.ker (normalizedCellEvaluation (K := K) p c₁ c₂).toRingHom =
      filtrationIdeal E c₁ c₂ ⊔ Ideal.span {X p - 1} := by
  change RingHom.ker ((fullChartToCell (K := K) p c₁ c₂).toRingHom.comp
    (matrixMinorEvaluation (pluckerChartMatrix p)).toRingHom) = _
  rw [← RingHom.comap_ker, fullChartToCell_kernel,
    ← filtrationIdeal_map_chart p E hE c₁ c₂,
    Ideal.comap_map_of_surjective'
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom
      (matrixMinorEvaluation_chart_surjective p),
    matrixMinorEvaluation_chart_kernel, pluckerBigCellIdeal]
  have hle : matrixPluckerIdeal (K := K) (s := t+2) (n := n) ≤
      filtrationIdeal E c₁ c₂ := le_trans le_sup_left le_sup_left
  rw [← sup_assoc, sup_eq_left.mpr hle]

/-- The actual normalized quotient defining the filtration stratum is
isomorphic to the original common-isotropic echelon coordinate ring. -/
def normalizedFiltrationCellEquiv (p : PluckerIndex (t+2) n)
    (E : Set (PluckerIndex (t+2) n)) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    (MvPolynomial (PluckerIndex (t+2) n) K ⧸
      (filtrationIdeal E c₁ c₂ ⊔ Ideal.span {X p - 1})) ≃ₐ[K]
      (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂) :=
  (Ideal.quotientEquivAlgOfEq K
    (normalizedCellEvaluation_kernel p E hE c₁ c₂).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (normalizedCellEvaluation_surjective p c₁ c₂))

/-- The whole scheme-theoretic pivot stratum of the original homogeneous
filtration is a polynomial algebra for every independent pivot. -/
def normalizedFiltrationPolynomialEquiv {k : ℕ} (p : PluckerIndex (t+2) (2*k+1))
    (E : Set (PluckerIndex (t+2) (2*k+1))) (hE : EarlierSet p E)
    (hp : IndependentPivots (indexEmbedding p)) :
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
      (filtrationIdeal E (2*k+1) (2*k) ⊔ Ideal.span {X p - 1})) ≃ₐ[K]
      MvPolynomial {i : Coordinate (indexEmbedding p) //
        i ∉ Set.range (pivotEmbedding hp)} K :=
  (normalizedFiltrationCellEquiv p E hE (2*k+1) (2*k)).trans
    (attractingCoordinateRingEquiv hp)

end PaperVerification.IsotropicAttractingCharts
