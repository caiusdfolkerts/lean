module

public import PaperVerification.AlternatingFormsPluckerIsotropy
public import PaperVerification.IsotropicAttractingPairing
public import PaperVerification.IsotropicAttractingElimination

/-!
# Attracting cells inside the original Plücker affine charts

The original chart polynomial ring retains every nonpivot matrix entry.
Setting the entries to the left of their row pivots to zero gives exactly
the row-echelon coordinates used by the explicit elimination theorem.
This restriction carries the original increasing-pair isotropy ideal to
the full skew-matrix ideal, and its kernel is the coordinate ideal of
those vanishing entries.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open MvPolynomial
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open PaperVerification.TriangularPolynomialCoordinates
open scoped BigOperators

variable {K : Type*} [Field K] {s n t : ℕ}

abbrev indexEmbedding (p : PluckerIndex s n) : Fin s ↪ Fin n :=
  ⟨p.val, p.property.injective⟩

@[simp] theorem indexEmbedding_apply (p : PluckerIndex s n) (i : Fin s) :
    indexEmbedding p i = p.val i := rfl

/-- These are precisely the nonpivot entries weakly left of the row
pivot; equality cannot occur because the column is a nonpivot. -/
def negativeCoordinates (p : PluckerIndex s n) : Set (PluckerChartVariable p) :=
  {v | ¬ (p.val v.1).val < v.2.val.val}

def positiveCoordinateEquiv (p : PluckerIndex s n) :
    {v : PluckerChartVariable p // v ∉ negativeCoordinates p} ≃ Coordinate (indexEmbedding p) where
  toFun v := ⟨(v.val.1, v.val.2.val), by
    simpa only [negativeCoordinates, Set.mem_ofPred_eq, not_not, indexEmbedding_apply]
      using v.property,
    v.val.2.property⟩
  invFun v := ⟨(v.val.1, ⟨v.val.2, v.property.2⟩), by
    simpa only [negativeCoordinates, Set.mem_ofPred_eq, not_not, indexEmbedding_apply]
      using v.property.1⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

/-- The actual polynomial restriction to row-echelon matrices. -/
def fullChartRestriction (p : PluckerIndex s n) :
    MvPolynomial (PluckerChartVariable p) K →ₐ[K]
      MvPolynomial (Coordinate (indexEmbedding p)) K :=
  (renameEquiv K (positiveCoordinateEquiv p)).toAlgHom.comp
    (eraseCoordinates (negativeCoordinates p))

theorem fullChartRestriction_X (p : PluckerIndex s n) (v : PluckerChartVariable p) :
    fullChartRestriction (K := K) p (X v) =
      if h : (p.val v.1).val < v.2.val.val then
        X (⟨(v.1,v.2.val),h,v.2.property⟩ : Coordinate (indexEmbedding p)) else 0 := by
  classical
  change (renameEquiv K (positiveCoordinateEquiv p))
    (eraseCoordinates (negativeCoordinates p) (X v)) = _
  by_cases h : (p.val v.1).val < v.2.val.val
  · have hv : v ∉ negativeCoordinates p := not_not.mpr h
    rw [eraseCoordinates, MvPolynomial.aeval_X, dite_eq_left hv,
      dite_eq_left h, renameEquiv_apply, MvPolynomial.rename_X]
    rfl
  · have hv : ¬ v ∉ negativeCoordinates p := fun hv => h (not_not.mp hv)
    rw [eraseCoordinates, MvPolynomial.aeval_X, dite_eq_right hv,
      map_zero, dite_eq_right h]

theorem fullChartRestriction_surjective (p : PluckerIndex s n) :
    Function.Surjective (fullChartRestriction (K := K) p) :=
  (renameEquiv K (positiveCoordinateEquiv p)).surjective.comp
    (eraseCoordinates_surjective (negativeCoordinates p))

theorem fullChartRestriction_kernel (p : PluckerIndex s n) :
    RingHom.ker (fullChartRestriction (K := K) p).toRingHom =
      Ideal.span (X '' negativeCoordinates p) := by
  change RingHom.ker ((renameEquiv K (positiveCoordinateEquiv p)).toRingHom.comp
    (eraseCoordinates (R := K) (negativeCoordinates p)).toRingHom) = _
  rw [RingHom.ker_comp_of_injective _
    (f := (renameEquiv K (positiveCoordinateEquiv p)).toRingHom)
    (renameEquiv K (positiveCoordinateEquiv p)).injective]
  exact ker_eraseCoordinates (negativeCoordinates p)

/-- The restricted original normalized matrix is the literal echelon
matrix, entry by entry. -/
theorem fullChartRestriction_matrix (p : PluckerIndex s n) (i : Fin s) (j : Fin n) :
    fullChartRestriction (K := K) p (pluckerChartMatrix p i j) =
      row (indexEmbedding p) i j := by
  classical
  by_cases hij : j = p.val i
  · simp [pluckerChartMatrix, row, hij]
  · by_cases hj : j ∈ Set.range p.val
    · simp only [pluckerChartMatrix, Matrix.of_apply, ite_eq_right hij, dite_eq_left hj, map_zero]
      simp [row, indexEmbedding, hij, hj]
    · rw [pluckerChartMatrix_nonpivot p i ⟨j,hj⟩, fullChartRestriction_X]
      simp only [row, indexEmbedding, Function.Embedding.coeFn_mk, ite_eq_right hij]
      by_cases hlt : (p.val i).val < j.val
      · simp [hlt, hj]
      · simp [hlt]

/-- Coefficients of the same skew matrix in the original convention. -/
def canonicalCoefficient (c : ℕ) : StrictPairs n → K :=
  fun q => formMatrix c q.val.1 q.val.2

theorem fullChartRestriction_pairing (p : PluckerIndex (t+2) n)
    (c : ℕ) (i j : Fin (t+2)) :
    fullChartRestriction (K := K) p
      (alternatingRowPair (canonicalCoefficient (K := K) c) (pluckerChartMatrix p) i j) =
      equation (indexEmbedding p) c i j := by
  simp only [alternatingRowPair, map_sum, map_smul, map_sub, map_mul,
    fullChartRestriction_matrix]
  rw [equation_eq_increasing_pair_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Algebra.smul_def]
  rfl

def canonicalForms (c₁ c₂ : ℕ) : Fin 2 → StrictPairs n → K :=
  fun l => canonicalCoefficient (if l = 0 then c₁ else c₂)

/-- The image is the full original isotropy ideal in the smaller cell
ring. No radical or reduction is taken. -/
theorem fullChartRestriction_isotropyIdeal (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    (isotropicChartIdeal p (canonicalForms (K := K) c₁ c₂)).map
        (fullChartRestriction p).toRingHom =
      isotropyIdeal (indexEmbedding p) c₁ c₂ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,q⟩,rfl⟩
    change fullChartRestriction p
      (alternatingRowPair (canonicalForms c₁ c₂ l) (pluckerChartMatrix p) q.val.1 q.val.2)
        ∈ isotropyIdeal (indexEmbedding p) c₁ c₂
    unfold canonicalForms
    rw [fullChartRestriction_pairing]
    apply Ideal.subset_span
    by_cases hl : l = 0
    · exact ⟨(true,q.val.1,q.val.2), by simp [hl]⟩
    · exact ⟨(false,q.val.1,q.val.2), by simp [hl]⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨b,i,j⟩,rfl⟩
    let l : Fin 2 := if b then 0 else 1
    have hl : (if l = 0 then c₁ else c₂) = (if b then c₁ else c₂) := by
      cases b <;> simp [l]
    have hmem := Ideal.mem_map_of_mem (fullChartRestriction (K := K) p).toRingHom
      (alternatingRowPair_mem_chartIdeal p (canonicalForms c₁ c₂) l i j)
    change fullChartRestriction p
      (alternatingRowPair (canonicalForms c₁ c₂ l) (pluckerChartMatrix p) i j) ∈ _ at hmem
    change equation (R := K) (indexEmbedding p) (if b then c₁ else c₂) i j ∈
      (isotropicChartIdeal p (canonicalForms c₁ c₂)).map
        (fullChartRestriction (K := K) p).toRingHom
    rw [canonicalForms, fullChartRestriction_pairing, hl] at hmem
    exact hmem

/-- Literal closed-cell ideal in the original full Plücker chart. -/
def fullCellIdeal (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  isotropicChartIdeal p (canonicalForms c₁ c₂) ⊔ Ideal.span (X '' negativeCoordinates p)

def fullChartToCell (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    MvPolynomial (PluckerChartVariable p) K →ₐ[K]
      (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂) :=
  (Ideal.Quotient.mkₐ K (isotropyIdeal (indexEmbedding p) c₁ c₂)).comp (fullChartRestriction p)

theorem fullChartToCell_surjective (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    Function.Surjective (fullChartToCell (K := K) p c₁ c₂) :=
  Ideal.Quotient.mk_surjective.comp (fullChartRestriction_surjective p)

theorem fullChartToCell_kernel (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    RingHom.ker (fullChartToCell (K := K) p c₁ c₂).toRingHom = fullCellIdeal p c₁ c₂ := by
  change RingHom.ker ((Ideal.Quotient.mk (isotropyIdeal (indexEmbedding p) c₁ c₂)).comp
    (fullChartRestriction (K := K) p).toRingHom) = _
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← fullChartRestriction_isotropyIdeal,
    Ideal.comap_map_of_surjective' (fullChartRestriction (K := K) p).toRingHom
      (fullChartRestriction_surjective p),
    fullChartRestriction_kernel]
  rfl

/-- The original chart with precisely its left entries set to zero has
the same complete coordinate ring as the explicitly eliminated cell. -/
def fullCellCoordinateRingEquiv (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    (MvPolynomial (PluckerChartVariable p) K ⧸ fullCellIdeal p c₁ c₂) ≃ₐ[K]
      (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂) :=
  (Ideal.quotientEquivAlgOfEq K (fullChartToCell_kernel p c₁ c₂).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (fullChartToCell_surjective p c₁ c₂))

/-- Every permitted original affine cell is an actual affine space. -/
def originalCellPolynomialEquiv {k : ℕ} (p : PluckerIndex (t+2) (2*k+1))
    (hp : IndependentPivots (indexEmbedding p)) :
    (MvPolynomial (PluckerChartVariable p) K ⧸ fullCellIdeal p (2*k+1) (2*k)) ≃ₐ[K]
      MvPolynomial {i : Coordinate (indexEmbedding p) //
        i ∉ Set.range (pivotEmbedding hp)} K :=
  (fullCellCoordinateRingEquiv p (2*k+1) (2*k)).trans (attractingCoordinateRingEquiv hp)

end PaperVerification.IsotropicAttractingCharts
