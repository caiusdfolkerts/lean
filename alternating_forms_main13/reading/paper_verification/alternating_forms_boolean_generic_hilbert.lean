module

public import PaperVerification.AlternatingFormsBooleanUpperBound
public import PaperVerification.AlternatingFormsBooleanRelationMatrix

/-!
# The exact generic Hilbert function of two Boolean linear equations

The lower certificate is the universal determinant-kernel minor.  The upper
certificate is an actual minor of the two multiplication matrices, detected
at the one-parameter pencil.  Their product is nonzero in the original
coefficient polynomial ring.  Its nonvanishing proves equality for the
ordinary homogeneous quotient piece, in every degree and every dimension.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BooleanGenericHilbert

open scoped BigOperators Classical
open BooleanWalks BooleanBadRelations BooleanQuotient BooleanRelationMatrix EvenDeterminants

variable {K : Type*} [Field K] [CharZero K]

def upperParameterEvaluation (m : ℕ) :
    UniversalParameters K m →+* BooleanUpperBound.ParameterField K :=
  MvPolynomial.eval₂Hom BooleanUpperBound.constants
    (fun z ↦ if z.1 then BooleanUpperBound.second m z.2 else BooleanUpperBound.first m z.2)

@[simp] theorem upperParameterEvaluation_first (m : ℕ) (i : Fin m) :
    upperParameterEvaluation (K := K) m (universalFirst m i) = BooleanUpperBound.first m i := by
  simp [upperParameterEvaluation, universalFirst]

@[simp] theorem upperParameterEvaluation_second (m : ℕ) (i : Fin m) :
    upperParameterEvaluation (K := K) m (universalSecond m i) = BooleanUpperBound.second m i := by
  simp [upperParameterEvaluation, universalSecond]

/-- The upper certificate is a minor of the original finite relation matrix,
not a polynomial defined through an asserted generic rank. -/
theorem exists_upper_minor (m r : ℕ) :
    ∃ p : UniversalParameters K m, p ≠ 0 ∧
      ∀ b c : Fin m → K, evaluateParameters b c p ≠ 0 →
        Module.finrank K (piece b c (r+1)) ≤ Fintype.card (GoodSubset m (r+1)) := by
  let φ := upperParameterEvaluation (K := K) m
  have hmap : (universalMatrix K m r).map φ =
      relationMatrix (BooleanUpperBound.first (K := K) m) (BooleanUpperBound.second m) r := by
    simp only [φ, universalMatrix_specialize, upperParameterEvaluation_first,
      upperParameterEvaluation_second]
  have hrank : Fintype.card (BadSubset m (r+1)) ≤
      ((universalMatrix K m r).map φ).rank := by
    rw [hmap, relationMatrix_rank]
    exact BooleanUpperBound.bad_card_le_finrank_relations m (r+1)
  obtain ⟨rows, cols, hminor⟩ := Matrix.le_rank_iff_exists_det_submatrix_ne_zero.mp hrank
  let p : UniversalParameters K m := ((universalMatrix K m r).submatrix rows cols).det
  have hφ : φ p ≠ 0 := by
    dsimp only [p]
    rw [φ.map_det]
    change (((universalMatrix K m r).map φ).submatrix rows cols).det ≠ 0
    exact hminor
  refine ⟨p, ?_, ?_⟩
  · intro hp
    exact hφ (by rw [hp, map_zero])
  · intro b c hp
    have hminor' : ((relationMatrix b c r).submatrix rows cols).det ≠ 0 := by
      have he : evaluateParameters b c p =
          ((relationMatrix b c r).submatrix rows cols).det := by
        dsimp only [p]
        rw [(evaluateParameters b c).map_det]
        change (((universalMatrix K m r).map (evaluateParameters b c)).submatrix rows cols).det = _
        rw [universalMatrix_evaluate]
      rwa [he] at hp
    have hlower : Fintype.card (BadSubset m (r+1)) ≤ (relationMatrix b c r).rank :=
      Matrix.le_rank_iff_exists_det_submatrix_ne_zero.mpr ⟨rows, cols, hminor'⟩
    have hdim := piece_finrank_add_matrix_rank b c r
    have hcard : Fintype.card (BadSubset m (r+1)) =
        Fintype.card (FixedSubsets (Fin m) (r+1)) - Fintype.card (GoodSubset m (r+1)) :=
      Fintype.card_subtype_compl (Good (m := m) (q := r+1))
    have hle : Fintype.card (GoodSubset m (r+1)) ≤ Fintype.card (FixedSubsets (Fin m) (r+1)) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    omega

/-- Both generic bounds hold on the nonvanishing locus of one explicitly
constructed nonzero polynomial in the original two coefficient vectors. -/
theorem generic_boolean_positive_degree (m r : ℕ) :
    ∃ p : UniversalParameters K m, p ≠ 0 ∧
      ∀ b c : Fin m → K, evaluateParameters b c p ≠ 0 →
        Module.finrank K (piece b c (r+1)) = Fintype.card (GoodSubset m (r+1)) := by
  obtain ⟨u, hu, hupper⟩ := exists_upper_minor (K := K) m r
  refine ⟨goodCoefficientMinor m (r+1) * u,
    mul_ne_zero (goodCoefficientMinor_ne_zero m (r+1)) hu, ?_⟩
  intro b c h
  rw [map_mul] at h
  obtain ⟨hgood, hu⟩ := mul_ne_zero_iff.mp h
  exact le_antisymm (hupper b c hu) (good_boolean_lower_bound_of_minor (r+1) b c hgood)

theorem all_good_degree_zero {m : ℕ} (S : FixedSubsets (Fin m) 0) : Good S := by
  have hS : S.val = ∅ := Finset.card_eq_zero.mp S.property
  intro r hr
  simp only [prefixCount, hS, Finset.filter_empty, Finset.card_empty,
    Nat.mul_zero, Nat.add_zero, Nat.zero_le, true_and]
  exact hr

theorem boolean_degree_zero (m : ℕ) (b c : Fin m → K) :
    Module.finrank K (piece b c 0) = Fintype.card (GoodSubset m 0) := by
  have hdim := (relations b c 0).finrank_quotient_add_finrank
  rw [(cokernelEquivPiece b c 0).finrank_eq, relations_zero, finrank_bot,
    Nat.add_zero, Module.finrank_pi] at hdim
  have he : GoodSubset m 0 ≃ FixedSubsets (Fin m) 0 :=
    Equiv.subtypeUnivEquiv all_good_degree_zero
  exact hdim.trans (Fintype.card_congr he).symm

/-- A complete all-degree statement with the ordinary quotient and exact
walk-defined good subsets.  There is no restriction on m or q. -/
theorem generic_boolean_degree (m q : ℕ) :
    ∃ p : UniversalParameters K m, p ≠ 0 ∧
      ∀ b c : Fin m → K, evaluateParameters b c p ≠ 0 →
        Module.finrank K (piece b c q) = Fintype.card (GoodSubset m q) := by
  cases q with
  | zero => exact ⟨1, one_ne_zero, fun b c h ↦ boolean_degree_zero m b c⟩
  | succ r => exact generic_boolean_positive_degree m r

end PaperVerification.AlternatingForms.BooleanGenericHilbert
