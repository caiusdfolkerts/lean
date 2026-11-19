module

public import PaperVerification.IsotropicAttractingRank
public import PaperVerification.IsotropicAttractingIdeal

/-!
# Explicit affine coordinate rings for every nonempty attracting chart

The original two isotropy equations form a triangular system with unit
pivots.  The resulting equivalence concerns the quotient by the full
original ideal, over every commutative coefficient ring.  The remaining
variables are exactly the row entries outside the chosen equation pivots.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial

variable {R : Type*} [CommRing R] {k s : ℕ} {p : Fin s ↪ Fin (2*k+1)}

def normalizer : LowPair p ⊕ LowPair p → R :=
  Sum.elim (fun q => if (p q.val.2).val ≤ k then 1 else -1) (fun _ => -1)

theorem normalizer_square (q : LowPair p ⊕ LowPair p) :
    normalizer (R := R) q * normalizer q = 1 := by
  cases q with
  | inl q => simp only [normalizer, Sum.elim_inl]; split <;> simp
  | inr q => simp [normalizer]

/-- Each literal equation is multiplied by its chosen coefficient, which
is its own inverse. -/
def normalizedEquation (q : LowPair p ⊕ LowPair p) : MvPolynomial (Coordinate p) R :=
  C (normalizer q) * lowEquation q

theorem normalizedEquation_homogeneous (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) :
    (normalizedEquation (R := R) q).IsWeightedHomogeneous (coordinateWeight p)
      (coordinateWeight p (pivotEmbedding hp q)) := by
  unfold normalizedEquation
  cases q with
  | inl q =>
      change (C (normalizer (Sum.inl q)) * equation p (2*k+1) q.val.1 q.val.2).IsWeightedHomogeneous
        (coordinateWeight p) (coordinateWeight p (firstPivot hp q))
      rw [coordinateWeight_firstPivot]
      simpa only [zero_add] using
        (isWeightedHomogeneous_C (coordinateWeight p) (normalizer (R := R) (Sum.inl q))).mul
          (equation_homogeneous p (2*k+1) q.val.1 q.val.2)
  | inr q =>
      change (C (normalizer (Sum.inr q)) * equation p (2*k) q.val.1 q.val.2).IsWeightedHomogeneous
        (coordinateWeight p) (coordinateWeight p (secondPivot hp q))
      rw [coordinateWeight_secondPivot]
      simpa only [zero_add] using
        (isWeightedHomogeneous_C (coordinateWeight p) (normalizer (R := R) (Sum.inr q))).mul
          (equation_homogeneous p (2*k) q.val.1 q.val.2)

theorem lowPair_rows_ne (q : LowPair p) : q.val.1 ≠ q.val.2 := by
  intro h
  have hl := q.property.1
  rw [h] at hl
  exact lt_irrefl _ hl

/-- The selected coefficient is literally one after normalization. -/
theorem normalizedEquation_pivot_coeff (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) :
    (normalizedEquation (R := R) q).coeff (Finsupp.single (pivotEmbedding hp q) 1) = 1 := by
  rw [normalizedEquation, coeff_C_mul]
  cases q with
  | inl q =>
      change normalizer (R := R) (Sum.inl q) *
        (equation p (2*k+1) q.val.1 q.val.2).coeff
          (Finsupp.single (firstPivot hp q) 1) = 1
      rw [equation_coeff_single]
      change normalizer (R := R) (Sum.inl q) *
        ((if q.val.1 = q.val.1 then
          formMatrix (2*k+1) (firstPivot hp q).val.2 (p q.val.2) else 0) +
          if q.val.1 = q.val.2 then
            formMatrix (2*k+1) (p q.val.1) (firstPivot hp q).val.2 else 0) = 1
      rw [ite_eq_left rfl, ite_eq_right (lowPair_rows_ne q), add_zero, firstPivot_coefficient]
      simp only [normalizer, Sum.elim_inl]
      split <;> simp
  | inr q =>
      change normalizer (R := R) (Sum.inr q) *
        (equation p (2*k) q.val.1 q.val.2).coeff
          (Finsupp.single (secondPivot hp q) 1) = 1
      rw [equation_coeff_single]
      change normalizer (R := R) (Sum.inr q) *
        ((if q.val.2 = q.val.1 then
          formMatrix (2*k) (secondPivot hp q).val.2 (p q.val.2) else 0) +
          if q.val.2 = q.val.2 then
            formMatrix (2*k) (p q.val.1) (secondPivot hp q).val.2 else 0) = 1
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm (lowPair_rows_ne q)), zero_add,
        secondPivot_coefficient]
      simp only [normalizer, Sum.elim_inr]
      simp

theorem first_linear_lower (hp : IndependentPivots p) (q : LowPair p)
    (v : Coordinate p) (hne : v ≠ firstPivot hp q)
    (hv : (equation (R := R) p (2*k+1) q.val.1 q.val.2).coeff
      (Finsupp.single v 1) ≠ 0) :
    eliminationRank hp v < eliminationRank hp (firstPivot hp q) := by
  rcases equation_linear_support p (2*k+1) q.val.1 q.val.2 v hv with h | h
  · exfalso
    apply hne
    apply Subtype.ext
    apply Prod.ext h.1
    apply Fin.ext
    rw [firstPivot_column_val]
    omega
  · exact first_partner_lower hp q v h.1 h.2

theorem second_linear_lower (hp : IndependentPivots p) (q : LowPair p)
    (v : Coordinate p) (hne : v ≠ secondPivot hp q)
    (hv : (equation (R := R) p (2*k) q.val.1 q.val.2).coeff
      (Finsupp.single v 1) ≠ 0) :
    eliminationRank hp v < eliminationRank hp (secondPivot hp q) := by
  rcases equation_linear_support p (2*k) q.val.1 q.val.2 v hv with h | h
  · exact second_partner_lower hp q v h.1 h.2
  · exfalso
    apply hne
    apply Subtype.ext
    apply Prod.ext h.1
    apply Fin.ext
    rw [secondPivot_column_val]
    omega

theorem normalizedEquation_linear_lower (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) (v : Coordinate p) (hne : v ≠ pivotEmbedding hp q)
    (hv : (normalizedEquation (R := R) q).coeff (Finsupp.single v 1) ≠ 0) :
    eliminationRank hp v < eliminationRank hp (pivotEmbedding hp q) := by
  have he : (lowEquation (R := R) q).coeff (Finsupp.single v 1) ≠ 0 := by
    intro hz
    apply hv
    simp only [normalizedEquation, coeff_C_mul, hz, mul_zero]
  cases q with
  | inl q => exact first_linear_lower hp q v hne he
  | inr q => exact second_linear_lower hp q v hne he

/-- Every variable in the normalized remainder has strictly lower rank. -/
theorem normalizedEquation_remainder_lower (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) (v : Coordinate p)
    (hv : v ∈ (normalizedEquation (R := R) q - X (pivotEmbedding hp q)).vars) :
    eliminationRank hp v < eliminationRank hp (pivotEmbedding hp q) := by
  classical
  have hh := (normalizedEquation_homogeneous (R := R) hp q).sub
    (isWeightedHomogeneous_X R (coordinateWeight p) (pivotEmbedding hp q))
  rcases vars_lt_weight_or_linear (coordinateWeight p) (coordinateWeight_pos p)
      (normalizedEquation q - X (pivotEmbedding hp q)) _ hh v hv with h | h
  · exact eliminationRank_lt_of_weight_lt hp v (pivotEmbedding hp q) h
  · by_cases he : v = pivotEmbedding hp q
    · subst v
      simp only [coeff_sub, normalizedEquation_pivot_coeff, coeff_single_X,
        and_self, ite_true, sub_self, ne_eq, not_true_eq_false] at h
    · apply normalizedEquation_linear_lower (R := R) hp q v he
      simpa only [coeff_sub, coeff_single_X, true_and, ite_eq_right (Ne.symm he),
        sub_zero] using h

/-- Extend the normalized remainders by zero on free coordinates. -/
def coordinateRemainder (hp : IndependentPivots p) :
    Coordinate p → MvPolynomial (Coordinate p) R :=
  Function.extend (pivotEmbedding hp)
    (fun q => normalizedEquation q - X (pivotEmbedding hp q)) (fun _ => 0)

@[simp] theorem coordinateRemainder_pivot (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) :
    coordinateRemainder (R := R) hp (pivotEmbedding hp q) =
      normalizedEquation q - X (pivotEmbedding hp q) :=
  (pivotEmbedding hp).injective.extend_apply _ _ q

theorem coordinateRemainder_lower (hp : IndependentPivots p) :
    ∀ i j, j ∈ (coordinateRemainder (R := R) hp i).vars →
      eliminationRank hp j < eliminationRank hp i := by
  intro i j hj
  by_cases hi : i ∈ Set.range (pivotEmbedding hp)
  · obtain ⟨q, rfl⟩ := hi
    rw [coordinateRemainder_pivot] at hj
    exact normalizedEquation_remainder_lower hp q j hj
  · have hz : coordinateRemainder (R := R) hp i = 0 :=
      Function.extend_apply' _ _ _ hi
    simp [hz] at hj

theorem lowIdeal_eq_normalized_span :
    lowIdeal (R := R) (p := p) = Ideal.span (Set.range (normalizedEquation (R := R) (p := p))) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨q, rfl⟩
    have he : lowEquation (R := R) q = C (normalizer q) * normalizedEquation q := by
      rw [normalizedEquation, ← mul_assoc, ← map_mul, normalizer_square, map_one, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)

theorem normalized_span_eq_triangular_span (hp : IndependentPivots p) :
    Ideal.span (Set.range (normalizedEquation (R := R) (p := p))) =
      Ideal.span ((fun i => X i + coordinateRemainder (R := R) hp i) ''
        Set.range (pivotEmbedding hp)) := by
  congr 1
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨pivotEmbedding hp q, ⟨q, rfl⟩, ?_⟩
    dsimp only
    rw [coordinateRemainder_pivot]
    ring
  · rintro ⟨i, ⟨q, rfl⟩, rfl⟩
    refine ⟨q, ?_⟩
    dsimp only
    rw [coordinateRemainder_pivot]
    ring

/-- The literal attracting-chart coordinate ring is a polynomial algebra
on its free entries. All original equations occur in the source ideal. -/
def attractingCoordinateRingEquiv (hp : IndependentPivots p) :
    (MvPolynomial (Coordinate p) R ⧸ isotropyIdeal p (2*k+1) (2*k)) ≃ₐ[R]
      MvPolynomial {i : Coordinate p // i ∉ Set.range (pivotEmbedding hp)} R :=
  (Ideal.quotientEquivAlgOfEq R ((isotropyIdeal_eq_lowIdeal hp).trans
    (lowIdeal_eq_normalized_span.trans (normalized_span_eq_triangular_span hp)))).trans
      (PaperVerification.TriangularPolynomialCoordinates.triangularQuotientEquiv
        (eliminationRank hp) (coordinateRemainder hp) (coordinateRemainder_lower hp)
        (Set.range (pivotEmbedding hp)))

end PaperVerification.IsotropicAttractingCoordinates
