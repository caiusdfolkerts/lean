module

public import PaperVerification.WeightedRegularQuotientDimension
public import PaperVerification.AlternatingFormsChernRegularity
public import PaperVerification.ChernFinite

/-!
# Dimension of the paper's actual Chern-relation quotient

There are no geometric identifications among the assumptions of this file.
The relations are the descended root polynomials of Section 4, with coefficient
variable weights `1,...,s`, and the quotient is the literal ideal quotient.
Regularity and finiteness are proved independently from the common-zero
calculation; the graded exact sequences then determine its dimension.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] [CharZero K]

set_option backward.isDefEq.respectTransparency false in
/-- The full weighted Hilbert series of the literal Chern-relation quotient.
The homogeneous pieces are the images of the usual weight-`1,...,s` pieces,
so the grading is specified independently of the dimension formula. -/
theorem chern_relation_quotient_hilbertSeries (s w : ℕ) (hw : 0<w) :
    ∃ H : TauCeti.InternalGrading K
        (MvPolynomial (Fin s) K ⧸ Ideal.ofList (chernRelationSequence K s w)) ℕ,
      (∀ d, H.piece d =
        ((WeightedRegularQuotientDimension.polynomialGrading (K:=K)
          chernCoefficientWeight).piece d).map
        ((Ideal.ofList (chernRelationSequence K s w)).mkQ.restrictScalars K)) ∧
      GradedInjectiveQuotient.hilbertSeries H *
        (∏ i : Fin s, (1-PowerSeries.X^(i.val+1))) =
        ∏ i : Fin s, (1-PowerSeries.X^(w+i.val)) := by
  classical
  obtain ⟨H, hp, hh⟩ :=
    WeightedRegularQuotientDimension.exists_graded_quotient_hilbertSeries
      (K:=K) chernCoefficientWeight chernCoefficientWeight_ne_zero s
      (fun i : Fin s => chernCoefficientRelation s (w+i.val))
      (fun i : Fin s => w+i.val)
      (fun i => chernCoefficientRelation_isWeightedHomogeneous s (w+i.val))
      (chernRelationSequence_isWeaklyRegular_over_field s w hw)
  refine ⟨H, hp, ?_⟩
  exact hh

/-- The complete-intersection quotient has the expected total dimension for
all positive starting degrees, over every characteristic-zero field. -/
theorem chern_relation_quotient_finrank (s w : ℕ) (hw : 0<w) :
    Module.finrank K
      (MvPolynomial (Fin s) K ⧸ Ideal.ofList (chernRelationSequence K s w)) =
      (w+s-1).choose s := by
  classical
  letI := chern_relation_quotient_finite (K:=K) s w hw
  obtain ⟨H, _, hh⟩ := chern_relation_quotient_hilbertSeries (K:=K) s w hw
  have hd := FiniteGradedDimension.finrank_mul_product_degrees H
    (fun i : Fin s => i.val+1) (fun i : Fin s => w+i.val) hh
  have hn :
      Module.finrank K
          (MvPolynomial (Fin s) K ⧸ Ideal.ofList (chernRelationSequence K s w)) *
        (∏ i : Fin s, (i.val+1)) = (∏ i : Fin s, (w+i.val)) := by
    exact_mod_cast hd
  rw [← Finset.prod_range (fun i : ℕ => i+1),
    ← Finset.prod_range (fun i : ℕ => w+i)] at hn
  rw [← Nat.factorial_eq_prod_range_add_one, ← Nat.ascFactorial_eq_prod_range,
    Nat.ascFactorial_eq_factorial_mul_choose'] at hn
  exact Nat.eq_of_mul_eq_mul_right s.factorial_pos (by simpa only [mul_comm] using hn)

/-- The geometric odd-pencil parameter range gives the Gaussian polynomial's
value at one, with no restriction to a finite list of examples. -/
theorem odd_chern_relation_quotient_finrank (s N : ℕ) :
    Module.finrank K
      (MvPolynomial (Fin s) K ⧸
        Ideal.ofList (chernRelationSequence K s (2*(N-s)+1))) =
      (2*(N-s)+s).choose s := by
  have h := chern_relation_quotient_finrank (K:=K) s (2*(N-s)+1) (by omega)
  simpa only [Nat.add_right_comm _ 1, Nat.add_sub_cancel] using h

end PaperVerification.AlternatingForms
