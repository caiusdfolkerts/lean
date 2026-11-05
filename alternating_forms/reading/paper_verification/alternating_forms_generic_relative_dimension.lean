module

public import PaperVerification.GenericPolynomialSectionDimension
public import PaperVerification.AlternatingFormsGenericSmoothness
public import PaperVerification.AlternatingFormsGenericNegativeDimension
public import PaperVerification.CommonIsotropicProjectiveNonempty
public import PaperVerification.AlternatingFormsColoredEdges

/-!
# The actual generic common-isotropic scheme has the expected relative dimension

The dimension is established using the original affine quotient presentations
and their full Jacobian-minor cover. The same parameter polynomial works for
every Plücker chart. The pair case combines this with an actual field-valued
point supplied by the common-isotropic induction, in every ambient dimension.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped BigOperators

namespace PaperVerification.AlternatingForms

open GenericSectionDifferentials

variable {K : Type} [Field K] [CharZero K] {t n m : ℕ}

private lemma relativeDimension_chart_variable_count (p : PluckerIndex (t + 2) n) :
    Fintype.card (PluckerChartVariable p) = (t + 2) * (n - (t + 2)) := by
  classical
  have h : Fintype.card (Set.range p.val) = t + 2 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_congr (Equiv.ofInjective p.val p.property.injective)).symm
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype_compl,
    Fintype.card_fin, h]

/-- The original quotient chart is locally standard smooth with exactly the
number of matrix variables minus the number of row-isotropy equations. -/
theorem isotropicChartRing_locally_standardSmoothOfRelativeDimension
    (p : PluckerIndex (t + 2) n) (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a
      (isotropicChartSmoothnessPolynomial (K := K) (m := m) p) ≠ 0) :
    RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension
        ((t + 2) * (n - (t + 2)) - m * (t + 2).choose 2))
      (algebraMap K (IsotropicChartRing p (fun l i ↦ a (l, i)))) := by
  classical
  have h := linearSection_quotient_locally_standardSmoothOfRelativeDimension
    (chartSectionEvaluation (K:=K) (m:=m) p) (chartSectionExtension (K:=K) (m:=m) p)
    (chartSectionEvaluation_rightInverse (K:=K) (m:=m) p) a ha
  have hf : linearSection (chartSectionEvaluation (K:=K) (m:=m) p) a =
      fun j : Fin m × StrictPairs (t + 2) ↦
        alternatingRowPair (fun i ↦ a (j.1, i)) (pluckerChartMatrix (K:=K) p)
          j.2.val.1 j.2.val.2 := by
    funext j
    exact chartSectionEvaluation_sum p a j
  rw [hf] at h
  rw [relativeDimension_chart_variable_count, Fintype.card_prod,
    Fintype.card_fin, card_strictPairs] at h
  exact h

/-- Every original chart, on the same nonempty parameter open, has the same
expected smooth relative dimension. -/
theorem isotropic_all_charts_relativeDimension (t n m : ℕ)
    (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K := K) t n m) ≠ 0)
    (p : PluckerIndex (t + 2) n) :
    RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension
        ((t + 2) * (n - (t + 2)) - m * (t + 2).choose 2))
      (algebraMap K (IsotropicChartRing p (fun l i ↦ a (l, i)))) := by
  classical
  apply isotropicChartRing_locally_standardSmoothOfRelativeDimension p a
  rw [isotropicSmoothnessPolynomial, map_prod] at ha
  exact (Finset.prod_ne_zero_iff.mp ha) p (Finset.mem_univ p)

/-- The native fixed-relative-dimension property descends from the proved
original affine chart cover to the genuine common-isotropic Proj scheme. -/
theorem isotropicStructureMap_smoothOfRelativeDimension (t n m : ℕ)
    (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K := K) t n m) ≠ 0) :
    SmoothOfRelativeDimension
      ((t + 2) * (n - (t + 2)) - m * (t + 2).choose 2)
      (isotropicStructureMap (t := t) (fun l i ↦ a (l, i))) := by
  let d := (t + 2) * (n - (t + 2)) - m * (t + 2).choose 2
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P:=@AlgebraicGeometry.SmoothOfRelativeDimension.{0} d)
    (fun p : PluckerIndex (t + 2) n ↦
      Proj.basicOpen (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))
        (Ideal.Quotient.mk (isotropicPluckerIdeal (fun l i ↦ a (l, i))) (X p)))
    (isotropicProjBasicOpen_cover (t := t) (fun l i ↦ a (l, i)))
  intro p
  rw [← isotropicProjBasicOpenIso_hom_over]
  letI : SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom
      (algebraMap K (IsotropicChartRing p (fun l i ↦ a (l, i)))))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr
      (isotropic_all_charts_relativeDimension t n m a ha p)
  have h : SmoothOfRelativeDimension (0 + d)
      ((isotropicProjBasicOpenIso p (fun l i ↦ a (l, i))).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (IsotropicChartRing p (fun l i ↦ a (l, i)))))) := inferInstance
  simpa only [Nat.zero_add] using h

/-- The presentation dimension in the pair case is precisely the paper's
`D = s*(n+1-2*s)` throughout its full nonempty parameter range. -/
theorem pair_expected_dimension (t n : ℕ) (hs : 2 * (t + 2) ≤ n + 1) :
    (t + 2) * (n - (t + 2)) - 2 * (t + 2).choose 2 =
      (t + 2) * (n + 1 - 2 * (t + 2)) := by
  have hchoose := two_mul_choose_two_add (t + 2)
  have h₁ : n - (t + 2) + (t + 2) = n := by omega
  have h₂ : n + 1 - 2 * (t + 2) + 2 * (t + 2) = n + 1 := by omega
  have hnum : (t + 2) * (n - (t + 2)) =
      (t + 2) * (n + 1 - 2 * (t + 2)) + 2 * (t + 2).choose 2 := by nlinarith
  rw [hnum, Nat.add_sub_cancel]

/-- The complete nonempty generic-smooth locus for pairs, with the actual
expected smooth relative dimension and the original coefficient parameter space. -/
theorem generic_pair_commonIsotropic_smooth_nonempty (t n : ℕ)
    (hs : 2 * (t + 2) ≤ n + 1) :
    ∃ Q : MvPolynomial (Fin 2 × StrictPairs n) K, Q ≠ 0 ∧
      (∃ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0) ∧
      ∀ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0 →
        Nonempty (Proj (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))) ∧
        SmoothOfRelativeDimension ((t + 2) * (n + 1 - 2 * (t + 2)))
          (isotropicStructureMap (t := t) (fun l i ↦ a (l, i))) := by
  refine ⟨isotropicSmoothnessPolynomial (K := K) t n 2,
    isotropicSmoothnessPolynomial_ne_zero (K := K) t n 2, ?_, ?_⟩
  · obtain ⟨a, ha, _⟩ := exists_isotropic_all_charts_smooth (K := K) t n 2
    exact ⟨a, ha⟩
  · intro a ha
    refine ⟨commonIsotropicProj_nonempty_of_dimension _ hs, ?_⟩
    rw [← pair_expected_dimension t n hs]
    exact isotropicStructureMap_smoothOfRelativeDimension t n 2 a ha

/-- The complementary range in the paper has empty general zero scheme,
including cases with no Grassmannian charts at all. -/
theorem generic_pair_commonIsotropic_empty (t n : ℕ)
    (hs : n + 1 < 2 * (t + 2)) :
    ∃ Q : MvPolynomial (Fin 2 × StrictPairs n) K, Q ≠ 0 ∧
      (∃ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0) ∧
      ∀ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0 →
        IsEmpty (Proj (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))) := by
  apply generic_commonIsotropic_empty_of_negative_dimension t n 2
  have hchoose := two_mul_choose_two_add (t + 2)
  have hnum : 2 * (t + 2).choose 2 = (t + 2) * (t + 1) := by nlinarith
  rw [hnum]
  exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)

end PaperVerification.AlternatingForms
