module

public import PaperVerification.AlternatingFormsGenericChartSmoothness
public import PaperVerification.GenericVectorSectionEmptiness
public import PaperVerification.AlternatingFormsProjAtlas

/-!
# Generic emptiness in negative expected dimension

For any number of alternating forms, the expected dimension is the number
of Grassmannian chart variables minus the number of row-isotropy equations.
If it is negative, the generic section has the unit ideal on every chart.
The genuine projective common-isotropic scheme is consequently empty.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open AlgebraicGeometry MvPolynomial

namespace PaperVerification.AlternatingForms

open GenericSectionDifferentials

variable {K : Type*} [Field K] [CharZero K] {t n m : ℕ}

private lemma chart_variable_count (p : PluckerIndex (t+2) n) :
    Fintype.card (PluckerChartVariable p) = (t+2)*(n-(t+2)) := by
  classical
  have h : Fintype.card (Set.range p.val)=t+2 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_congr (Equiv.ofInjective p.val p.property.injective)).symm
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_subtype_compl,Fintype.card_fin,h]

/-- The original chart ideal is the unit ideal, without passing to its radical. -/
theorem isotropicChartIdeal_eq_top_of_negative_dimension
    (p : PluckerIndex (t+2) n) (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicChartSmoothnessPolynomial (K:=K) (m:=m) p) ≠ 0)
    (hd : (t+2)*(n-(t+2)) < m*(t+2).choose 2) :
    isotropicChartIdeal p (fun l i => a (l,i)) = ⊤ := by
  classical
  have hc : Fintype.card (PluckerChartVariable p) <
      Fintype.card (Fin m × StrictPairs (t+2)) := by
    rw [chart_variable_count, Fintype.card_prod, Fintype.card_fin, card_strictPairs]
    exact hd
  have h := linearSection_ideal_eq_top_of_more_equations
    (KaehlerDifferential.mvPolynomialBasis K (PluckerChartVariable p))
    (chartSectionEvaluation (K:=K) (m:=m) p) (chartSectionExtension (K:=K) (m:=m) p)
    (chartSectionEvaluation_rightInverse (K:=K) (m:=m) p) a ha hc
  have hf : linearSection (chartSectionEvaluation (K:=K) (m:=m) p) a =
      fun j : Fin m × StrictPairs (t+2) =>
        alternatingRowPair (fun i => a (j.1,i)) (pluckerChartMatrix (K:=K) p)
          j.2.val.1 j.2.val.2 := by
    funext j
    exact chartSectionEvaluation_sum p a j
  rw [hf] at h
  exact h

/-- Empty original affine charts force the actual homogeneous-quotient Proj
to be empty by its established basic-open cover. -/
theorem isotropicProj_isEmpty_of_chartIdeals_eq_top
    (forms : Fin m → StrictPairs n → K)
    (h : ∀ p : PluckerIndex (t+2) n, isotropicChartIdeal p forms=⊤) :
    IsEmpty (Proj (isotropicProjectiveGrading (t:=t) forms)) := by
  classical
  constructor
  intro x
  have hx : x ∈ (⨆ p : PluckerIndex (t+2) n,
      Proj.basicOpen (isotropicProjectiveGrading (t:=t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))) := by
    rw [isotropicProjBasicOpen_cover]
    trivial
  obtain ⟨p,hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  letI : Subsingleton (IsotropicChartRing p forms) :=
    Ideal.Quotient.subsingleton_iff.mpr (h p)
  let x' : PrimeSpectrum (IsotropicChartRing p forms) :=
    (isotropicProjBasicOpenIso p forms).hom ⟨x,hp⟩
  exact isEmptyElim x'

/-- A single nonempty principal open in the complete coefficient space has
empty common-isotropic scheme whenever its expected dimension is negative. -/
theorem generic_commonIsotropic_empty_of_negative_dimension (t n m : ℕ)
    (hd : (t+2)*(n-(t+2)) < m*(t+2).choose 2) :
    ∃ Q : MvPolynomial (Fin m × StrictPairs n) K, Q≠0 ∧
      (∃ a : (Fin m × StrictPairs n) → K, MvPolynomial.aeval a Q≠0) ∧
      ∀ a : (Fin m × StrictPairs n) → K, MvPolynomial.aeval a Q≠0 →
        IsEmpty (Proj (isotropicProjectiveGrading (t:=t) (fun l i => a (l,i)))) := by
  classical
  refine ⟨isotropicSmoothnessPolynomial (K:=K) t n m,
    isotropicSmoothnessPolynomial_ne_zero (K:=K) t n m, ?_, ?_⟩
  · obtain ⟨a,ha,_⟩ := exists_isotropic_all_charts_smooth (K:=K) t n m
    exact ⟨a,ha⟩
  · intro a ha
    apply isotropicProj_isEmpty_of_chartIdeals_eq_top
    intro p
    apply isotropicChartIdeal_eq_top_of_negative_dimension p a _ hd
    rw [isotropicSmoothnessPolynomial,map_prod] at ha
    exact (Finset.prod_ne_zero_iff.mp ha) p (Finset.mem_univ p)

end PaperVerification.AlternatingForms
