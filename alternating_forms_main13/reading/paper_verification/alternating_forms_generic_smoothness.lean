module

public import PaperVerification.AlternatingFormsGenericChartSmoothness
public import PaperVerification.AlternatingFormsProjOver
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Generic smoothness of the actual common-isotropic projective scheme

The affine chart theorem is transported along the original chart isomorphisms,
which commute with the canonical map to `Spec K`. Smoothness is then descended
along their proved open cover. The parameter polynomial belongs to the full
coefficient space of all alternating forms.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K]

/-- A nonzero polynomial in all form coefficients ensures that the genuine
common-isotropic scheme is smooth over its original coefficient field. -/
theorem isotropicStructureMap_smooth (t n m : ℕ)
    (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K:=K) t n m) ≠ 0) :
    Smooth (isotropicStructureMap (t:=t) (fun l i => a (l,i))) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P:=@AlgebraicGeometry.Smooth.{0})
    (fun p : PluckerIndex (t+2) n =>
      Proj.basicOpen (isotropicProjectiveGrading (t:=t) (fun l i => a (l,i)))
        (Ideal.Quotient.mk (isotropicPluckerIdeal (fun l i => a (l,i))) (X p)))
    (isotropicProjBasicOpen_cover (t:=t) (fun l i => a (l,i)))
  intro p
  rw [← isotropicProjBasicOpenIso_hom_over]
  letI : Algebra.Smooth K (IsotropicChartRing p (fun l i => a (l,i))) :=
    isotropic_all_charts_smooth t n m a ha p
  haveI : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap K (IsotropicChartRing p (fun l i => a (l,i)))))) :=
    (HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  infer_instance

/-- The complete principal-open statement for any number of alternating
forms and any plane dimension at least two. Smoothness allows an empty zero
scheme; nonemptiness and expected dimension are separate conclusions. -/
theorem generic_commonIsotropic_smooth (t n m : ℕ) :
    ∃ Q : MvPolynomial (Fin m × StrictPairs n) K, Q ≠ 0 ∧
      (∃ a : (Fin m × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0) ∧
      ∀ a : (Fin m × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0 →
        Smooth (isotropicStructureMap (t:=t) (fun l i => a (l,i))) := by
  refine ⟨isotropicSmoothnessPolynomial (K:=K) t n m,
    isotropicSmoothnessPolynomial_ne_zero (K:=K) t n m, ?_, ?_⟩
  · obtain ⟨a,ha,_⟩ := exists_isotropic_all_charts_smooth (K:=K) t n m
    exact ⟨a,ha⟩
  · exact isotropicStructureMap_smooth t n m

end PaperVerification.AlternatingForms
