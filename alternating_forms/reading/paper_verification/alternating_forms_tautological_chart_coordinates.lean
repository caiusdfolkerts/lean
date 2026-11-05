module

public import PaperVerification.AlternatingFormsTautologicalIncidence
public import PaperVerification.TwistingChartFractions

/-!
# The actual coordinate functions on a tautological chart

The affine chart ring maps to sections of the structure sheaf through the
degree-zero homogeneous localization. The formulas below retain this map:
normalizing a homogeneous Plücker polynomial is the same operation as dividing
its twisting-sheaf section by the chart's distinguished degree-one section.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory MvPolynomial Opposite
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

abbrev tautologicalChartOpen (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :=
  Proj.basicOpen (isotropicProjectiveGrading (t:=t) forms)
    (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))

/-- The chart ring's genuine section homomorphism, rather than a chosen
identification of points. -/
def tautologicalChartSectionHom (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    IsotropicChartRing p forms →+*
      Γ(Proj (isotropicProjectiveGrading (t:=t) forms), tautologicalChartOpen p forms) :=
  (Proj.awayToSection (isotropicProjectiveGrading (t:=t) forms)
    (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))).hom.comp
      (isotropicProjChartRingEquiv_arbitraryChar p forms).symm.toRingHom

/-- The normalized homogeneous fraction evaluates in the original row chart
by its actual maximal minors. -/
theorem isotropicProjChartRingEquiv_arbitraryChar_fraction (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) {d : ℕ}
    (f : MvPolynomial (PluckerIndex (t+2) n) K) (hf : f.IsHomogeneous d) :
    isotropicProjChartRingEquiv_arbitraryChar p forms
      (HomogeneousChartDehomogenization.fraction
        (isotropicProjectiveGrading (t:=t) forms)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (homogeneousPluckerClass forms f hf)) =
      isotropicChartEvaluation p forms f := by
  rw [isotropicProjChartRingEquiv_arbitraryChar, RingEquiv.trans_apply,
    HomogeneousQuotientCharts.awayQuotientChartEquiv, RingEquiv.trans_apply]
  erw [HomogeneousChartDehomogenization.awayEquivNormalized_fraction]
  change isotropicPluckerBigCellEquiv_arbitraryChar p forms
    (HomogeneousQuotientCharts.normalizedQuotientEquiv _ p
      (HomogeneousChartDehomogenization.quotientMap _
        (Ideal.Quotient.mk _ f))) = _
  rw [HomogeneousQuotientCharts.normalizedQuotientEquiv_class]
  have h₁ := Ideal.quotientEquivAlgOfEq_mk K
    (isotropicChartEvaluation_kernel_arbitraryChar p forms).symm f
  have h₂ := Ideal.quotientKerAlgEquivOfSurjective_mk
    (f := isotropicChartEvaluation p forms)
    (isotropicChartEvaluation_surjective p forms) f
  exact (congrArg (Ideal.quotientKerAlgEquivOfSurjective
    (f := isotropicChartEvaluation p forms)
    (isotropicChartEvaluation_surjective p forms)) h₁).trans h₂

/-- The concrete section associated with a normalized homogeneous polynomial. -/
theorem tautologicalChartSectionHom_homogeneous
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    {d : ℕ} (f : MvPolynomial (PluckerIndex (t+2) n) K)
    (hf : f.IsHomogeneous d) :
    tautologicalChartSectionHom p forms (isotropicChartEvaluation p forms f) =
      Proj.awayToSection (isotropicProjectiveGrading (t:=t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))
        (HomogeneousChartDehomogenization.fraction
          (isotropicProjectiveGrading (t:=t) forms)
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
          (homogeneousPluckerClass forms f hf)) := by
  rw [← isotropicProjChartRingEquiv_arbitraryChar_fraction p forms f hf]
  simp only [tautologicalChartSectionHom, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]

/-- The genuine Plücker line bundle's canonical frame on the pivot chart. -/
def tautologicalChartLineEquiv (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    Γ(Proj (isotropicProjectiveGrading (t:=t) forms), tautologicalChartOpen p forms) ≃ₗ[
      Γ(Proj (isotropicProjectiveGrading (t:=t) forms), tautologicalChartOpen p forms)]
      Γ(tautologicalLine (t:=t) forms, tautologicalChartOpen p forms) :=
  Proj.twistingSheaf.chartSectionsLinearEquiv
    (𝒜:=isotropicProjectiveGrading (t:=t) forms) 1
    (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
    (tautologicalChartOpen p forms) le_rfl

/-- In the actual twisting-sheaf trivialization, the normalized row-chart
function is exactly the original homogeneous Plücker section. -/
theorem tautologicalChart_frame_homogeneous
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (f : MvPolynomial (PluckerIndex (t+2) n) K)
    (hf : f.IsHomogeneous 1) :
    Proj.twistingSheaf.chartSectionsLinearEquiv
      (𝒜:=isotropicProjectiveGrading (t:=t) forms) 1
      (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
      (tautologicalChartOpen p forms) le_rfl
      (tautologicalChartSectionHom p forms (isotropicChartEvaluation p forms f)) =
      Proj.toTwistingSheaf (isotropicProjectiveGrading (t:=t) forms) rfl
        (tautologicalChartOpen p forms) (homogeneousPluckerClass forms f hf) := by
  rw [tautologicalChartSectionHom_homogeneous p forms f hf]
  exact TwistingChartFractions.chart_frame_fraction
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
    (homogeneousPluckerClass forms f hf)

/-- The affine coordinate polynomial ring maps into the actual chart sections. -/
def tautologicalChartPolynomialHom (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    MvPolynomial (PluckerChartVariable p) K →+*
      Γ(Proj (isotropicProjectiveGrading (t:=t) forms), tautologicalChartOpen p forms) :=
  (tautologicalChartSectionHom p forms).comp
    (Ideal.Quotient.mk (isotropicChartIdeal p forms))

/-- The normalized row matrix now has coefficients in the genuine structure
sheaf on its standard open. -/
def tautologicalChartMatrix (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :=
  (pluckerChartMatrix (K:=K) p).map (tautologicalChartPolynomialHom p forms)

theorem tautologicalChartMatrix_pivot (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    (tautologicalChartMatrix p forms).submatrix id p.val = 1 := by
  exact NormalizedTautologicalKernel.pivot_map
    (tautologicalChartPolynomialHom p forms) (pluckerChartMatrix p) p.val
    (pluckerChartMatrix_pivot p)

theorem tautologicalChart_incidence_coordinates
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (v : Fin n → Γ(Proj (isotropicProjectiveGrading (t:=t) forms),
      tautologicalChartOpen p forms)) (J : Fin ((t+2)+1) → Fin n) :
    (∑ i : Fin n, v i * tautologicalChartSectionHom p forms
      (isotropicChartEvaluation p forms (tautologicalIncidenceCoefficient J i))) =
      NormalizedTautologicalKernel.incidence (tautologicalChartMatrix p forms) v J :=
  tautologicalIncidenceCoefficient_evaluation_map
    (tautologicalChartPolynomialHom p forms) (pluckerChartMatrix p) v J

/-- On the chart, the actual global incidence morphism is exactly the
augmented-minor map in the canonical line-bundle frame. -/
theorem tautologicalIncidenceComponent_chart
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (J : Fin ((t+2)+1) → Fin n)
    (x : (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin n)).val.obj
        (op (tautologicalChartOpen p forms))) :
    (tautologicalIncidenceComponent (t:=t) forms J).val.app
      (op (tautologicalChartOpen p forms)) x =
      tautologicalChartLineEquiv p forms
        (NormalizedTautologicalKernel.incidence (tautologicalChartMatrix p forms)
          (SheafModulePowers.sectionsEquiv
            (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
            (Fin n) (tautologicalChartOpen p forms) x) J) := by
  classical
  refine (SheafCoordinateMorphisms.fromSections_apply
    (tautologicalLine (t := t) forms)
    (fun i : Fin n => tautologicalCoordinateSection forms
      (tautologicalIncidenceCoefficient (K := K) J i)
      (tautologicalIncidenceCoefficient_isHomogeneous (K := K) J i))
    (tautologicalChartOpen p forms) x).trans ?_
  simp only [tautologicalCoordinateSection_eval]
  let v : Fin n → Γ(Proj (isotropicProjectiveGrading (t := t) forms), (tautologicalChartOpen p forms)) :=
    SheafModulePowers.sectionsEquiv
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin n) (tautologicalChartOpen p forms) x
  let a : Fin n → Γ(Proj (isotropicProjectiveGrading (t := t) forms), (tautologicalChartOpen p forms)) :=
    fun i => tautologicalChartSectionHom p forms
      (isotropicChartEvaluation p forms (tautologicalIncidenceCoefficient (K := K) J i))
  let z : Fin n → Γ(tautologicalLine (t := t) forms, (tautologicalChartOpen p forms)) := fun i =>
    Proj.toTwistingSheaf (isotropicProjectiveGrading (t := t) forms) rfl (tautologicalChartOpen p forms)
      (homogeneousPluckerClass forms (tautologicalIncidenceCoefficient (K := K) J i)
        (tautologicalIncidenceCoefficient_isHomogeneous (K := K) J i))
  have hframe (i : Fin n) : (tautologicalChartLineEquiv p forms) (a i) = z i :=
    tautologicalChart_frame_homogeneous p forms (tautologicalIncidenceCoefficient (K := K) J i)
      (tautologicalIncidenceCoefficient_isHomogeneous (K := K) J i)
  exact (SheafCoordinateMorphisms.sum_smul_eq_frame
    (R := Γ(Proj (isotropicProjectiveGrading (t := t) forms), (tautologicalChartOpen p forms)))
    (M := Γ(tautologicalLine (t := t) forms, (tautologicalChartOpen p forms)))
    (tautologicalChartLineEquiv p forms) v a z hframe).trans
      (congrArg (tautologicalChartLineEquiv p forms) (tautologicalChart_incidence_coordinates p forms v J))

/-- The kernel condition on actual sheaf sections is precisely the original
augmented-determinant condition over the chart's structure ring. -/
theorem tautologicalIncidenceMap_chart_zero_iff
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (x : (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin n)).val.obj
        (op (tautologicalChartOpen p forms))) :
    (tautologicalIncidenceMap (t:=t) forms).val.app
      (op (tautologicalChartOpen p forms)) x=0 ↔
      ∀ J, NormalizedTautologicalKernel.incidence (tautologicalChartMatrix p forms)
        (SheafModulePowers.sectionsEquiv
          (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
          (Fin n) (tautologicalChartOpen p forms) x) J=0 := by
  rw [SheafModulePowers.section_eq_zero_iff
    (tautologicalLine (t:=t) forms) (Fin ((t+2)+1) → Fin n)
    (tautologicalChartOpen p forms)]
  apply forall_congr'
  intro J
  have hc := (tautologicalIncidenceMap_component_apply (t := t) forms J
    (tautologicalChartOpen p forms) x).trans (tautologicalIncidenceComponent_chart p forms J x)
  constructor
  · intro h
    apply (tautologicalChartLineEquiv p forms).injective
    exact hc.symm.trans (h.trans (map_zero (tautologicalChartLineEquiv p forms)).symm)
  · intro h
    exact hc.trans ((congrArg (tautologicalChartLineEquiv p forms) h).trans
      (map_zero (tautologicalChartLineEquiv p forms)))

end PaperVerification.AlternatingForms
