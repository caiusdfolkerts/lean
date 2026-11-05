module

public import paper_verification.ambient_zero6
import all paper_verification.ambient_zero6
public import paper_verification.ambient_generic1
import all paper_verification.ambient_generic1
public import paper_verification.literal005
import all paper_verification.literal005
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.AlternatingFormsTautologicalIncidence -/


/-!
# The universal tautological incidence map

The source is the genuine free structure sheaf on the ambient coordinate
vectors. Its target is a finite product of the genuine Plücker twisting sheaf.
The matrix entries are the signed Plücker coordinates in the exterior-product
formula. Its kernel is defined before any rank or cohomology assertion.

Evaluation on a normalized chart gives the actual augmented determinants;
the preceding integral matrix theorem identifies their common kernel with the
span of the normalized rows, over arbitrary coefficient algebras.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped BigOperators
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {s t n m : ℕ}

/-- The coefficient of the ambient vector coordinate `i` in the exterior
incidence equation indexed by the ordered column word `J`. -/
def tautologicalIncidenceCoefficient (J : Fin (s+1) → Fin n) (i : Fin n) :
    MvPolynomial (PluckerIndex s n) K :=
  ∑ q : Fin (s+1), if J q=i then
    ((-1 : K)^q.val) • orderedPluckerCoordinate (fun z => J (q.succAbove z))
  else 0

theorem tautologicalIncidenceCoefficient_isHomogeneous
    (J : Fin (s+1) → Fin n) (i : Fin n) :
    (tautologicalIncidenceCoefficient (K:=K) J i).IsHomogeneous 1 := by
  classical
  unfold tautologicalIncidenceCoefficient
  apply MvPolynomial.IsHomogeneous.sum
  intro q hq
  split_ifs
  · exact (MvPolynomial.homogeneousSubmodule (PluckerIndex s n) K 1).smul_mem _
      (orderedPluckerCoordinate_isHomogeneous _)
  · exact MvPolynomial.isHomogeneous_zero _ K _

/-- The coefficient expression is literally the determinant with the tested
vector adjoined to the row matrix, by Laplace expansion. -/
theorem tautologicalIncidenceCoefficient_evaluation
    {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) (v : Fin n → R)
    (J : Fin (s+1) → Fin n) :
    (∑ i : Fin n, v i * matrixMinorEvaluation A
      (tautologicalIncidenceCoefficient (K:=K) J i)) =
      NormalizedTautologicalKernel.incidence A v J := by
  classical
  simp only [tautologicalIncidenceCoefficient,map_sum,apply_ite,map_smul,map_zero,
    matrixMinorEvaluation_orderedCoordinate,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true,Algebra.smul_def]
  rw [NormalizedTautologicalKernel.incidence_eq_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [map_pow, map_neg, map_one, Matrix.submatrix, id_eq]
  ring

/-- The same determinant identity after an arbitrary ring homomorphism. This
form does not choose an additional coefficient-field action on the target. -/
theorem tautologicalIncidenceCoefficient_evaluation_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra K R]
    (φ : R →+* S) (A : Matrix (Fin s) (Fin n) R)
    (v : Fin n → S) (J : Fin (s+1) → Fin n) :
    (∑ i : Fin n, v i * φ (matrixMinorEvaluation A
      (tautologicalIncidenceCoefficient (K:=K) J i))) =
      NormalizedTautologicalKernel.incidence (A.map φ) v J := by
  classical
  simp only [tautologicalIncidenceCoefficient, map_sum, apply_ite, map_smul,
    map_zero, matrixMinorEvaluation_orderedCoordinate, Algebra.smul_def,
    map_mul, map_pow, map_neg, map_one, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [NormalizedTautologicalKernel.incidence_eq_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [RingHom.map_det]
  change v (J q) * ((-1 : S)^q.val *
    Matrix.det ((A.map φ).submatrix id (fun z => J (q.succAbove z)))) =
      (-1 : S)^q.val * v (J q) *
        Matrix.det ((A.map φ).submatrix id (fun z => J (q.succAbove z)))
  ring

abbrev tautologicalLine (forms : Fin m → StrictPairs n → K) :=
  Proj.twistingSheaf (isotropicProjectiveGrading (t:=t) forms) (1 : ℤ)

/-- A homogeneous class, with its membership proof in the literal quotient
grading. -/
def homogeneousPluckerClass (forms : Fin m → StrictPairs n → K)
    {d : ℕ} (f : MvPolynomial (PluckerIndex (t+2) n) K)
    (hf : f.IsHomogeneous d) : isotropicProjectiveGrading (t:=t) forms d :=
  ⟨Ideal.Quotient.mk (isotropicPluckerIdeal forms) f, by
    change Ideal.Quotient.mk (isotropicPluckerIdeal forms) f ∈
      HomogeneousQuotientProjective.grading _ _ d
    rw [HomogeneousQuotientProjective.grading_eq_piece]
    exact ⟨f,hf,rfl⟩⟩

/-- The actual compatible family of twisting-sheaf sections associated to a
homogeneous coordinate linear form. -/
def tautologicalCoordinateSection (forms : Fin m → StrictPairs n → K)
    (f : MvPolynomial (PluckerIndex (t+2) n) K) (hf : f.IsHomogeneous 1) :
    (tautologicalLine (t:=t) forms).sections := by
  let r : isotropicProjectiveGrading (t:=t) forms 1 :=
    homogeneousPluckerClass forms f hf
  exact PresheafOfModules.sectionsMk
    (fun U => Proj.toTwistingSheaf
      (isotropicProjectiveGrading (t:=t) forms) rfl U.unop r)
    (by intro U V i; rfl)

@[simp] theorem tautologicalCoordinateSection_value
    (forms : Fin m → StrictPairs n → K)
    (f : MvPolynomial (PluckerIndex (t+2) n) K) (hf : f.IsHomogeneous 1)
    (U : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens) :
    (tautologicalCoordinateSection forms f hf).val (op U) =
      Proj.toTwistingSheaf (isotropicProjectiveGrading (t:=t) forms) rfl U
        (homogeneousPluckerClass forms f hf) := rfl

@[simp] theorem tautologicalCoordinateSection_eval
    (forms : Fin m → StrictPairs n → K)
    (f : MvPolynomial (PluckerIndex (t+2) n) K) (hf : f.IsHomogeneous 1)
    (U : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens) :
    (tautologicalCoordinateSection forms f hf).eval (op U) =
      Proj.toTwistingSheaf (isotropicProjectiveGrading (t:=t) forms) rfl U
        (homogeneousPluckerClass forms f hf) := rfl

/-- One component of the universal exterior incidence morphism. -/
def tautologicalIncidenceComponent (forms : Fin m → StrictPairs n → K)
    (J : Fin ((t+2)+1) → Fin n) :
    SheafModulePowers.structurePower (Proj
      (isotropicProjectiveGrading (t:=t) forms)) (Fin n) ⟶
        tautologicalLine (t:=t) forms :=
  SheafCoordinateMorphisms.fromSections _
    (fun i : Fin n => tautologicalCoordinateSection forms
      (tautologicalIncidenceCoefficient J i)
      (tautologicalIncidenceCoefficient_isHomogeneous J i))

/-- The global map uses actual free and twisting sheaves; it is independent
of the subsequent chart-rank calculation. -/
def tautologicalIncidenceMap (forms : Fin m → StrictPairs n → K) :
    SheafModulePowers.structurePower (Proj
      (isotropicProjectiveGrading (t:=t) forms)) (Fin n) ⟶
      ∏ᶜ (fun _ : Fin ((t+2)+1) → Fin n => tautologicalLine (t:=t) forms) :=
  Pi.lift (tautologicalIncidenceComponent forms)

@[simp] theorem tautologicalIncidenceMap_component
    (forms : Fin m → StrictPairs n → K) (J : Fin ((t+2)+1) → Fin n) :
    tautologicalIncidenceMap (t:=t) forms ≫
      Pi.π (fun _ : Fin ((t+2)+1) → Fin n => tautologicalLine (t:=t) forms) J =
        tautologicalIncidenceComponent (t:=t) forms J :=
  Pi.lift_comp_π _ _

@[simp] theorem tautologicalIncidenceMap_component_apply
    (forms : Fin m → StrictPairs n → K) (J : Fin ((t+2)+1) → Fin n)
    (U : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (x : (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin n)).val.obj (op U)) :
    (Pi.π (fun _ : Fin ((t+2)+1) → Fin n => tautologicalLine (t:=t) forms) J).val.app
      (op U) ((tautologicalIncidenceMap (t:=t) forms).val.app (op U) x) =
        (tautologicalIncidenceComponent (t:=t) forms J).val.app (op U) x := by
  exact congrArg (fun f => f.val.app (op U) x)
    (tautologicalIncidenceMap_component (t:=t) forms J)

/-- The canonical submodule sheaf cut out by universal Plücker incidence. -/
def tautologicalKernel (forms : Fin m → StrictPairs n → K) :
    (Proj (isotropicProjectiveGrading (t:=t) forms)).Modules :=
  kernel (tautologicalIncidenceMap (t:=t) forms)

/-- Its inclusion is the actual categorical kernel inclusion. -/
def tautologicalKernelInclusion (forms : Fin m → StrictPairs n → K) :
    tautologicalKernel (t:=t) forms ⟶
      SheafModulePowers.structurePower (Proj
        (isotropicProjectiveGrading (t:=t) forms)) (Fin n) :=
  kernel.ι (tautologicalIncidenceMap (t:=t) forms)

theorem tautologicalKernel_incidence (forms : Fin m → StrictPairs n → K) :
    tautologicalKernelInclusion (t:=t) forms ≫
      tautologicalIncidenceMap (t:=t) forms=0 :=
  kernel.condition _

/-- Projection of the actual kernel inclusion onto the selected pivot
coordinates. This is a global sheaf morphism; its restriction to the pivot
chart is the local frame coordinate map. -/
def tautologicalPivotMap (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    tautologicalKernel (t:=t) forms ⟶
      SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin (t+2)) :=
  tautologicalKernelInclusion (t := t) forms ≫
    SheafModulePowers.reindex
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin n) (Fin (t + 2)) p.val

/-- The pivot map is the original coordinate projection after the genuine
kernel inclusion. -/
theorem tautologicalPivotMap_projection
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (i : Fin (t+2)) :
    tautologicalPivotMap p forms ≫
      Pi.π (fun _ : Fin (t+2) => SheafOfModules.unit (Proj
        (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf) i =
      tautologicalKernelInclusion (t:=t) forms ≫
        Pi.π (fun _ : Fin n => SheafOfModules.unit (Proj
          (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf) (p.val i) := by
  unfold tautologicalPivotMap
  exact (CategoryTheory.Category.assoc _ _ _).trans
    (congrArg
      (fun g : SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t := t) forms)) (Fin n) ⟶
          SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf ↦
        tautologicalKernelInclusion (t := t) forms ≫ g)
      (SheafModulePowers.reindex_projection
        (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
        (Fin n) (Fin (t + 2)) p.val i))

end PaperVerification.AlternatingForms
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsTautologicalIncidence"

section ComponentSource_1
/- Original module: PaperVerification.AlternatingFormsTautologicalChartCoordinates -/


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
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsTautologicalChartCoordinates"

section ComponentSource_2
/- Original module: PaperVerification.AlternatingFormsTautologicalLocalFrames -/


/-!
# Local frames on every subopen of a Plücker chart

The coefficient maps are restrictions of the actual affine-chart functions.
The chart calculation consequently applies to every subopen, as required for
an isomorphism of sheaves rather than only their global section modules.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

def tautologicalLocalSectionHom (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    IsotropicChartRing p forms →+* Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V) :=
  ((Proj (isotropicProjectiveGrading (t:=t) forms)).presheaf.map
    (homOfLE hV).op).hom.comp (tautologicalChartSectionHom p forms)

def tautologicalLocalPolynomialHom (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    MvPolynomial (PluckerChartVariable p) K →+*
      Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V) :=
  (tautologicalLocalSectionHom p forms V hV).comp
    (Ideal.Quotient.mk (isotropicChartIdeal p forms))

def tautologicalLocalMatrix (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :=
  (pluckerChartMatrix (K:=K) p).map (tautologicalLocalPolynomialHom p forms V hV)

theorem tautologicalLocalMatrix_pivot (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    (tautologicalLocalMatrix p forms V hV).submatrix id p.val=1 :=
  NormalizedTautologicalKernel.pivot_map _ _ _ (pluckerChartMatrix_pivot (K:=K) p)

def tautologicalLocalLineEquiv (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V) ≃ₗ[
      Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V)]
      Γ(tautologicalLine (t:=t) forms,V) :=
  Proj.twistingSheaf.chartSectionsLinearEquiv
    (𝒜:=isotropicProjectiveGrading (t:=t) forms) 1
    (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) V hV

theorem tautologicalLocal_frame_homogeneous
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms)
    (f : MvPolynomial (PluckerIndex (t+2) n) K) (hf : f.IsHomogeneous 1) :
    tautologicalLocalLineEquiv p forms V hV
      (tautologicalLocalSectionHom p forms V hV (isotropicChartEvaluation p forms f)) =
      Proj.toTwistingSheaf (isotropicProjectiveGrading (t:=t) forms) rfl V
        (homogeneousPluckerClass forms f hf) := by
  let i : V ⟶ tautologicalChartOpen p forms := homOfLE hV
  have hnat := Proj.twistingSheaf.res_chartSectionsLinearEquiv
    (𝒜 := isotropicProjectiveGrading (t := t) forms) 1
    (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
    (tautologicalChartOpen p forms) le_rfl i
    (tautologicalChartSectionHom p forms (isotropicChartEvaluation p forms f))
  calc
    tautologicalLocalLineEquiv p forms V hV
        (tautologicalLocalSectionHom p forms V hV (isotropicChartEvaluation p forms f)) =
      (tautologicalLine (t := t) forms).presheaf.map i.op
        (tautologicalChartLineEquiv p forms
          (tautologicalChartSectionHom p forms (isotropicChartEvaluation p forms f))) := hnat.symm
    _ = (tautologicalLine (t := t) forms).presheaf.map i.op
        (Proj.toTwistingSheaf (isotropicProjectiveGrading (t := t) forms) rfl
          (tautologicalChartOpen p forms) (homogeneousPluckerClass forms f hf)) :=
      congrArg (fun z => (tautologicalLine (t := t) forms).presheaf.map i.op z)
        (tautologicalChart_frame_homogeneous p forms f hf)
    _ = Proj.toTwistingSheaf (isotropicProjectiveGrading (t := t) forms) rfl V
        (homogeneousPluckerClass forms f hf) := rfl

theorem tautologicalLocal_incidence_coordinates
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms)
    (v : Fin n → Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V))
    (J : Fin ((t+2)+1) → Fin n) :
    (∑ i : Fin n, v i * tautologicalLocalSectionHom p forms V hV
      (isotropicChartEvaluation p forms (tautologicalIncidenceCoefficient J i))) =
      NormalizedTautologicalKernel.incidence (tautologicalLocalMatrix p forms V hV) v J :=
  tautologicalIncidenceCoefficient_evaluation_map
    (tautologicalLocalPolynomialHom p forms V hV) (pluckerChartMatrix p) v J

theorem tautologicalIncidenceComponent_local
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms)
    (J : Fin ((t+2)+1) → Fin n)
    (x : (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin n)).val.obj (op V)) :
    (tautologicalIncidenceComponent (t:=t) forms J).val.app (op V) x =
      tautologicalLocalLineEquiv p forms V hV
        (NormalizedTautologicalKernel.incidence (tautologicalLocalMatrix p forms V hV)
          (SheafModulePowers.sectionsEquiv
            (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
            (Fin n) V x) J) := by
  classical
  refine (SheafCoordinateMorphisms.fromSections_apply
    (tautologicalLine (t := t) forms)
    (fun i : Fin n => tautologicalCoordinateSection forms
      (tautologicalIncidenceCoefficient (K := K) J i)
      (tautologicalIncidenceCoefficient_isHomogeneous (K := K) J i))
    V x).trans ?_
  simp only [tautologicalCoordinateSection_eval]
  let v : Fin n → Γ(Proj (isotropicProjectiveGrading (t := t) forms), V) :=
    SheafModulePowers.sectionsEquiv
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin n) V x
  let a : Fin n → Γ(Proj (isotropicProjectiveGrading (t := t) forms), V) :=
    fun i => tautologicalLocalSectionHom p forms V hV
      (isotropicChartEvaluation p forms (tautologicalIncidenceCoefficient (K := K) J i))
  let z : Fin n → Γ(tautologicalLine (t := t) forms, V) := fun i =>
    Proj.toTwistingSheaf (isotropicProjectiveGrading (t := t) forms) rfl V
      (homogeneousPluckerClass forms (tautologicalIncidenceCoefficient (K := K) J i)
        (tautologicalIncidenceCoefficient_isHomogeneous (K := K) J i))
  have hframe (i : Fin n) : (tautologicalLocalLineEquiv p forms V hV) (a i) = z i :=
    tautologicalLocal_frame_homogeneous p forms V hV (tautologicalIncidenceCoefficient (K := K) J i)
      (tautologicalIncidenceCoefficient_isHomogeneous (K := K) J i)
  exact (SheafCoordinateMorphisms.sum_smul_eq_frame
    (R := Γ(Proj (isotropicProjectiveGrading (t := t) forms), V))
    (M := Γ(tautologicalLine (t := t) forms, V))
    (tautologicalLocalLineEquiv p forms V hV) v a z hframe).trans
      (congrArg (tautologicalLocalLineEquiv p forms V hV) (tautologicalLocal_incidence_coordinates p forms V hV v J))

theorem tautologicalIncidenceMap_local_zero_iff
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms)
    (x : (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin n)).val.obj (op V)) :
    (tautologicalIncidenceMap (t:=t) forms).val.app (op V) x=0 ↔
      ∀ J, NormalizedTautologicalKernel.incidence (tautologicalLocalMatrix p forms V hV)
        (SheafModulePowers.sectionsEquiv
          (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
          (Fin n) V x) J=0 := by
  rw [SheafModulePowers.section_eq_zero_iff
    (tautologicalLine (t:=t) forms) (Fin ((t+2)+1) → Fin n) V]
  apply forall_congr'
  intro J
  have hc := (tautologicalIncidenceMap_component_apply (t := t) forms J
    V x).trans (tautologicalIncidenceComponent_local p forms V hV J x)
  constructor
  · intro h
    apply (tautologicalLocalLineEquiv p forms V hV).injective
    exact hc.symm.trans (h.trans (map_zero (tautologicalLocalLineEquiv p forms V hV)).symm)
  · intro h
    exact hc.trans ((congrArg (tautologicalLocalLineEquiv p forms V hV) h).trans
      (map_zero (tautologicalLocalLineEquiv p forms V hV)))

/-- On every subopen of the pivot chart, the actual pivot morphism is a
bijection on sections. Its inverse is the normalized row embedding. -/
theorem tautologicalPivotMap_bijective
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    Function.Bijective ((tautologicalPivotMap p forms).val.app (op V)) := by
  letI : CommRing ((Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf.obj.obj
      (op V)) := inferInstanceAs
    (CommRing Γ(Proj (isotropicProjectiveGrading (t:=t) forms), V))
  let eA := SheafModulePowers.sectionsEquiv
    (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
    (Fin n) V
  let eB := SheafModulePowers.sectionsEquiv
    (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
    (Fin (t+2)) V
  let eK := SheafModuleKernels.sectionsEquiv
    (tautologicalIncidenceMap (t:=t) forms) V
  let f :
      (SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t := t) forms)) (Fin n)).val.obj (op V) →ₗ[
          Γ(Proj (isotropicProjectiveGrading (t := t) forms), V)]
      (SheafModulePowers.power (tautologicalLine (t := t) forms)
        (Fin ((t + 2) + 1) → Fin n)).val.obj (op V) :=
    ((SheafOfModules.evaluation
    (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf (op V)).map
      (tautologicalIncidenceMap (t:=t) forms)).hom
  have hP := NormalizedTautologicalKernel.kernel_pivot_bijective
    (R := Γ(Proj (isotropicProjectiveGrading (t := t) forms), V))
    (M := (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t := t) forms)) (Fin n)).val.obj (op V))
    (N := (SheafModulePowers.power (tautologicalLine (t := t) forms)
      (Fin ((t + 2) + 1) → Fin n)).val.obj (op V)) f eA
    (tautologicalLocalMatrix p forms V hV) p.val
    (tautologicalLocalMatrix_pivot p forms V hV)
    (tautologicalIncidenceMap_local_zero_iff p forms V hV)
  have he (x : (tautologicalKernel (t:=t) forms).val.obj (op V)) :
      eB ((tautologicalPivotMap p forms).val.app (op V) x) =
        fun i => eA (eK x).val (p.val i) := by
    funext i
    have hB := SheafModulePowers.sectionsEquiv_apply
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin (t + 2)) V ((tautologicalPivotMap p forms).val.app (op V) x) i
    have hProjection := congrArg
      (fun g : tautologicalKernel (t := t) forms ⟶
          SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf =>
        g.val.app (op V) x)
      (tautologicalPivotMap_projection p forms i)
    have hA := SheafModulePowers.sectionsEquiv_apply
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin n) V (eK x).val (p.val i)
    have hK := congrArg
      (fun z : (SheafModulePowers.structurePower
          (Proj (isotropicProjectiveGrading (t := t) forms)) (Fin n)).val.obj (op V) =>
        (Pi.π (fun _ : Fin n => SheafOfModules.unit
          (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf) (p.val i)).val.app
            (op V) z)
      (SheafModuleKernels.sectionsEquiv_coe (tautologicalIncidenceMap (t := t) forms) V x)
    exact hB.trans (hProjection.trans (hA.trans hK).symm)
  have hb : Function.Bijective
      (fun x => eB ((tautologicalPivotMap p forms).val.app (op V) x)) := by
    have hh : (fun x => eB ((tautologicalPivotMap p forms).val.app (op V) x)) =
        (fun x => fun i => eA (eK x).val (p.val i)) := funext he
    rw [hh]
    exact hP.comp eK.bijective
  constructor
  · intro x y h
    exact hb.1 (congrArg eB h)
  · intro y
    obtain ⟨x,hx⟩ := hb.2 (eB y)
    exact ⟨x,eB.injective hx⟩

/-- The actual tautological kernel is isomorphic on the whole pivot chart to
`𝒪^s`. The comparison is induced by its actual coordinate projection. -/
def tautologicalFrameIso (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    (tautologicalKernel (t:=t) forms).over (tautologicalChartOpen p forms) ≅
      (SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin (t+2))).over
          (tautologicalChartOpen p forms) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun V => (LinearEquiv.ofBijective
        (((tautologicalPivotMap p forms).over (tautologicalChartOpen p forms)).val.app V).hom
        (tautologicalPivotMap_bijective p forms V.unop.left V.unop.hom.le)).toModuleIso)
      (fun _ _ f => ((tautologicalPivotMap p forms).over
        (tautologicalChartOpen p forms)).val.naturality f)

/-- Every standard chart carries a genuine free frame of the indicated rank. -/
theorem tautological_frame_exists (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    Nonempty ((tautologicalKernel (t:=t) forms).over (tautologicalChartOpen p forms) ≅
      (SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin (t+2))).over
          (tautologicalChartOpen p forms)) :=
  ⟨tautologicalFrameIso p forms⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsTautologicalLocalFrames"

section ComponentSource_3
/- Original module: PaperVerification.ProjConstantFraction -/


/-! # Degree-zero homogeneous fractions in actual chart sections -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open AlgebraicGeometry

namespace PaperVerification.ProjConstantFraction

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A degree-zero homogeneous element gives its literal constant fraction.
The denominator equality is proved in the actual prime-complement submonoid. -/
theorem awayToSection_fraction_zero {f : A} (hf : f ∈ 𝒜 1) (a : 𝒜 0)
    (x : Proj.basicOpen 𝒜 f) :
    ((Proj.awayToSection 𝒜 f
      (HomogeneousChartDehomogenization.fraction 𝒜 hf 0 a)).1 x).val =
        Localization.mk (a : A) 1 := by
  rw [HomogeneousChartDehomogenization.fraction, Proj.val_awayToSection_mk_apply]
  apply congrArg (Localization.mk (a : A))
  apply Subtype.ext
  exact pow_zero f

end PaperVerification.ProjConstantFraction
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjConstantFraction"

section ComponentSource_4
/- Original module: PaperVerification.AlternatingFormsAlternatingSection -/


/-!
# The original forms on the actual tautological bundle

This file restricts an arbitrary alternating form on the ambient coordinate
space to the actual incidence-kernel bundle.  Its scalar coefficients are
the genuine constant functions on the projective scheme, obtained from
degree-zero homogeneous sections.  In particular, the construction does
not assume that the form vanishes on the common-isotropic scheme.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

local instance (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens) :
    CommRing ((Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf.obj.obj
      (op U)) :=
  inferInstanceAs (CommRing Γ(Proj (isotropicProjectiveGrading (t := t) forms), U))

local instance (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens) :
    CommRing ((SheafOfModules.unit
      (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf).val.obj (op U)) :=
  inferInstanceAs (CommRing Γ(Proj (isotropicProjectiveGrading (t := t) forms), U))

/-- The compatible degree-zero homogeneous section defined by a scalar. -/
def tautologicalConstantTwistSection (forms : Fin m → StrictPairs n → K) (a : K) :
    (Proj.twistingSheaf (isotropicProjectiveGrading (t := t) forms) 0).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ Proj.toTwistingSheaf
      (isotropicProjectiveGrading (t := t) forms) rfl U.unop
      (homogeneousPluckerClass forms (MvPolynomial.C a)
        (MvPolynomial.isHomogeneous_C _ a)))
    (by intro U V i; rfl)

/-- The scalar as an actual global section of the structure sheaf. -/
def tautologicalCoefficientSection (forms : Fin m → StrictPairs n → K) (a : K) :
    (SheafOfModules.unit
      (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf).sections :=
  SheafOfModules.sectionsMap
    (Proj.unitIsoTwistingSheafZero (isotropicProjectiveGrading (t := t) forms)).inv
    (tautologicalConstantTwistSection forms a)

/-- The coefficient section is the literal degree-zero fraction `a / 1`. -/
theorem tautologicalCoefficientSection_value
    (forms : Fin m → StrictPairs n → K) (a : K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens) (x : U) :
    (((tautologicalCoefficientSection (t := t) forms a).eval (op U)).1 x).val =
      Localization.mk (Ideal.Quotient.mk (isotropicPluckerIdeal forms)
        (MvPolynomial.C a)) 1 := by
  change (((Proj.sectionsLinearEquivTwistingSheafZero
    (isotropicProjectiveGrading (t := t) forms) U).symm
      (Proj.toTwistingSheaf (isotropicProjectiveGrading (t := t) forms) rfl U
        (homogeneousPluckerClass forms (MvPolynomial.C a)
          (MvPolynomial.isHomogeneous_C _ a)))).1 x).val = _
  rw [Proj.sectionsLinearEquivTwistingSheafZero_symm_apply_val,
    Proj.toTwistingSheaf_apply_apply]
  rfl

/-- On a normalized affine chart, a constant polynomial gives the same
scalar function as the intrinsic degree-zero homogeneous construction. -/
theorem tautologicalCoefficientSection_chart
    (p : PluckerIndex (t + 2) n) (forms : Fin m → StrictPairs n → K) (a : K) :
    tautologicalChartPolynomialHom p forms (MvPolynomial.C a) =
      (tautologicalCoefficientSection forms a).eval (op (tautologicalChartOpen p forms)) := by
  have hC : isotropicChartEvaluation p forms (MvPolynomial.C a) =
      Ideal.Quotient.mk (isotropicChartIdeal p forms) (MvPolynomial.C a) :=
    (isotropicChartEvaluation p forms).commutes a
  change tautologicalChartSectionHom p forms
    (Ideal.Quotient.mk (isotropicChartIdeal p forms) (MvPolynomial.C a)) = _
  rw [← hC, tautologicalChartSectionHom_homogeneous p forms (MvPolynomial.C a)
    (MvPolynomial.isHomogeneous_C _ a)]
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rw [tautologicalCoefficientSection_value]
  simpa only [homogeneousPluckerClass] using
    ProjConstantFraction.awayToSection_fraction_zero
      (isotropicProjectiveGrading (t := t) forms)
      (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
      (homogeneousPluckerClass (t := t) forms (MvPolynomial.C a)
        (MvPolynomial.isHomogeneous_C _ a)) x

/-- The coefficient comparison holds on every subopen of the chart. -/
theorem tautologicalCoefficientSection_local
    (p : PluckerIndex (t + 2) n) (forms : Fin m → StrictPairs n → K) (a : K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms) :
    tautologicalLocalPolynomialHom p forms U hU (MvPolynomial.C a) =
      (tautologicalCoefficientSection forms a).eval (op U) := by
  change (Proj (isotropicProjectiveGrading (t := t) forms)).presheaf.map
      (homOfLE hU).op (tautologicalChartPolynomialHom p forms (MvPolynomial.C a)) = _
  rw [tautologicalCoefficientSection_chart]
  exact PresheafOfModules.sections_property
    (tautologicalCoefficientSection forms a) (homOfLE hU).op

/-- An ambient coordinate restricted along the genuine tautological inclusion. -/
def tautologicalCoordinateFunctional (forms : Fin m → StrictPairs n → K) (i : Fin n) :
    tautologicalKernel (t := t) forms ⟶
      SheafOfModules.unit
        (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf :=
  tautologicalKernelInclusion (t := t) forms ≫
    Pi.π (fun _ : Fin n ↦ SheafOfModules.unit
      (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf) i

/-- The ambient coordinates of an actual section of the kernel bundle. -/
def tautologicalSectionCoordinates (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (v : (tautologicalKernel (t := t) forms).val.obj (op U)) :
    Fin n → Γ(Proj (isotropicProjectiveGrading (t := t) forms), U) :=
  fun i ↦ (tautologicalCoordinateFunctional forms i).val.app (op U) v

/-- The original alternating form evaluated on actual local kernel sections. -/
def tautologicalLocalAlternatingForm (forms : Fin m → StrictPairs n → K)
    (f : StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens) :=
  AlternatingSectionPresheaf.localForm
    (R := (Proj (isotropicProjectiveGrading (t := t) forms)).sheaf.obj)
    (fun p : StrictPairs n ↦ p.val.1) (fun p : StrictPairs n ↦ p.val.2)
    (fun i ↦ (tautologicalCoordinateFunctional forms i).val)
    (fun p ↦ tautologicalCoefficientSection forms (f p)) (op U)

/-- The original kernel condition reconstructs every section as a linear
combination of the normalized rows, on every subopen of a chart. -/
theorem tautologicalSectionCoordinates_rowCombination
    (p : PluckerIndex (t + 2) n) (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms)
    (v : (tautologicalKernel (t := t) forms).val.obj (op U)) :
    tautologicalSectionCoordinates forms U v =
      (fun i ↦ tautologicalSectionCoordinates forms U v (p.val i)) ᵥ*
        tautologicalLocalMatrix p forms U hU := by
  let z := (tautologicalKernelInclusion (t := t) forms).val.app (op U) v
  have hz : (tautologicalIncidenceMap (t := t) forms).val.app (op U) z = 0 := by
    exact congrArg (fun f ↦ f.val.app (op U) v)
      (tautologicalKernel_incidence (t := t) forms)
  have hcoord : SheafModulePowers.sectionsEquiv
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin n) U z = tautologicalSectionCoordinates forms U v := by
    funext i
    exact SheafModulePowers.sectionsEquiv_apply _ (Fin n) U z i
  have hi := (tautologicalIncidenceMap_local_zero_iff p forms U hU z).mp hz
  rw [hcoord] at hi
  exact (NormalizedTautologicalKernel.incidence_zero_iff_rowCombination
    (tautologicalLocalMatrix p forms U hU) p.val
    (tautologicalLocalMatrix_pivot p forms U hU)
    (tautologicalSectionCoordinates forms U v)).mp hi

/-- The form on the normalized rows is the image of the original chart
polynomial, with its scalar action and all signs unchanged. -/
theorem tautologicalLocalForm_rows
    (p : PluckerIndex (t + 2) n) (forms : Fin m → StrictPairs n → K)
    (f : StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms) (i j : Fin (t + 2)) :
    AlternatingSectionAlgebra.coefficientForm
        (R := Γ(Proj (isotropicProjectiveGrading (t := t) forms), U))
        (fun a : StrictPairs n ↦ a.val.1) (fun a : StrictPairs n ↦ a.val.2)
        (fun a ↦ (tautologicalCoefficientSection forms (f a)).eval (op U))
        ![tautologicalLocalMatrix p forms U hU i,
          tautologicalLocalMatrix p forms U hU j] =
      tautologicalLocalPolynomialHom p forms U hU
        (alternatingRowPair f (pluckerChartMatrix p) i j) := by
  have hc (a : StrictPairs n) :
      (tautologicalCoefficientSection forms (f a)).eval (op U) =
        tautologicalLocalPolynomialHom p forms U hU (MvPolynomial.C (f a)) :=
    (tautologicalCoefficientSection_local p forms (f a) U hU).symm
  simp only [AlternatingSectionAlgebra.coefficientForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, hc,
    tautologicalLocalMatrix, Matrix.map_apply, alternatingRowPair,
    Algebra.smul_def, MvPolynomial.algebraMap_eq, map_sum, map_mul, map_sub]

/-- Every original defining form vanishes on every pair of normalized
frame rows in the literal chart quotient. -/
theorem tautologicalDefiningForm_rows_zero
    (p : PluckerIndex (t + 2) n) (forms : Fin m → StrictPairs n → K) (l : Fin m)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms) (i j : Fin (t + 2)) :
    AlternatingSectionAlgebra.coefficientForm
        (R := Γ(Proj (isotropicProjectiveGrading (t := t) forms), U))
        (fun a : StrictPairs n ↦ a.val.1) (fun a : StrictPairs n ↦ a.val.2)
        (fun a ↦ (tautologicalCoefficientSection forms (forms l a)).eval (op U))
        ![tautologicalLocalMatrix p forms U hU i,
          tautologicalLocalMatrix p forms U hU j] = 0 := by
  rw [tautologicalLocalForm_rows]
  change tautologicalLocalSectionHom p forms U hU
    (Ideal.Quotient.mk (isotropicChartIdeal p forms)
      (alternatingRowPair (forms l) (pluckerChartMatrix p) i j)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (alternatingRowPair_mem_chartIdeal p forms l i j),
    map_zero]

/-- The defining form vanishes on arbitrary kernel sections over any
subopen of a normalized chart, including nonreduced charts. -/
theorem tautologicalDefiningForm_local_zero
    (p : PluckerIndex (t + 2) n) (forms : Fin m → StrictPairs n → K) (l : Fin m)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms)
    (v : Fin 2 → (tautologicalKernel (t := t) forms).val.obj (op U)) :
    tautologicalLocalAlternatingForm forms (forms l) U v = 0 := by
  change AlternatingSectionAlgebra.coefficientForm
      (R := Γ(Proj (isotropicProjectiveGrading (t := t) forms), U))
      (fun a : StrictPairs n ↦ a.val.1) (fun a : StrictPairs n ↦ a.val.2)
      (fun a ↦ (tautologicalCoefficientSection forms (forms l a)).eval (op U))
      (fun i ↦ tautologicalSectionCoordinates forms U (v i)) = 0
  have hv : (fun i ↦ tautologicalSectionCoordinates forms U (v i)) =
      (fun i ↦ ∑ j : Fin (t + 2),
        tautologicalSectionCoordinates forms U (v i) (p.val j) •
          tautologicalLocalMatrix p forms U hU j) := by
    funext i
    exact (tautologicalSectionCoordinates_rowCombination p forms U hU (v i)).trans
      (Matrix.vecMul_eq_sum _ _)
  rw [hv]
  exact AlternatingSectionSpan.alternatingForm_linear_combinations_zero _
    (tautologicalLocalMatrix p forms U hU)
    (tautologicalDefiningForm_rows_zero p forms l U hU) _

/-- Vanishing on the actual projective scheme follows by restriction to
its proved Plücker open cover.  The equality is an equality of functions
with values in homogeneous localizations, without any reduction assumption. -/
theorem tautologicalDefiningForm_sections_zero
    (forms : Fin m → StrictPairs n → K) (l : Fin m)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (v : Fin 2 → (tautologicalKernel (t := t) forms).val.obj (op U)) :
    tautologicalLocalAlternatingForm forms (forms l) U v = 0 := by
  apply Subtype.ext
  funext x
  have hx : x.val ∈ ⨆ p : PluckerIndex (t + 2) n,
      tautologicalChartOpen p forms := by
    change x.val ∈ ⨆ p : PluckerIndex (t + 2) n,
      Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (MvPolynomial.X p))
    rw [isotropicProjBasicOpen_cover_arbitraryChar]
    trivial
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let V := U ⊓ tautologicalChartOpen p forms
  let j : V ⟶ U := homOfLE inf_le_left
  have hz := tautologicalDefiningForm_local_zero p forms l V inf_le_right
    (fun i ↦ (tautologicalKernel (t := t) forms).val.map j.op (v i))
  have hnat := AlternatingSectionPresheaf.localForm_naturality
    (R := (Proj (isotropicProjectiveGrading (t := t) forms)).sheaf.obj)
    (fun a : StrictPairs n ↦ a.val.1) (fun a : StrictPairs n ↦ a.val.2)
    (fun i ↦ (tautologicalCoordinateFunctional forms i).val)
    (fun a ↦ tautologicalCoefficientSection forms (forms l a)) j.op v
  have hr : (Proj (isotropicProjectiveGrading (t := t) forms)).presheaf.map j.op
      (tautologicalLocalAlternatingForm forms (forms l) U v) = 0 :=
    hnat.symm.trans hz
  exact congrArg (fun z : Γ(Proj (isotropicProjectiveGrading (t := t) forms), V) ↦
    z.1 ⟨x.val, ⟨x.property, hp⟩⟩) hr

/-- The actual second exterior power, written using its defining
sectionwise exterior power followed by sheafification. -/
abbrev tautologicalExteriorSquare (forms : Fin m → StrictPairs n → K) :=
  (PresheafOfModules.sheafification
    (R := (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf) (𝟙 _)).obj
    ((PresheafOfModulesOfCommRing.exteriorPower 2).obj
      (tautologicalKernel (t := t) forms).val)

/-- Restriction of an arbitrary original two-form to the tautological bundle. -/
def tautologicalAlternatingFunctional
    (forms : Fin m → StrictPairs n → K) (f : StrictPairs n → K) :
    tautologicalExteriorSquare (t := t) forms ⟶
      SheafOfModules.unit
        (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf :=
  AlternatingSectionSheaf.functional
    (R := (Proj (isotropicProjectiveGrading (t := t) forms)).sheaf)
    (fun p : StrictPairs n ↦ p.val.1) (fun p : StrictPairs n ↦ p.val.2)
    (tautologicalCoordinateFunctional forms)
    (fun p ↦ tautologicalCoefficientSection forms (f p))

/-- Evaluation on local wedges retains every original coefficient and sign. -/
theorem tautologicalAlternatingFunctional_wedge
    (forms : Fin m → StrictPairs n → K) (f : StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (v : Fin 2 → (tautologicalKernel (t := t) forms).val.obj (op U)) :
    (tautologicalAlternatingFunctional (t := t) forms f).val.app (op U)
        (((PresheafOfModules.sheafificationAdjunction
          (R := (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
          (𝟙 _)).unit.app
            ((PresheafOfModulesOfCommRing.exteriorPower 2).obj
              (tautologicalKernel (t := t) forms).val)).app (op U)
                (ModuleCat.exteriorPower.mk v)) =
      ∑ p : StrictPairs n, (tautologicalCoefficientSection forms (f p)).eval (op U) *
        ((tautologicalCoordinateFunctional forms p.val.1).val.app (op U) (v 0) *
          (tautologicalCoordinateFunctional forms p.val.2).val.app (op U) (v 1) -
         (tautologicalCoordinateFunctional forms p.val.2).val.app (op U) (v 0) *
          (tautologicalCoordinateFunctional forms p.val.1).val.app (op U) (v 1)) :=
  AlternatingSectionSheaf.functional_app_sheafified_wedge
    (R := (Proj (isotropicProjectiveGrading (t := t) forms)).sheaf)
    (fun p : StrictPairs n ↦ p.val.1) (fun p : StrictPairs n ↦ p.val.2)
    (tautologicalCoordinateFunctional forms)
    (fun p ↦ tautologicalCoefficientSection forms (f p)) (op U) v

/-- Each original defining form restricts to the zero morphism on the
genuine second exterior power of the tautological incidence kernel. -/
theorem tautologicalDefiningFunctional_eq_zero
    (forms : Fin m → StrictPairs n → K) (l : Fin m) :
    tautologicalAlternatingFunctional (t := t) forms (forms l) = 0 := by
  apply AlternatingSectionSheaf.functional_eq_zero
  intro U v
  exact tautologicalDefiningForm_sections_zero forms l U.unop v

end PaperVerification.AlternatingForms
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsAlternatingSection"

section ComponentSource_5
/- Original module: PaperVerification.AlternatingFormsAmbientSectionFrames -/


/-!
# The intrinsic tautological section in the ambient chart frames

The normalized rows below are actual sections of the incidence-kernel
bundle, obtained by inverting its pivot-coordinate frame.  Evaluating the
global alternating functional on their sheafified wedges gives exactly the
original polynomial equations used in the independent zero-scheme
construction.  This identifies the local equations with the actual
ambient bundle section, including their coefficients and signs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

local instance (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens) :
    CommRing ((Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf.obj.obj
      (op U)) :=
  inferInstanceAs (CommRing Γ(Proj (isotropicProjectiveGrading (t := t) forms), U))

local instance (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens) :
    CommRing ((SheafOfModules.unit
      (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf).val.obj (op U)) :=
  inferInstanceAs (CommRing Γ(Proj (isotropicProjectiveGrading (t := t) forms), U))

local instance (U : (ambientGrassmannian (K := K) t n).Opens) :
    CommRing ((ambientGrassmannian (K := K) t n).ringCatSheaf.obj.obj (op U)) :=
  inferInstanceAs (CommRing Γ(ambientGrassmannian (K := K) t n, U))

local instance (U : (ambientGrassmannian (K := K) t n).Opens) :
    CommRing ((SheafOfModules.unit
      (ambientGrassmannian (K := K) t n).ringCatSheaf).val.obj (op U)) :=
  inferInstanceAs (CommRing Γ(ambientGrassmannian (K := K) t n, U))

/-- Pivot coordinates as a genuine linear equivalence on sections of the bundle. -/
def tautologicalFrameCoordinates (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms) :
    (tautologicalKernel (t := t) forms).val.obj (op U) ≃ₗ[
      Γ(Proj (isotropicProjectiveGrading (t := t) forms), U)]
      (Fin (t + 2) → Γ(Proj (isotropicProjectiveGrading (t := t) forms), U)) :=
  (LinearEquiv.ofBijective ((tautologicalPivotMap p forms).val.app (op U)).hom
    (tautologicalPivotMap_bijective p forms U hU)) ≪≫ₗ
      (SheafModulePowers.sectionsEquiv
        (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
        (Fin (t + 2)) U)

theorem tautologicalFrameCoordinates_apply (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms)
    (v : (tautologicalKernel (t := t) forms).val.obj (op U)) (i : Fin (t + 2)) :
    tautologicalFrameCoordinates p forms U hU v i =
      tautologicalSectionCoordinates forms U v (p.val i) := by
  change SheafModulePowers.sectionsEquiv
    (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
    (Fin (t + 2)) U ((tautologicalPivotMap p forms).val.app (op U) v) i = _
  rw [SheafModulePowers.sectionsEquiv_apply]
  exact congrArg
    (fun g : tautologicalKernel (t := t) forms ⟶
      SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf =>
      g.val.app (op U) v)
    (tautologicalPivotMap_projection p forms i)

/-- A normalized row is an actual section of the original tautological kernel. -/
def tautologicalRowSection (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms) (i : Fin (t + 2)) :
    (tautologicalKernel (t := t) forms).val.obj (op U) :=
  (tautologicalFrameCoordinates p forms U hU).symm (Pi.single i 1)

theorem tautologicalRowSection_coordinates (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms) (i : Fin (t + 2)) :
    tautologicalSectionCoordinates forms U (tautologicalRowSection p forms U hU i) =
      tautologicalLocalMatrix p forms U hU i := by
  rw [tautologicalSectionCoordinates_rowCombination p forms U hU]
  have hp :
      (fun j ↦ tautologicalSectionCoordinates forms U
        (tautologicalRowSection p forms U hU i) (p.val j)) = Pi.single i 1 := by
    rw [← funext (tautologicalFrameCoordinates_apply p forms U hU
      (tautologicalRowSection p forms U hU i))]
    exact (tautologicalFrameCoordinates p forms U hU).apply_symm_apply _
  rw [hp]
  ext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/-- The polynomial section equations are the evaluations of the actual
global alternating functional on the actual local frame wedges. -/
theorem tautologicalAlternatingFunctional_row_wedge
    (p : PluckerIndex (t + 2) n) (forms : Fin m → StrictPairs n → K)
    (f : StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms) (i j : Fin (t + 2)) :
    (tautologicalAlternatingFunctional forms f).val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction
        (R := (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
        (𝟙 _)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower 2).obj
            (tautologicalKernel forms).val)).app (op U)
              (ModuleCat.exteriorPower.mk
                ![tautologicalRowSection p forms U hU i,
                  tautologicalRowSection p forms U hU j])) =
      tautologicalLocalPolynomialHom p forms U hU
        (alternatingRowPair f (pluckerChartMatrix p) i j) := by
  rw [tautologicalAlternatingFunctional_wedge]
  let c : StrictPairs n → Γ(Proj (isotropicProjectiveGrading (t := t) forms), U) :=
    fun a ↦ (tautologicalCoefficientSection forms (f a)).eval (op U)
  change (∑ a : StrictPairs n, c a *
      (tautologicalSectionCoordinates forms U
          (tautologicalRowSection p forms U hU i) a.val.1 *
        tautologicalSectionCoordinates forms U
          (tautologicalRowSection p forms U hU j) a.val.2 -
       tautologicalSectionCoordinates forms U
          (tautologicalRowSection p forms U hU i) a.val.2 *
        tautologicalSectionCoordinates forms U
          (tautologicalRowSection p forms U hU j) a.val.1)) = _
  simp only [tautologicalRowSection_coordinates]
  simpa only [c, AlternatingSectionAlgebra.coefficientForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
      tautologicalLocalForm_rows p forms f U hU i j

/-- The original section equations are evaluated on the ambient bundle,
where no isotropy condition has yet been imposed. -/
theorem ambientAlternatingFunctional_row_wedge
    (p : PluckerIndex (t + 2) n) (f : StrictPairs n → K)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n)))
    (i j : Fin (t + 2)) :
    (tautologicalAlternatingFunctional emptyAlternatingTuple f).val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction
        (R := (ambientGrassmannian (K := K) t n).ringCatSheaf)
        (𝟙 _)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower 2).obj
            (tautologicalKernel (t := t) emptyAlternatingTuple).val)).app (op U)
              (ModuleCat.exteriorPower.mk
                ![tautologicalRowSection p emptyAlternatingTuple U hU i,
                  tautologicalRowSection p emptyAlternatingTuple U hU j])) =
      tautologicalLocalPolynomialHom p emptyAlternatingTuple U hU
        (alternatingRowPair f (pluckerChartMatrix p) i j) :=
  tautologicalAlternatingFunctional_row_wedge p emptyAlternatingTuple f U hU i j

/-- The ambient chart's polynomial functions identify bijectively with
the actual structure-sheaf sections.  Thus the displayed section equations
are an equality in the full chart ring, not merely an equality of values. -/
theorem ambientChartPolynomialHom_bijective (p : PluckerIndex (t + 2) n) :
    Function.Bijective
      (tautologicalChartPolynomialHom p (emptyAlternatingTuple (K := K) (n := n))) := by
  let g := isotropicProjectiveGrading (t := t)
    (emptyAlternatingTuple (K := K) (n := n))
  let x := Ideal.Quotient.mk
    (isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)))
    (MvPolynomial.X p)
  let hx := HomogeneousQuotientProjective.quotient_X_mem_one
    (isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)))
    (isotropicPluckerIdeal_isHomogeneous emptyAlternatingTuple) p
  letI : IsIso (Proj.awayToSection g x) :=
    (Proj.basicOpenIsoAway g x hx one_pos).isIso_hom
  have hsection : Function.Bijective
      (tautologicalChartSectionHom p (emptyAlternatingTuple (K := K) (n := n))) :=
    (ConcreteCategory.bijective_of_isIso (Proj.awayToSection g x)).comp
      (isotropicProjChartRingEquiv_arbitraryChar p emptyAlternatingTuple).symm.bijective
  have hquot : Function.Bijective
      (Ideal.Quotient.mk (isotropicChartIdeal p
        (emptyAlternatingTuple (K := K) (n := n)))) := by
    rw [isotropicChartIdeal_empty]
    exact (RingEquiv.quotientBot (MvPolynomial (PluckerChartVariable p) K)).symm.bijective
  exact hsection.comp hquot

end PaperVerification.AlternatingForms
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsAmbientSectionFrames"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.GradedSurjective, "definition"),
    (`PaperVerification.irrelevant_le_map_of_gradedSurjective, "theorem"),
    (`PaperVerification.gradedAwayMap_surjective, "theorem"),
    (`PaperVerification.gradedProjMap_chart_isPullback, "theorem"),
    (`PaperVerification.isClosedImmersion_projMap_of_gradedSurjective, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientGradedHom, "definition"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientGradedHom_surjective, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientProjMap, "definition"),
    (`PaperVerification.AlternatingForms.emptyAlternatingTuple, "definition"),
    (`PaperVerification.AlternatingForms.isotropicPluckerIdeal_empty, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicChartIdeal_empty, "theorem"),
    (`PaperVerification.AlternatingForms.ambientGrassmannian, "definition"),
    (`PaperVerification.AlternatingForms.isotropicAmbientImmersion, "definition"),
    (`PaperVerification.AlternatingForms.isotropicAmbientImmersion_preimage_chart, "theorem"),
    (`PaperVerification.AlternatingForms.ambientChartRingEquiv, "definition"),
    (`PaperVerification.AlternatingForms.ambientChartRing_commutes, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicAffineChart_ambient_commutes, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicAffineChart_ambient_isPullback, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicAffineChartCover, "definition"),
    (`PaperVerification.AlternatingForms.isotropicChartSectionFunctional, "definition"),
    (`PaperVerification.AlternatingForms.isotropicChartSectionFunctional_range, "theorem"),
    (`PaperVerification.AlternatingForms.ambientSectionChartIdeal, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroIdeal, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroScheme, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroIdeal_eq_kernel, "theorem"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroIdeal_chart, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicSectionZeroIso, "definition"),
    (`PaperVerification.AlternatingForms.isotropicSectionZeroIso_over_ambient, "theorem"),
    (`PaperVerification.AlternatingForms.tautologicalAlternatingFunctional, "definition"),
    (`PaperVerification.AlternatingForms.tautologicalFrameCoordinates, "definition"),
    (`PaperVerification.AlternatingForms.tautologicalRowSection_coordinates, "theorem"),
    (`PaperVerification.AlternatingForms.tautologicalAlternatingFunctional_row_wedge, "theorem"),
    (`PaperVerification.AlternatingForms.ambientAlternatingFunctional_row_wedge, "theorem"),
    (`PaperVerification.AlternatingForms.ambientChartPolynomialHom_bijective, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicPluckerIdeal_map_chart_eq_arbitraryChar, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicChartEvaluation_kernel_arbitraryChar, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicPluckerBigCellEquiv_arbitraryChar, "definition"),
    (`PaperVerification.AlternatingForms.isotropicProjChartRingEquiv_arbitraryChar, "definition"),
    (`PaperVerification.AlternatingForms.isotropicProjBasicOpenIso_arbitraryChar, "definition"),
    (`PaperVerification.AlternatingForms.isotropicProjBasicOpen_cover_arbitraryChar, "theorem"),
    (`PaperVerification.AlternatingForms.tautologicalFrameIso, "definition"),
    (`PaperVerification.AlternatingForms.tautologicalPivotMap_bijective, "theorem"),
    (`PaperVerification.AlternatingForms.tautologicalDefiningFunctional_eq_zero, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "128bdddc5682993a1b8e835067d6d757"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:128bdddc5682993a1b8e835067d6d757"
