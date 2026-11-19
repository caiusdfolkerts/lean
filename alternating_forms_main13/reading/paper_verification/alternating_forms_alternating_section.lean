module

public import PaperVerification.AlternatingSectionVanishing
public import PaperVerification.AlternatingFormsTautologicalLocalFrames
public import PaperVerification.ProjConstantFraction

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
