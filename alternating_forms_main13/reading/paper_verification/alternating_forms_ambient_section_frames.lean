module

public import PaperVerification.AlternatingFormsSectionZeroScheme
public import PaperVerification.AlternatingFormsAlternatingSection

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
