module

public import PaperVerification.ProjTautologicalLineCoordinates
public import PaperVerification.ZeroExteriorSectionScheme
public import PaperVerification.AlternatingFormsOnePlaneSections

/-!
# The actual tautological zero-section interpretation for one-planes

The ambient scheme is the original one-row Plücker Proj.  Its tautological
line is the actual O(-1), with coordinates given by multiplication by the
original Plücker variables.  Original alternating forms are restricted to
that line as sheaf morphisms, before their vanishing is proved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open scoped BigOperators

namespace PaperVerification.AlternatingForms

universe u

variable {K : Type} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original one-row Plücker grading, for every ambient dimension. -/
def onePlaneAmbientGrading (n : ℕ) : ℕ → Submodule K
    (MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal) :=
  HomogeneousQuotientProjective.grading _ (onePlane_matrixPluckerIdeal_isHomogeneous n)

instance onePlaneAmbientGradedAlgebra (n : ℕ) :
    GradedAlgebra (onePlaneAmbientGrading (K := K) n) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra _ _

/-- Agreement with the original odd-dimensional one-plane section theorem. -/
theorem onePlaneAmbientGrading_odd (k : ℕ) :
    onePlaneAmbientGrading (K := K) (2 * k + 1) = onePlaneProjectiveGrading k := rfl

abbrev onePlaneAmbient (n : ℕ) : Scheme := Proj (onePlaneAmbientGrading (K := K) n)

/-- The actual tautological line sheaf on the Plücker projective scheme. -/
abbrev onePlaneTautologicalLine (n : ℕ) : (onePlaneAmbient (K := K) n).Modules :=
  Proj.twistingSheaf (onePlaneAmbientGrading (K := K) n) (-1)

local instance (n : ℕ) (U : (onePlaneAmbient (K := K) n).Opens) :
    CommRing ((onePlaneAmbient (K := K) n).ringCatSheaf.obj.obj (op U)) :=
  inferInstanceAs (CommRing Γ(onePlaneAmbient (K := K) n, U))

local instance (n : ℕ) (U : (onePlaneAmbient (K := K) n).Opens) :
    CommRing ((SheafOfModules.unit (onePlaneAmbient (K := K) n).ringCatSheaf).val.obj (op U)) :=
  inferInstanceAs (CommRing Γ(onePlaneAmbient (K := K) n, U))

theorem onePlaneAmbient_cover (n : ℕ) :
    (⨆ p : PluckerIndex 1 n, Proj.basicOpen (onePlaneAmbientGrading (K := K) n)
      (Ideal.Quotient.mk matrixPluckerIdeal (X p))) = ⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover _ _
    (Ideal.Quotient.mkₐ K matrixPluckerIdeal)
    (Ideal.Quotient.mkₐ_surjective K matrixPluckerIdeal)
    (fun p ↦ HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)

/-- The genuine second exterior-power sheaf of this tautological line is zero. -/
theorem onePlaneTautological_exteriorSquare_isZero (n : ℕ) :
    IsZero (LineExteriorSquareZero.exteriorSquare (onePlaneTautologicalLine (K := K) n)) :=
  LineExteriorSquareZero.twistingSheaf_exteriorSquare_isZero
    (onePlaneAmbientGrading (K := K) n)
    (fun p : PluckerIndex 1 n ↦ Ideal.Quotient.mk matrixPluckerIdeal (X p))
    (fun p ↦ HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
    (onePlaneAmbient_cover n) (-1)

/-- Each ambient coordinate is the original Plücker coordinate on O(-1). -/
def onePlaneTautologicalCoordinate (n : ℕ) (i : Fin n) :
    onePlaneTautologicalLine (K := K) n ⟶
      SheafOfModules.unit (onePlaneAmbient (K := K) n).ringCatSheaf :=
  ProjTautologicalLineCoordinates.coordinate (onePlaneAmbientGrading (K := K) n)
    (Ideal.Quotient.mk matrixPluckerIdeal (X (onePlaneIndex i)))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ (onePlaneIndex i))

def onePlaneHomogeneousClass (n d : ℕ)
    (p : MvPolynomial (PluckerIndex 1 n) K) (hp : p.IsHomogeneous d) :
    onePlaneAmbientGrading (K := K) n d :=
  ⟨Ideal.Quotient.mk matrixPluckerIdeal p, by
    rw [onePlaneAmbientGrading, HomogeneousQuotientProjective.grading_eq_piece]
    exact ⟨p, hp, rfl⟩⟩

def onePlaneConstantTwistSection (n : ℕ) (a : K) :
    (Proj.twistingSheaf (onePlaneAmbientGrading (K := K) n) 0).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ Proj.toTwistingSheaf (onePlaneAmbientGrading (K := K) n) rfl U.unop
      (onePlaneHomogeneousClass n 0 (C a) (isHomogeneous_C _ a)))
    (by intro U V i; rfl)

/-- Original scalar coefficients as actual regular functions on the ambient scheme. -/
def onePlaneCoefficientSection (n : ℕ) (a : K) :
    (SheafOfModules.unit (onePlaneAmbient (K := K) n).ringCatSheaf).sections :=
  SheafOfModules.sectionsMap
    (Proj.unitIsoTwistingSheafZero (onePlaneAmbientGrading (K := K) n)).inv
    (onePlaneConstantTwistSection n a)

/-- Each original scalar coefficient is its literal degree-zero fraction. -/
theorem onePlaneCoefficientSection_value (n : ℕ) (a : K)
    (U : (onePlaneAmbient (K := K) n).Opens) (x : U) :
    (((onePlaneCoefficientSection n a).eval (op U)).1 x).val =
      Localization.mk (Ideal.Quotient.mk matrixPluckerIdeal
        (MvPolynomial.C a : MvPolynomial (PluckerIndex 1 n) K)) 1 := by
  change (((Proj.sectionsLinearEquivTwistingSheafZero
    (onePlaneAmbientGrading (K := K) n) U).symm
      (Proj.toTwistingSheaf (onePlaneAmbientGrading (K := K) n) rfl U
        (onePlaneHomogeneousClass n 0 (MvPolynomial.C a)
          (MvPolynomial.isHomogeneous_C _ a)))).1 x).val = _
  rw [Proj.sectionsLinearEquivTwistingSheafZero_symm_apply_val,
    Proj.toTwistingSheaf_apply_apply]
  rfl

/-- Restriction of an arbitrary original two-form to the actual tautological line. -/
def onePlaneAlternatingFunctional {n : ℕ} (f : StrictPairs n → K) :
    LineExteriorSquareZero.exteriorSquare (onePlaneTautologicalLine (K := K) n) ⟶
      SheafOfModules.unit (onePlaneAmbient (K := K) n).ringCatSheaf :=
  AlternatingSectionSheaf.functional (R := (onePlaneAmbient (K := K) n).sheaf)
    (fun p : StrictPairs n ↦ p.val.1) (fun p : StrictPairs n ↦ p.val.2)
    (onePlaneTautologicalCoordinate n) (fun p : StrictPairs n ↦ onePlaneCoefficientSection n (f p))

/-- The actual functional has the original alternating coefficient formula on every local wedge. -/
theorem onePlaneAlternatingFunctional_wedge {n : ℕ} (f : StrictPairs n → K)
    (U : (onePlaneAmbient (K := K) n).Opens)
    (v : Fin 2 → (onePlaneTautologicalLine (K := K) n).val.obj (op U)) :
    (onePlaneAlternatingFunctional f).val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction
          (R := (onePlaneAmbient (K := K) n).ringCatSheaf) (𝟙 _)).unit.app
        ((PresheafOfModulesOfCommRing.exteriorPower 2).obj
          (onePlaneTautologicalLine (K := K) n).val)).app (op U)
        (ModuleCat.exteriorPower.mk v)) =
      ∑ p : StrictPairs n, (onePlaneCoefficientSection n (f p)).eval (op U) *
        ((onePlaneTautologicalCoordinate n p.val.1).val.app (op U) (v 0) *
          (onePlaneTautologicalCoordinate n p.val.2).val.app (op U) (v 1) -
         (onePlaneTautologicalCoordinate n p.val.2).val.app (op U) (v 0) *
          (onePlaneTautologicalCoordinate n p.val.1).val.app (op U) (v 1)) :=
  AlternatingSectionSheaf.functional_app_sheafified_wedge
    (R := (onePlaneAmbient (K := K) n).sheaf)
    (fun p : StrictPairs n ↦ p.val.1) (fun p : StrictPairs n ↦ p.val.2)
    (onePlaneTautologicalCoordinate n) (fun p : StrictPairs n ↦ onePlaneCoefficientSection n (f p)) (op U) v

/-- Every original alternating form restricts to zero as a sheaf morphism. -/
theorem onePlaneAlternatingFunctional_eq_zero {n : ℕ} (f : StrictPairs n → K) :
    onePlaneAlternatingFunctional f = 0 :=
  (onePlaneTautological_exteriorSquare_isZero n).eq_zero_of_src _

/-- The zero ideal is formed from the actual restriction morphisms, with every coefficient retained. -/
def onePlaneSectionZeroIdeal {n m : ℕ} (forms : Fin m → StrictPairs n → K) :
    (onePlaneAmbient (K := K) n).IdealSheafData :=
  ZeroExteriorSectionScheme.imageIdeal (fun l ↦ onePlaneAlternatingFunctional (forms l))

theorem onePlaneSectionZeroIdeal_eq_bot {n m : ℕ} (forms : Fin m → StrictPairs n → K) :
    onePlaneSectionZeroIdeal forms = ⊥ :=
  ZeroExteriorSectionScheme.imageIdeal_eq_bot _ (onePlaneTautological_exteriorSquare_isZero n)

/-- The original one-plane isotropy zero scheme is the whole original Plücker scheme. -/
def onePlaneSectionZeroIso {n m : ℕ} (forms : Fin m → StrictPairs n → K) :
    (onePlaneSectionZeroIdeal forms).subscheme ≅ onePlaneAmbient (K := K) n :=
  ZeroExteriorSectionScheme.zeroSchemeIso _ (onePlaneTautological_exteriorSquare_isZero n)

theorem onePlaneSectionZeroIso_over_ambient {n m : ℕ}
    (forms : Fin m → StrictPairs n → K) :
    (onePlaneSectionZeroIso forms).hom = (onePlaneSectionZeroIdeal forms).subschemeι := rfl

/-- Every integer Plücker twist on the actual one-plane zero scheme. -/
def onePlaneSectionZeroTwist {n m : ℕ}
    (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (onePlaneSectionZeroIdeal forms).subscheme.Modules :=
  (Scheme.Modules.pullback (onePlaneSectionZeroIdeal forms).subschemeι).obj
    (Proj.twistingSheaf (onePlaneAmbientGrading (K := K) n) r)

/-- The one-plane comparison preserves the actual Plücker line and all its twists. -/
def onePlaneSectionZeroTwistingIso {n m : ℕ}
    (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (Scheme.Modules.pullback (onePlaneSectionZeroIso forms).inv).obj
        (onePlaneSectionZeroTwist forms r) ≅
      Proj.twistingSheaf (onePlaneAmbientGrading (K := K) n) r :=
  (Scheme.Modules.pullbackComp (onePlaneSectionZeroIso forms).inv
    (onePlaneSectionZeroIdeal forms).subschemeι).app _ ≪≫
    eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
      (Proj.twistingSheaf (onePlaneAmbientGrading (K := K) n) r))
      (onePlaneSectionZeroIso forms).inv_hom_id) ≪≫
    (Scheme.Modules.pullbackId (onePlaneAmbient (K := K) n)).app _

end PaperVerification.AlternatingForms
