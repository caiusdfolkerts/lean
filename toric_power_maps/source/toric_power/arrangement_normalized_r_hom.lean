module

public import ToricPower.ArrangementBoundarySources
public import ToricPower.ArrangementPowerDerivedModel
public import ToricPower.ArrangementNormalizedAdjunction
public import ToricPower.CartierFiniteMeetDerived
public import ToricPower.RightDerivedPrecomposeEquivalence

/-!
# Identifying the finite model with the normalized unbounded right adjoint

Both models satisfy the actual right-derived universal property for
their stated comparison maps. Cartier multiplication and the original
tensor adjunction account for the boundary twist; the inverse dimension
shift is then applied explicitly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open TopologicalSpace TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X
set_option quotPrecheck false in
local notation "DC" => DerivedCategory (C ⥤ ModuleCat.{0} ℂ)
local notation "P" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "PN" => normalizedCartierQuasicoherentSources fan nonempty regular basis rays
local notation "U" => toricDerivedChartOpen fan
local notation "l" => toricDerivedChartList fan
local notation "E" => quasicoherentCartierTensorEquivalence
  (invariantCartierDivisor fan nonempty regular (fun _ => 1))

local instance normalizedRHom_derivedQCoh : HasDerivedCategory.{1} Q := HasDerivedCategory.standard _
local instance normalizedRHom_derivedCells : HasDerivedCategory.{1} (C ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _
local instance normalizedRHom_derivedCharts : HasDerivedCategory.{1} ((ToricMeetChartIndex fan)ᵒᵖ ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

theorem normalizedCartierSources_invertible (c : C) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X ((PN).obj (op c)).obj := by
  letI := toricSchemeIntegral fan nonempty
  change TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
    (invariantCartierDivisor fan nonempty regular
      ((fun _ => 1) + diagonalRightCoefficients fan basis rays c.2)).sheaf
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isInvertible_sheaf _

local instance normalizedToricHomLimits (cone : fan.cones) :
    PreservesFiniteLimits (quasicoherentOpenLocalization (U cone).ι ⋙ Cellular.homDiagram ℂ PN) :=
  (toricDerivedLabelLocalExact fan PN
    (normalizedCartierSources_invertible fan nonempty regular basis rays) cone).1

local instance normalizedToricHomColimits (cone : fan.cones) :
    PreservesFiniteColimits (quasicoherentOpenLocalization (U cone).ι ⋙ Cellular.homDiagram ℂ PN) :=
  (toricDerivedLabelLocalExact fan PN
    (normalizedCartierSources_invertible fan nonempty regular basis rays) cone).2

local instance originalToricHomLimits (cone : fan.cones) :
    PreservesFiniteLimits (quasicoherentOpenLocalization (U cone).ι ⋙ Cellular.homDiagram ℂ P) :=
  (toricDerivedLabelLocalExact fan P (fun _ => inferInstance) cone).1

local instance originalToricHomColimits (cone : fan.cones) :
    PreservesFiniteColimits (quasicoherentOpenLocalization (U cone).ι ⋙ Cellular.homDiagram ℂ P) :=
  (toricDerivedLabelLocalExact fan P (fun _ => inferInstance) cone).2

/-- The actual affine right-derived Hom functor for the normalized sources. -/
def normalizedCartierAffineRHom : DerivedCategory Q ⥤ DC :=
  affineConeDerivedStage U (Cellular.homDiagram ℂ PN) l

/-- Universal uniqueness retains the genuine boundary tensor adjunction. -/
def normalizedCartierRHomBoundaryIso :
    letI := toricSchemeIntegral fan nonempty
    normalizedCartierAffineRHom fan nonempty regular basis rays ≅
      (E).inverse.mapDerivedCategory ⋙ arrangementToricDerivedHom fan nonempty regular basis rays := by
  letI := toricSchemeIntegral fan nonempty
  letI : (E).symm.functor.Additive := inferInstanceAs (E).inverse.Additive
  let α := affineRightDerivedUnit U (Cellular.homDiagram ℂ P) l
  letI : (arrangementToricDerivedHom fan nonempty regular basis rays).IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso Q (.up ℤ)) :=
    affineConeDerivedStage_isRightDerivedFunctor U (Cellular.homDiagram ℂ P)
      l (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan)
  letI : (normalizedCartierAffineRHom fan nonempty regular basis rays).IsRightDerivedFunctor
      (affineRightDerivedUnit U (Cellular.homDiagram ℂ PN) l)
      (HomologicalComplex.quasiIso Q (.up ℤ)) :=
    affineConeDerivedStage_isRightDerivedFunctor U (Cellular.homDiagram ℂ PN)
      l (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan)
  letI : ((E).inverse.mapDerivedCategory ⋙
      arrangementToricDerivedHom fan nonempty regular basis rays).IsRightDerivedFunctor
      (rightDerivedPrecomposeEquivalenceUnit (E).symm (Cellular.homDiagram ℂ P)
        (arrangementToricDerivedHom fan nonempty regular basis rays) α)
      (HomologicalComplex.quasiIso Q (.up ℤ)) :=
    rightDerivedPrecomposeEquivalence_isRightDerivedFunctor (E).symm
      (Cellular.homDiagram ℂ P) (arrangementToricDerivedHom fan nonempty regular basis rays) α
  exact Functor.rightDerivedNatIso
    (normalizedCartierAffineRHom fan nonempty regular basis rays)
    ((E).inverse.mapDerivedCategory ⋙ arrangementToricDerivedHom fan nonempty regular basis rays)
    (affineRightDerivedUnit U (Cellular.homDiagram ℂ PN) l)
    (rightDerivedPrecomposeEquivalenceUnit (E).symm (Cellular.homDiagram ℂ P)
      (arrangementToricDerivedHom fan nonempty regular basis rays) α)
    (HomologicalComplex.quasiIso Q (.up ℤ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (normalizedCartierHomBoundaryIso fan nonempty regular basis rays) (.up ℤ))
      DerivedCategory.Q)

local notation "B" => ToricMeetChartIndex fan
local notation "V'" => Functor.obj (toricMeetChartOpenFunctor fan)

local instance normalizedMeetAffine (a : B) : IsAffine (V' a).toScheme :=
  toricDerivedChartOpen_isAffine fan (toricMeetChartEquiv fan a)
local instance normalizedMeetIntegral (a : B) : IsIntegral (V' a).toScheme :=
  toricDerivedChartOpen_isIntegral fan (toricMeetChartEquiv fan a)
local instance normalizedMeetAffineHom (a : B) : IsAffineHom (V' a).ι :=
  toricDerivedChartOpen_isAffineHom fan (toricMeetChartEquiv fan a)
local instance normalizedMeetHomLimits (a : B) :
    PreservesFiniteLimits (quasicoherentOpenLocalization (V' a).ι ⋙ Cellular.homDiagram ℂ PN) :=
  normalizedToricHomLimits fan nonempty regular basis rays (toricMeetChartEquiv fan a)
local instance normalizedMeetHomColimits (a : B) :
    PreservesFiniteColimits (quasicoherentOpenLocalization (V' a).ι ⋙ Cellular.homDiagram ℂ PN) :=
  normalizedToricHomColimits fan nonempty regular basis rays (toricMeetChartEquiv fan a)

/-- Every chart is included; the smaller index type only changes its universe. -/
def toricMeetDerivedChartList : List B :=
  letI : Fintype B := Fintype.ofFinite _
  Finset.univ.toList

theorem mem_toricMeetDerivedChartList (a : B) : a ∈ toricMeetDerivedChartList fan := by
  simp [toricMeetDerivedChartList]

/-- The finite chart model is the actual unbounded right adjoint for
the normalized sources, independently of the chosen affine index type. -/
def normalizedCartierFiniteRHomIso :
    normalizedCartierFiniteModel fan nonempty regular basis rays ≅
      normalizedCartierAffineRHom fan nonempty regular basis rays := by
  letI := toricSchemeIntegral fan nonempty
  let l' := toricMeetDerivedChartList fan
  letI := affineConeDerivedStage_isRightDerivedFunctor V' (Cellular.homDiagram ℂ PN)
    l' (mem_toricMeetDerivedChartList fan) (IsOpenCover.mk (toricMeetChartOpen_covers fan))
  letI := affineConeDerivedStage_isRightDerivedFunctor U (Cellular.homDiagram ℂ PN)
    l (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan)
  exact cartierFiniteMeetRHomIso ℂ X
      (normalizedCartierSources fan nonempty regular basis rays) (toricMeetChartOpenFunctor fan)
      (fun a => isAffineOpen_opensRange (fan.affineToricChartι (toricMeetChartEquiv fan a)))
      (fun a b => (toricMeetChartOpenHom fan).map_inf' a b)
      (toricMeetChartOpen_covers fan) (toricMeetChartOpen_tupleMeet fan)
      l' (mem_toricMeetDerivedChartList fan) ≪≫
    Functor.rightDerivedUnique
      (affineConeDerivedStage V' (Cellular.homDiagram ℂ PN) l')
      (affineConeDerivedStage U (Cellular.homDiagram ℂ PN) l)
      (affineRightDerivedUnit V' (Cellular.homDiagram ℂ PN) l')
      (affineRightDerivedUnit U (Cellular.homDiagram ℂ PN) l)
      (HomologicalComplex.quasiIso Q (.up ℤ))

/-- The paper's actual normalized right adjoint is the concrete finite
model with exactly the inverse dimension shift. -/
def arrangementNormalizedHomFiniteModelIso :
    letI := nonempty
    arrangementNormalizedDerivedHom fan regular basis rays ≅
      shiftFunctor (DerivedCategory Q) (n : ℤ) ⋙
        normalizedCartierFiniteModel fan nonempty regular basis rays := by
  letI := nonempty
  letI := toricSchemeIntegral fan nonempty
  change shiftFunctor (DerivedCategory Q) (-(-(n : ℤ))) ⋙
      (E).inverse.mapDerivedCategory ⋙ arrangementToricDerivedHom fan nonempty regular basis rays ≅ _
  rw [neg_neg]
  exact Functor.isoWhiskerLeft (shiftFunctor (DerivedCategory Q) (n : ℤ))
    ((normalizedCartierFiniteRHomIso fan nonempty regular basis rays) ≪≫
      normalizedCartierRHomBoundaryIso fan nonempty regular basis rays).symm

end ToricPower

end
