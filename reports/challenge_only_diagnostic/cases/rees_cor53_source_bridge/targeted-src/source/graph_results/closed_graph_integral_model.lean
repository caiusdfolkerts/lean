module
public import graph_results.closed_graph_power_homology
public import shared_results.part012
public import shared_results.part014
public import shared_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIntegralModel -/
section

/-! # The actual finite free integral graph model

The coefficient ring is literally ℤ[z], and the coefficient module is the
literal power of the displayed parameter ideal. The transferred differential
is polynomial-linear, has entries in the variable ideal, and has the actual
module-action augmentation. Its coefficient-linear splitting is explicit and
survives every coefficient base change. The separate degree construction
turns this total model into the finite graded chain resolution of Section 9.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open HomologicalPerturbation
open scoped TensorProduct
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
attribute [local instance 2000] LinearMap.IsScalarTower.compatibleSMul

abbrev GraphIntegralCoefficientRing := Polynomial ℤ
abbrev GraphIntegralVariables (N : ℕ) := FiniteVariable.{0} (GraphRows N)
abbrev GraphIntegralPolynomialRing (N : ℕ) :=
  MvPolynomial (GraphIntegralVariables N) GraphIntegralCoefficientRing

variable {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) (s : ℕ)

def integralGraphParameterData : QuotientGroebnerData (GraphIntegralVariables N)
    GraphIntegralCoefficientRing :=
  graphParameterPowerQuotientData (Polynomial.X : Polynomial ℤ) Polynomial.X_ne_zero hG s

def integralGraphParameterHomogeneous :
    (integralGraphParameterData hG s).ideal.IsHomogeneous
      (weightedHomogeneousSubmodule GraphIntegralCoefficientRing
        (fun _ : GraphIntegralVariables N => (1 : ℕ))) :=
  graphParameterPower_ordinary_homogeneous (Polynomial.X : Polynomial ℤ) G s

abbrev IntegralGraphModule := (integralGraphParameterData hG s).ideal
abbrev IntegralGraphHomology := IdealGradedHomology (integralGraphParameterData hG s)
  (integralGraphParameterHomogeneous hG s)
abbrev IntegralGraphFreeModel := GraphIntegralPolynomialRing N ⊗[GraphIntegralCoefficientRing]
  IntegralGraphHomology hG s

local instance integralGraphFreeModel_scalarTower :
    IsScalarTower GraphIntegralCoefficientRing (GraphIntegralPolynomialRing N)
      (IntegralGraphFreeModel hG s) :=
  TensorProduct.isScalarTower_left (R := GraphIntegralCoefficientRing)
    (R' := GraphIntegralPolynomialRing N) (R'₂ := GraphIntegralCoefficientRing)
    (M := GraphIntegralPolynomialRing N) (N := IntegralGraphHomology hG s)

local instance integralGraphModule_scalarTower :
    IsScalarTower GraphIntegralCoefficientRing (GraphIntegralPolynomialRing N)
      (IntegralGraphModule hG s) :=
  Submodule.isScalarTower (integralGraphParameterData hG s).ideal

variable (hs : 0 < s)

include hs in
theorem integralGraphHomologyPiece_free (q p : ℕ) :
    Module.Free GraphIntegralCoefficientRing
      (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) q p) := by
  dsimp only [integralGraphParameterData, integralGraphParameterHomogeneous]
  exact intervalGraph_parameter_power_homology_free (k := Polynomial ℤ) hG
    Polynomial.X Polynomial.X_ne_zero s hs q p

include hs in
theorem integralGraphHomologyPiece_finite (q p : ℕ) :
    Module.Finite GraphIntegralCoefficientRing
      (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) q p) := by
  dsimp only [integralGraphParameterData, integralGraphParameterHomogeneous]
  exact intervalGraph_parameter_power_homology_finite (k := Polynomial ℤ) hG
    Polynomial.X Polynomial.X_ne_zero s hs q p

include hs in
/-- Freeness of total homology is proved from the actual homogeneous
pieces, independently of the later polynomial extension. -/
theorem integralGraphHomology_free :
    Module.Free GraphIntegralCoefficientRing (IntegralGraphHomology hG s) := by
  letI : ∀ q p, Module.Free GraphIntegralCoefficientRing
      (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) q p) :=
    integralGraphHomologyPiece_free hG s hs
  exact Module.Free.of_basis (gradedFreeBasis
    (fun q p => actualIdealOrdinaryHomology (integralGraphParameterData hG s)
      (integralGraphParameterHomogeneous hG s) q p))

include hs in
/-- The explicit q and p support bounds make the total actual homology
finite; no finiteness of the infinite polynomial Koszul terms is assumed. -/
theorem integralGraphHomology_finite :
    Module.Finite GraphIntegralCoefficientRing (IntegralGraphHomology hG s) := by
  letI : ∀ q p, Module.Free GraphIntegralCoefficientRing
      (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) q p) :=
    integralGraphHomologyPiece_free hG s hs
  letI : ∀ q p, Module.Finite GraphIntegralCoefficientRing
      (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) q p) :=
    integralGraphHomologyPiece_finite hG s hs
  apply finite_gradedFreeTotal
    (fun q p => actualIdealOrdinaryHomology (integralGraphParameterData hG s)
      (integralGraphParameterHomogeneous hG s) q p)
    (Fintype.card (GraphIntegralVariables N) * s) (Fintype.card (GraphIntegralVariables N))
  · intro q p hq
    dsimp only [integralGraphParameterData, integralGraphParameterHomogeneous]
    exact intervalGraph_parameter_power_homology_zero_of_degree_gt hG
      (Polynomial.X : Polynomial ℤ) Polynomial.X_ne_zero s q p hq
  · intro q p hp
    dsimp only [integralGraphParameterData, integralGraphParameterHomogeneous]
    exact intervalGraph_parameter_power_homology_zero_of_exterior_degree_gt hG
      (Polynomial.X : Polynomial ℤ) Polynomial.X_ne_zero s q p hp

/-- The actual coefficient Koszul contraction has no unproved splitting
input: all homology projectivity was obtained from the graph theorem. -/
def integralGraphKoszulContraction :
    LinearContraction (R := GraphIntegralCoefficientRing)
      (M := TensorExteriorKoszul.Total (K := GraphIntegralCoefficientRing)
        (V := GraphIntegralVariables N) (M := IntegralGraphModule hG s))
      (H := IntegralGraphHomology hG s) :=
  actualIdealTensorContraction (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs)

theorem integralGraphKoszulContraction_d :
    (integralGraphKoszulContraction hG s hs).d =
      TensorExteriorKoszul.differential (K := GraphIntegralCoefficientRing)
        (M := IntegralGraphModule hG s) (X : GraphIntegralVariables N → GraphIntegralPolynomialRing N) :=
  actualIdealTensorContraction_d (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs)

def integralGraphIdealBasis :=
  groebnerIdealBasis (integralGraphParameterData hG s).order
    (integralGraphParameterData hG s).ideal (integralGraphParameterData hG s).generators
    (integralGraphParameterData hG s).groebner (integralGraphParameterData hG s).unitLeading

def integralGraphCoefficientDegree
    (a : NonstandardIndex (integralGraphParameterData hG s).order
      (integralGraphParameterData hG s).ideal) : ℕ := a.val.degree

theorem integralGraphKoszulContraction_h_nonincreasing :
    DegreeNonincreasing (R := GraphIntegralCoefficientRing)
      (M := TensorExteriorKoszul.Total (K := GraphIntegralCoefficientRing)
        (V := GraphIntegralVariables N) (M := IntegralGraphModule hG s))
      (PolynomialPerturbation.tensorBasis (R := GraphIntegralCoefficientRing)
        (V := GraphIntegralVariables N) (IntegralGraphModule hG s) (integralGraphIdealBasis hG s))
      (PolynomialPerturbation.internalDegree (V := GraphIntegralVariables N)
        (integralGraphCoefficientDegree hG s))
      (integralGraphKoszulContraction hG s hs).h := by
  have hb : PolynomialPerturbation.tensorBasis (R := GraphIntegralCoefficientRing)
      (V := GraphIntegralVariables N) (IntegralGraphModule hG s) (integralGraphIdealBasis hG s) =
      idealTensorBasis (integralGraphParameterData hG s) := by
    unfold PolynomialPerturbation.tensorBasis integralGraphIdealBasis idealTensorBasis
    rfl
  have hd : PolynomialPerturbation.internalDegree (V := GraphIntegralVariables N)
      (integralGraphCoefficientDegree hG s) =
      idealTensorOrdinaryDegree (integralGraphParameterData hG s) := by
    funext a
    rfl
  rw [hb, hd]
  exact actualIdealTensorContraction_h_nonincreasing (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs)

/-- This is a constructed polynomial-linear differential and deformation
retract of the actual diagonal resolution onto the finite free model. -/
def integralGraphTransferredModel :
    LinearDeformationRetract (R := GraphIntegralPolynomialRing N)
      (M := PolynomialModuleResolution.Bar (R := GraphIntegralCoefficientRing)
        (V := GraphIntegralVariables N) (IntegralGraphModule hG s))
      (H := IntegralGraphFreeModel hG s) :=
  PolynomialPerturbation.transferred (R := GraphIntegralCoefficientRing)
    (V := GraphIntegralVariables N) (IntegralGraphModule hG s)
    (integralGraphKoszulContraction hG s hs) (integralGraphKoszulContraction_d hG s hs)
    (integralGraphIdealBasis hG s) (integralGraphCoefficientDegree hG s)
    (integralGraphKoszulContraction_h_nonincreasing hG s hs)

include hs in
/-- The target is finite free over the actual polynomial ring in x and y. -/
theorem integralGraphFreeModel_free :
    Module.Free (GraphIntegralPolynomialRing N) (IntegralGraphFreeModel hG s) := by
  letI := integralGraphHomology_free hG s hs
  exact Module.Free.of_basis ((Module.Free.chooseBasis GraphIntegralCoefficientRing
    (IntegralGraphHomology hG s)).baseChange (GraphIntegralPolynomialRing N))

include hs in
theorem integralGraphFreeModel_finite :
    Module.Finite (GraphIntegralPolynomialRing N) (IntegralGraphFreeModel hG s) := by
  letI := integralGraphHomology_free hG s hs
  letI := integralGraphHomology_finite hG s hs
  exact Module.Finite.of_basis ((Module.Free.chooseBasis GraphIntegralCoefficientRing
    (IntegralGraphHomology hG s)).baseChange (GraphIntegralPolynomialRing N))

def integralGraphAugmentation : IntegralGraphFreeModel hG s →ₗ[GraphIntegralPolynomialRing N]
    IntegralGraphModule hG s :=
  PolynomialPerturbation.augmentation (R := GraphIntegralCoefficientRing)
    (V := GraphIntegralVariables N) (IntegralGraphModule hG s)
    (integralGraphKoszulContraction hG s hs) (integralGraphKoszulContraction_d hG s hs)
    (integralGraphIdealBasis hG s) (integralGraphCoefficientDegree hG s)
    (integralGraphKoszulContraction_h_nonincreasing hG s hs)

def integralGraphSplitAugmentation :
    LinearDeformationRetract (R := GraphIntegralCoefficientRing)
      (M := IntegralGraphFreeModel hG s) (H := IntegralGraphModule hG s) :=
  PolynomialPerturbation.splitAugmentation (R := GraphIntegralCoefficientRing)
    (V := GraphIntegralVariables N) (IntegralGraphModule hG s)
    (integralGraphKoszulContraction hG s hs) (integralGraphKoszulContraction_d hG s hs)
    (integralGraphIdealBasis hG s) (integralGraphCoefficientDegree hG s)
    (integralGraphKoszulContraction_h_nonincreasing hG s hs)

theorem integralGraphSplitAugmentation_projection :
    (integralGraphSplitAugmentation hG s hs).projection =
      (integralGraphAugmentation hG s hs).restrictScalars GraphIntegralCoefficientRing :=
  PolynomialPerturbation.splitAugmentation_projection (R := GraphIntegralCoefficientRing)
    (V := GraphIntegralVariables N) (IntegralGraphModule hG s)
    (integralGraphKoszulContraction hG s hs) (integralGraphKoszulContraction_d hG s hs)
    (integralGraphIdealBasis hG s) (integralGraphCoefficientDegree hG s)
    (integralGraphKoszulContraction_h_nonincreasing hG s hs)

@[simp] theorem integralGraphSplitAugmentation_sourceD :
    (integralGraphSplitAugmentation hG s hs).sourceD =
      (integralGraphTransferredModel hG s hs).targetD.restrictScalars GraphIntegralCoefficientRing := rfl

@[simp] theorem integralGraphSplitAugmentation_targetD :
    (integralGraphSplitAugmentation hG s hs).targetD = 0 := rfl

theorem integralGraphAugmentation_surjective :
    Function.Surjective (integralGraphAugmentation hG s hs) := by
  intro x
  refine ⟨(integralGraphSplitAugmentation hG s hs).inclusion x, ?_⟩
  have he := LinearMap.congr_fun (integralGraphSplitAugmentation hG s hs).retract x
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    integralGraphSplitAugmentation_projection, LinearMap.restrictScalars_apply] using he

/-- Every actual cycle in the augmentation kernel has an explicit
boundary filling. This is the exactness identity for the total model. -/
theorem integralGraphModel_cycle_boundary (x : IntegralGraphFreeModel hG s)
    (hx : (integralGraphTransferredModel hG s hs).targetD x = 0)
    (hε : integralGraphAugmentation hG s hs x = 0) :
    ∃ y, (integralGraphTransferredModel hG s hs).targetD y = x := by
  let A := integralGraphSplitAugmentation hG s hs
  refine ⟨A.homotopy x, ?_⟩
  have hxA : A.sourceD x = 0 := hx
  have he := A.cycle_decomposition x hxA
  have hp : A.projection x = 0 := by
    change (integralGraphSplitAugmentation hG s hs).projection x = 0
    rw [integralGraphSplitAugmentation_projection]
    exact hε
  have hz : A.sourceD (A.homotopy x) = x := by
    simpa only [hp, map_zero, zero_add] using he.symm
  have hd := LinearMap.congr_fun (integralGraphSplitAugmentation_sourceD hG s hs)
    (A.homotopy x)
  exact hd.symm.trans hz

/-- Minimality is a literal coefficient statement in every target basis;
all entries belong to the polynomial-variable ideal over ℤ[z]. -/
theorem integralGraphModel_entries_in_variableIdeal {I : Type*}
    (b : Module.Basis I (GraphIntegralPolynomialRing N) (IntegralGraphFreeModel hG s))
    (i j : I) :
    b.repr ((integralGraphTransferredModel hG s hs).targetD (b i)) j ∈
      MvPolynomial.idealOfVars (GraphIntegralVariables N) GraphIntegralCoefficientRing :=
  PolynomialPerturbation.differential_entries_in_variableIdeal (R := GraphIntegralCoefficientRing)
    (V := GraphIntegralVariables N) (IntegralGraphModule hG s)
    (integralGraphKoszulContraction hG s hs) (integralGraphKoszulContraction_d hG s hs)
    (integralGraphIdealBasis hG s) (integralGraphCoefficientDegree hG s)
    (integralGraphKoszulContraction_h_nonincreasing hG s hs) b i j

/-- The explicit splitting tensors with any coefficient algebra, without
a flatness assumption. It is an actual deformation retract after base change. -/
def integralGraphSplitBaseChange (A : Type*) [CommRing A]
    [Algebra GraphIntegralCoefficientRing A] :
    LinearDeformationRetract (R := A)
      (M := A ⊗[GraphIntegralCoefficientRing] IntegralGraphFreeModel hG s)
      (H := A ⊗[GraphIntegralCoefficientRing] IntegralGraphModule hG s) :=
  (integralGraphSplitAugmentation hG s hs).baseChange A

end FourPapers.Sublattice

end
end
end


end
