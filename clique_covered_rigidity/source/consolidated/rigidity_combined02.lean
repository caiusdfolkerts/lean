module
import verification.internal.checkpoint
import verification.internal.extract
public import consolidated.pair_pin_progress01
import all consolidated.pair_pin_progress01
public import consolidated.pair_pin_progress02
import all consolidated.pair_pin_progress02
public import consolidated.rigidity_combined_prepared
import all consolidated.rigidity_combined_prepared
public import consolidated.rigidity_foundations01
import all consolidated.rigidity_foundations01
public import consolidated.rigidity_foundations02
import all consolidated.rigidity_foundations02
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Minimal
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityZheng_Incidence_PinOuterFullProvenanceHeightTransfer.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/PinOuterFullProvenanceHeightTransfer.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/





@[expose] public section

/-!
# Full-provenance transfer for the pin-outer active-height theorem

This file connects the concrete private-pin height calculation to the exact
finite-generic prime-height interface.  The route is explicit:

* contract a finite-generic prime through the pin-coefficient localization;
* swap the pin and twist polynomial layers;
* localize the selected angular product and split private from retained pins;
* use the actual compatibility equations to add two height units per active
  occurrence; and
* localize the retained coefficient prime at the complete pairwise-distinct
  factor.

Consequently the only remaining height input is the height of the selected
null ideal in the retained coefficient ring where both the angular and the
pairwise-distinct provenance factors are invertible.  No presentation map or
coordinate-change hypothesis is an input to the final theorem.
-/

namespace RB31E2E

namespace PinOuterFullProvenanceHeightTransfer

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open UniversalHomogeneousChart
open PinTriangularElimination
open TotalRingProvenanceSwap
open PinOuterActiveHeight
open ActivePinPrimeHeight
open UniversalActivePinHeightTransfer

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The complete provenance denominator in twist coefficients -/

/-- One grounded twist coordinate before adjoining any pin variables. -/
def coefficientGroundedCoordinate
    {V : Type*} [DecidableEq V] (root v : V)
    (c : TwistCoordinate) : TwistCoefficientRing root :=
  if c.1 then
    (coefficientGroundedTwist root v).2 c.2
  else
    (coefficientGroundedTwist root v).1 c.2

/-- A labelled body-difference coordinate in the twist coefficient ring. -/
def coefficientBodyDifferenceCoordinate
    {V : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    TwistCoefficientRing root :=
  coefficientGroundedCoordinate root uv.1.1 c -
    coefficientGroundedCoordinate root uv.1.2 c

/-- The complete pairwise-distinct factor before adjoining pin variables. -/
def coefficientDistinctnessDenominator
    {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V) :
    TwistCoefficientRing root :=
  ∏ uv : OrderedDistinctBodyPair V,
    coefficientBodyDifferenceCoordinate root uv (chart uv)

/-- The complete pairwise-distinct times active-angular coefficient product. -/
def coefficientIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) : TwistCoefficientRing root :=
  coefficientDistinctnessDenominator root distinctChart *
    activeAngularDenominator root src dst active angularChart

theorem totalRingSwapHom_universalGroundedCoordinate
    {V E : Type*} [DecidableEq V] (root v : V)
    (c : TwistCoordinate) :
    totalRingSwapHom (E := E) root
        (universalGroundedCoordinate (E := E) root v c) =
      C (coefficientGroundedCoordinate root v c) := by
  rcases c with ⟨b, i⟩
  cases b
  · have hswap := congrArg (fun Z ↦ Z.1 i)
      (map_universalGroundedTwist (E := E) root v)
    have hcoefficient := congrArg (fun Z ↦ Z.1 i)
      (pinOuterGroundedTwist_eq_map_coefficientGroundedTwist
        (E := E) root v)
    exact hswap.trans hcoefficient
  · have hswap := congrArg (fun Z ↦ Z.2 i)
      (map_universalGroundedTwist (E := E) root v)
    have hcoefficient := congrArg (fun Z ↦ Z.2 i)
      (pinOuterGroundedTwist_eq_map_coefficientGroundedTwist
        (E := E) root v)
    exact hswap.trans hcoefficient

theorem totalRingSwapHom_universalBodyDifferenceCoordinate
    {V E : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    totalRingSwapHom (E := E) root
        (universalBodyDifferenceCoordinate (E := E) root uv c) =
      C (coefficientBodyDifferenceCoordinate root uv c) := by
  rw [universalBodyDifferenceCoordinate,
    coefficientBodyDifferenceCoordinate, map_sub,
    totalRingSwapHom_universalGroundedCoordinate,
    totalRingSwapHom_universalGroundedCoordinate, map_sub]

theorem totalRingSwapHom_universalDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V) :
    totalRingSwapHom (E := E) root
        (universalDistinctnessDenominator (E := E) root chart) =
      C (coefficientDistinctnessDenominator root chart) := by
  rw [universalDistinctnessDenominator,
    coefficientDistinctnessDenominator, map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro uv _huv
  exact totalRingSwapHom_universalBodyDifferenceCoordinate
    (E := E) root uv (chart uv)

theorem coefficientBodyDifferenceCoordinate_active_eq
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (e : active) :
    coefficientBodyDifferenceCoordinate root
        ⟨(src e.1, dst e.1), hLoop e.1 e.2⟩
        ⟨false, angularChart e⟩ =
      activeAngularCoefficient
        root src dst active angularChart e := by
  rfl

theorem totalRingSwapHom_universalActiveAngularFactor
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (e : active) :
    totalRingSwapHom (E := E) root
        (universalActiveAngularFactor
          root src dst active hLoop angularChart e) =
      C (activeAngularCoefficient
        root src dst active angularChart e) := by
  rw [universalActiveAngularFactor,
    totalRingSwapHom_universalBodyDifferenceCoordinate]
  exact congrArg C
    (coefficientBodyDifferenceCoordinate_active_eq
      root src dst active hLoop angularChart e)

theorem totalRingSwapHom_universalAngularDenominator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) :
    totalRingSwapHom (E := E) root
        (universalAngularDenominator
          root src dst active hLoop angularChart) =
      C (activeAngularDenominator
        root src dst active angularChart) := by
  rw [universalAngularDenominator, activeAngularDenominator,
    map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro e _he
  exact totalRingSwapHom_universalActiveAngularFactor
    root src dst active hLoop angularChart e

/-- The full denominator really is coefficient-valued after the total-ring
swap; no pin variable is hidden in the localization factor. -/
theorem totalRingSwapHom_universalIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) :
    totalRingSwapHom (E := E) root
        (universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart) =
      C (coefficientIncidenceProvenanceDenominator
        root src dst active distinctChart angularChart) := by
  rw [universalIncidenceProvenanceDenominator,
    coefficientIncidenceProvenanceDenominator, map_mul,
    totalRingSwapHom_universalDistinctnessDenominator,
    totalRingSwapHom_universalAngularDenominator, map_mul]

/-! ## The selected-null ideal in retained coefficients -/

theorem map_splitKlein_local
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Z : Twist R) :
    f (Twist.splitKlein Z) =
      Twist.splitKlein (mapTwist f Z) := by
  simp [Twist.splitKlein, Vec3.dot, mapTwist, mapVec3]

/-- A selected null equation after angular localization and absorption of
all non-private pin variables into the coefficient ring. -/
def retainedNullEquation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (e : E) :
    RetainedCoefficientRing root src dst active angularChart :=
  Twist.splitKlein
    (retainedRelativeTwist root src dst active angularChart e)

theorem localizedPrivatePresentationHom_universalNullEquation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (e : E) :
    localizedPrivatePresentationHom
        root src dst active angularChart
        (universalNullEquation root src dst e) =
      (C (retainedNullEquation
        root src dst active angularChart e) :
        PrivatePresentationRing root src dst active angularChart) := by
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let f := localizedPrivatePresentationHom
    root src dst active angularChart
  have htwist : mapTwist f
      (universalRelativeTwist root src dst e) =
      mapTwist (C : RetainedCoefficientRing
          root src dst active angularChart →+*
          PrivatePresentationRing
            root src dst active angularChart)
        (retainedRelativeTwist
          root src dst active angularChart e) := by
    apply Prod.ext <;> funext i
    · exact localizedPrivatePresentationHom_relativeTwist_angular
        root src dst active angularChart e i
    · exact localizedPrivatePresentationHom_relativeTwist_translational
        root src dst active angularChart e i
  rw [universalNullEquation, map_splitKlein_local, htwist]
  exact (map_splitKlein_local
    (C : RetainedCoefficientRing
        root src dst active angularChart →+*
        PrivatePresentationRing root src dst active angularChart)
    (retainedRelativeTwist
      root src dst active angularChart e)).symm

/-- The selected-null ideal before the private polynomial variables are
adjoined. -/
def retainedSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    Ideal (RetainedCoefficientRing
      root src dst active angularChart) :=
  Ideal.span (Set.range (fun e : SelectedOccurrence active selected ↦
    retainedNullEquation
      root src dst active angularChart e.1.1))

/-- Mapping the literal universal selected-null ideal lands exactly in the
constant extension of the retained selected-null ideal. -/
theorem map_selectedNullIdeal_eq_map_C_retainedSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    Ideal.map
        (localizedPrivatePresentationHom
          root src dst active angularChart)
        (Ideal.span
          (selectedNullGeneratorSet
            root src dst active selected)) =
      Ideal.map
        (C : RetainedCoefficientRing
            root src dst active angularChart →+*
          PrivatePresentationRing
            root src dst active angularChart)
        (retainedSelectedNullIdeal
          root src dst active angularChart selected) := by
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  rw [Ideal.map_span, retainedSelectedNullIdeal, Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨e, rfl⟩, rfl⟩
    exact ⟨retainedNullEquation
        root src dst active angularChart e.1.1,
        ⟨⟨e, rfl⟩,
        (localizedPrivatePresentationHom_universalNullEquation
          root src dst active angularChart e.1.1).symm⟩⟩
  · rintro ⟨g, ⟨e, rfl⟩, rfl⟩
    exact ⟨selectedNullGenerator root src dst active selected e,
        ⟨⟨e, rfl⟩,
        localizedPrivatePresentationHom_universalNullEquation
          root src dst active angularChart e.1.1⟩⟩

/-! ## Pairwise-distinct localization after the angular chart -/

/-- The pairwise-distinct factor inside the retained coefficient ring. -/
def retainedDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (distinctChart : DistinctnessChart V) :
    RetainedCoefficientRing root src dst active angularChart :=
  C (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization
        root src dst active angularChart)
      (coefficientDistinctnessDenominator root distinctChart))

/-- Retained coefficients on the chart where both angular and complete
pairwise-distinct provenance factors are invertible. -/
abbrev IncidenceLocalizedRetainedCoefficientRing
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (distinctChart : DistinctnessChart V) :=
  Localization.Away
    (retainedDistinctnessDenominator
      root src dst active angularChart distinctChart)

/-- The sole remaining ideal after both provenance localizations. -/
def incidenceLocalizedSelectedNullIdeal
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V) :
    Ideal (IncidenceLocalizedRetainedCoefficientRing
      root src dst active angularChart distinctChart) :=
  Ideal.map
    (algebraMap
      (RetainedCoefficientRing root src dst active angularChart)
      (IncidenceLocalizedRetainedCoefficientRing
        root src dst active angularChart distinctChart))
    (retainedSelectedNullIdeal
      root src dst active angularChart selected)

/-- The Krull height of the preceding ideal, packaged with one coherent
choice of commutative-ring instances for the iterated polynomial
localizations. -/
def incidenceLocalizedSelectedNullIdealHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V) : ℕ∞ :=
  let R := RetainedCoefficientRing
    root src dst active angularChart
  letI : CommRing R := inferInstance
  let d : R := retainedDistinctnessDenominator
    root src dst active angularChart distinctChart
  let T := Localization.Away d
  letI : CommRing T := inferInstance
  let I : Ideal R := Ideal.span
    (Set.range (fun e : SelectedOccurrence active selected ↦
      retainedNullEquation
        root src dst active angularChart e.1.1))
  let J : Ideal T := Ideal.map (algebraMap R T) I
  J.height

/-! ## Height-preserving changes of presentation -/

/-- Contracting through generic pin coefficients and undoing the finite
twist reindexing preserves ideal height.  This is the precise bridge from
the finite-generic presentation back to the original total ring. -/
theorem finiteGenericChartHom_height_comap
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (Q : Ideal (FiniteGenericRelativeRing root E)) :
    (Ideal.comap (finiteGenericChartHom root) Q).height = Q.height := by
  let e := MvPolynomial.renameEquiv (GenericPinCoefficientField E)
    (finiteTwistIndexEquiv root)
  let Qg : Ideal (GenericRelativeRing root E) :=
    Ideal.comap e.toRingEquiv.toRingHom Q
  change (Ideal.comap (genericCoefficientExtensionHom root) Qg).height =
    Q.height
  calc
    (Ideal.comap (genericCoefficientExtensionHom root) Qg).height =
        Qg.height := by
      change (Ideal.comap
        (algebraMap (RelativeRing root E)
          (GenericRelativeRing root E)) Qg).height = Qg.height
      exact IsLocalization.height_comap
        ((nonZeroDivisors (PinParameterRing E)).map
          (C : PinParameterRing E →+* RelativeRing root E)) Qg
    _ = Q.height := by
      exact RingEquiv.height_comap e.toRingEquiv Q

/-- Avoiding the selected angular product is exactly the disjointness needed
to localize the pin-outer ring coefficientwise. -/
theorem localizedSplitPinOuterHom_height_map
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (P : Ideal (PinOuterRing root E)) [P.IsPrime]
    (hAngular :
      C (activeAngularDenominator
        root src dst active angularChart) ∉ P) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active angularChart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active angularChart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active angularChart) := inferInstance
    (Ideal.map
      (localizedSplitPinOuterHom
        root src dst active angularChart) P).height = P.height := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active angularChart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active angularChart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let A := AngularCoefficientLocalization
    root src dst active angularChart
  letI : CommRing A := inferInstance
  letI : CommRing (MvPolynomial (PinVariable E) A) := inferInstance
  let f : PinOuterRing root E →+* MvPolynomial (PinVariable E) A :=
    MvPolynomial.map
      (algebraMap (TwistCoefficientRing root) A)
  let Pangular : Ideal (MvPolynomial (PinVariable E) A) :=
    Ideal.map f P
  have hdisj : Disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E) : Set (PinOuterRing root E))
      (P : Set (PinOuterRing root E)) := by
    rw [Submonoid.map_powers]
    exact (Ideal.disjoint_powers_iff_notMem
      (C (activeAngularDenominator
        root src dst active angularChart))
      (Ideal.IsPrime.isRadical inferInstance)).2 hAngular
  have hlocalization : Pangular.height = P.height := by
    change (Ideal.map
      (algebraMap (PinOuterRing root E)
        (MvPolynomial (PinVariable E) A)) P).height = P.height
    exact IsLocalization.height_map_of_disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E)) P hdisj
  rw [localizedSplitPinOuterHom, ← Ideal.map_map]
  change (Ideal.map
    (splitPinVariables (A := A) active angularChart).toRingEquiv.toRingHom
    Pangular).height = P.height
  exact (RingEquiv.height_map
    (splitPinVariables (A := A) active angularChart).toRingEquiv
    Pangular).trans hlocalization

/-- The angular-localized private-presentation image of a disjoint prime is
again prime. -/
theorem localizedSplitPinOuterHom_isPrime
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (P : Ideal (PinOuterRing root E)) [P.IsPrime]
    (hAngular :
      C (activeAngularDenominator
        root src dst active angularChart) ∉ P) :
    (Ideal.map
      (localizedSplitPinOuterHom
        root src dst active angularChart) P).IsPrime := by
  let A := AngularCoefficientLocalization
    root src dst active angularChart
  let f : PinOuterRing root E →+* MvPolynomial (PinVariable E) A :=
    MvPolynomial.map
      (algebraMap (TwistCoefficientRing root) A)
  let Pangular : Ideal (MvPolynomial (PinVariable E) A) :=
    Ideal.map f P
  have hdisj : Disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E) : Set (PinOuterRing root E))
      (P : Set (PinOuterRing root E)) := by
    rw [Submonoid.map_powers]
    exact (Ideal.disjoint_powers_iff_notMem
      (C (activeAngularDenominator
        root src dst active angularChart))
      (Ideal.IsPrime.isRadical inferInstance)).2 hAngular
  letI : Pangular.IsPrime := by
    change (Ideal.map
      (algebraMap (PinOuterRing root E)
        (MvPolynomial (PinVariable E) A)) P).IsPrime
    exact IsLocalization.isPrime_of_isPrime_disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E))
      (MvPolynomial (PinVariable E) A) P inferInstance hdisj
  rw [localizedSplitPinOuterHom, ← Ideal.map_map]
  exact Ideal.map_isPrime_of_equiv
    (splitPinVariables (A := A) active angularChart).toRingEquiv

/-- Avoidance of the complete coefficient product implies avoidance of its
angular factor. -/
theorem angularDenominator_not_mem_of_incidenceDenominator_not_mem
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3)
    (P : Ideal (PinOuterRing root E))
    (hfull : C (coefficientIncidenceProvenanceDenominator
      root src dst active distinctChart angularChart) ∉ P) :
    C (activeAngularDenominator
      root src dst active angularChart) ∉ P := by
  intro hAngular
  apply hfull
  rw [coefficientIncidenceProvenanceDenominator, map_mul]
  exact P.mul_mem_left _ hAngular

/-- Avoidance of the complete coefficient product also implies avoidance of
its pairwise-distinct factor. -/
theorem distinctnessDenominator_not_mem_of_incidenceDenominator_not_mem
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3)
    (P : Ideal (PinOuterRing root E))
    (hfull : C (coefficientIncidenceProvenanceDenominator
      root src dst active distinctChart angularChart) ∉ P) :
    C (coefficientDistinctnessDenominator
      root distinctChart) ∉ P := by
  intro hDistinct
  apply hfull
  rw [coefficientIncidenceProvenanceDenominator, map_mul]
  exact P.mul_mem_right _ hDistinct

/-! ## Literal source-ideal bridges -/

/-- Each sign-oriented compatibility equation is one of the two literal
active compatibility generators, up to multiplication by `-1`. -/
theorem universalOrientedCompatibilityEquation_mem_activeCompatibilityIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (q : active × Fin 2) :
    universalOrientedCompatibilityEquation
        root src dst q.1.1 (angularChart q.1) q.2 ∈
      activeCompatibilityIdeal
        root src dst active angularChart := by
  have hne_general (i : Fin 3) (slot : Fin 2) :
      solvingCompatibilityCoordinate i slot ≠ i := by
    fin_cases i <;> fin_cases slot <;> decide
  have hne : solvingCompatibilityCoordinate
      (angularChart q.1) q.2 ≠ angularChart q.1 :=
    hne_general (angularChart q.1) q.2
  let a : ActiveCompatibilityIndex active angularChart :=
    ⟨q.1, ⟨solvingCompatibilityCoordinate
      (angularChart q.1) q.2, hne⟩⟩
  have hgenerator : universalCompatibilityCoordinate
      root src dst q.1.1
        (solvingCompatibilityCoordinate (angularChart q.1) q.2) ∈
      activeCompatibilityIdeal
        root src dst active angularChart := by
    change activeCompatibilityGenerator
      root src dst active angularChart a ∈
        activeCompatibilityIdeal root src dst active angularChart
    exact Ideal.subset_span ⟨a, rfl⟩
  rcases universalTriangularResidual_eq_compatibility_or_neg
      root src dst q.1.1 (angularChart q.1) q.2 with h | h
  · rw [universalTriangularResidual_eq_orientedCompatibilityEquation]
      at h
    rw [h]
    exact hgenerator
  · rw [universalTriangularResidual_eq_orientedCompatibilityEquation]
      at h
    rw [h]
    exact (activeCompatibilityIdeal
      root src dst active angularChart).neg_mem hgenerator

theorem activeCompatibilityIdeal_le_universalChartIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    activeCompatibilityIdeal root src dst active angularChart ≤
      universalChartIdeal
        root src dst active angularChart selected := by
  rw [activeCompatibilityIdeal, universalChartIdeal,
    universalChartGeneratorSet, Ideal.span_union]
  exact le_sup_left

theorem selectedNullIdeal_le_universalChartIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    Ideal.span (selectedNullGeneratorSet
        root src dst active selected) ≤
      universalChartIdeal
        root src dst active angularChart selected := by
  rw [universalChartIdeal, universalChartGeneratorSet,
    Ideal.span_union]
  exact le_sup_right

/-- The concrete localized active ideal is generated by images of literal
source-chart generators. -/
theorem localizedActiveCompatibilityIdeal_le_map_activeCompatibilityIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) :
    localizedActiveCompatibilityIdeal
        root src dst active angularChart ≤
      Ideal.map
        (localizedPrivatePresentationHom
          root src dst active angularChart)
        (activeCompatibilityIdeal
          root src dst active angularChart) := by
  rw [localizedActiveCompatibilityIdeal, Ideal.span_le]
  rintro _ ⟨q, rfl⟩
  exact Ideal.mem_map_of_mem _
    (universalOrientedCompatibilityEquation_mem_activeCompatibilityIdeal
      root src dst active angularChart q)

/-- A polynomial avoided by a prime before angular localization remains
avoided after the coefficient localization and variable-splitting
equivalence. -/
theorem localizedSplitPinOuterHom_not_mem_map_of_not_mem
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (P : Ideal (PinOuterRing root E)) [P.IsPrime]
    (hAngular : C (activeAngularDenominator
      root src dst active angularChart) ∉ P)
    (x : PinOuterRing root E) (hx : x ∉ P) :
    localizedSplitPinOuterHom
        root src dst active angularChart x ∉
      Ideal.map
        (localizedSplitPinOuterHom
          root src dst active angularChart) P := by
  let A := AngularCoefficientLocalization
    root src dst active angularChart
  let f : PinOuterRing root E →+* MvPolynomial (PinVariable E) A :=
    MvPolynomial.map
      (algebraMap (TwistCoefficientRing root) A)
  let e := (splitPinVariables
    (A := A) active angularChart).toRingEquiv
  let Pangular : Ideal (MvPolynomial (PinVariable E) A) :=
    Ideal.map f P
  have hdisj : Disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E) : Set (PinOuterRing root E))
      (P : Set (PinOuterRing root E)) := by
    rw [Submonoid.map_powers]
    exact (Ideal.disjoint_powers_iff_notMem
      (C (activeAngularDenominator
        root src dst active angularChart))
      (Ideal.IsPrime.isRadical inferInstance)).2 hAngular
  have hcomap : Ideal.comap f Pangular = P := by
    change Ideal.comap
      (algebraMap (PinOuterRing root E)
        (MvPolynomial (PinVariable E) A))
      (Ideal.map
        (algebraMap (PinOuterRing root E)
          (MvPolynomial (PinVariable E) A)) P) = P
    exact IsLocalization.comap_map_of_isPrime_disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E))
      (MvPolynomial (PinVariable E) A) inferInstance hdisj
  intro hxmap
  have hefx : e (f x) ∈ Ideal.map e Pangular := by
    change e (f x) ∈ Ideal.map (e.toRingHom.comp f) P at hxmap
    rw [← Ideal.map_map] at hxmap
    exact hxmap
  have hfx : f x ∈ Pangular := by
    have hback := (Ideal.symm_apply_mem_of_equiv_iff
      (I := Pangular) (f := e) (y := e (f x))).2 hefx
    simpa using hback
  apply hx
  rw [← hcomap]
  exact hfx

/-! ## Unconditional relative height of the actual compatibility summand -/

/-- In the concrete angular pin-outer presentation, every prime containing
the actual active compatibility ideal has at least two height units per
active occurrence above its retained-coefficient contraction. -/
theorem privatePresentation_prime_height_ge_coefficientContraction_add_twice_card
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (Q : Ideal (PrivatePresentationRing
      root src dst active angularChart)) [Q.IsPrime]
    (hcompat : localizedActiveCompatibilityIdeal
      root src dst active angularChart ≤ Q) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active angularChart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active angularChart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : IsDomain (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active angularChart) := inferInstance
    (Ideal.comap
        (C : RetainedCoefficientRing
            root src dst active angularChart →+*
          PrivatePresentationRing
            root src dst active angularChart) Q).height +
        (2 * active.card : ℕ) ≤ Q.height := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active angularChart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active angularChart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let R := RetainedCoefficientRing
    root src dst active angularChart
  let S := PrivatePresentationRing
    root src dst active angularChart
  let P : Ideal R := Ideal.comap (C : R →+* S) Q
  letI : P.IsPrime := by
    dsimp [P]
    exact Ideal.comap_isPrime _ _
  let c : Fin (active.card * 2) → ActivePrivatePin active angularChart :=
    activePrivateEnumeration active angularChart
  let a : ActivePrivatePin active angularChart → R :=
    activePrivateTranslation root src dst active angularChart
  let I₀ : Ideal S :=
    basePrimeCoordinateIdeal P (Set.range c)
  let τ : S ≃+* S :=
    (coordinateTranslationEquiv (fun x ↦ -a x)).toRingEquiv
  let Iₜ : Ideal S := Ideal.map τ I₀
  have hconstant : Ideal.map τ
      (Ideal.map (C : R →+* S) P) =
      Ideal.map (C : R →+* S) P := by
    rw [show Ideal.map τ
          (Ideal.map (C : R →+* S) P) =
        Ideal.map (τ.toRingHom.comp C) P by
          exact Ideal.map_map C τ.toRingHom]
    congr 1
    apply DFunLike.ext _ _
    intro r
    exact coordinateTranslationEquiv_C (fun x ↦ -a x) r
  have htranslated : Iₜ =
      Ideal.map (C : R →+* S) P ⊔
        translatedCoordinateIdeal c a := by
    dsimp [Iₜ, I₀]
    rw [basePrimeCoordinateIdeal, Ideal.map_sup,
      hconstant]
    congr 1
    exact (translatedCoordinateIdeal_eq_map_coordinateVariableIdeal
      c a).symm
  have hnormalized : activeNormalizedPrivateIdeal
      root src dst active angularChart ≤ Q := by
    rw [← localizedActiveCompatibilityIdeal_eq_activeNormalizedPrivateIdeal
      root src dst active angularChart hLoop]
    exact hcompat
  have htranslated_le : translatedCoordinateIdeal c a ≤ Q := by
    exact (translatedCoordinateIdeal_le_activeNormalizedPrivateIdeal
      root src dst active angularChart hLoop).trans hnormalized
  have hIₜ : Iₜ ≤ Q := by
    rw [htranslated]
    apply sup_le
    · exact Ideal.map_comap_le
    · exact htranslated_le
  have hI₀ : P.height + (active.card * 2 : ℕ) ≤ I₀.height := by
    exact basePrimeCoordinateIdeal_height_ge_add_card
      P c (activePrivateEnumeration_injective active angularChart)
  calc
    P.height + (2 * active.card : ℕ) =
        P.height + (active.card * 2 : ℕ) := by
      rw [Nat.mul_comm]
    _ ≤ I₀.height := hI₀
    _ = Iₜ.height := (RingEquiv.height_map τ I₀).symm
    _ ≤ Q.height := Ideal.height_mono hIₜ

/-! ## Reduction to the selected-null height statement -/

/-- The complete finite-generic provenance height condition follows from
one presentation-invariant statement: the selected null ideal has its
expected height after localizing the retained coefficient ring at both the
active-angular and complete pairwise-distinct factors.

The preceding comparison theorems account for all changes of presentation
and for the `2 * active.card` contribution of the compatibility equations. -/
theorem finiteGenericIncidenceProvenancePrimeHeightCondition_of_incidenceLocalizedSelectedNullIdeal_height
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hcard : selected.card =
      6 * (Fintype.card V - 1) - 2 * active.card)
    (hselected : (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart) :
    FiniteGenericIncidenceProvenancePrimeHeightCondition
      root src dst active hLoop angularChart selected distinctChart := by
  intro Q hQprime _hQhom hchart hdenominator
  letI : Q.IsPrime := hQprime
  let P₀ : Ideal (RelativeRing root E) :=
    Ideal.comap (finiteGenericChartHom root) Q
  letI : P₀.IsPrime := by
    dsimp [P₀]
    exact Ideal.comap_isPrime _ _
  let swap : RelativeRing root E ≃+* PinOuterRing root E :=
    (totalRingSwap (E := E) root).toRingEquiv
  let P₁ : Ideal (PinOuterRing root E) := Ideal.map swap P₀
  letI : P₁.IsPrime := by
    dsimp [P₁]
    exact Ideal.map_isPrime_of_equiv swap
  have hfullP₀ : universalIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart ∉ P₀ := by
    simpa [P₀, finiteGenericIncidenceProvenanceDenominator] using
      hdenominator
  have hfullP₁ : C (coefficientIncidenceProvenanceDenominator
      root src dst active distinctChart angularChart) ∉ P₁ := by
    intro hx
    have hback := (Ideal.symm_apply_mem_of_equiv_iff
      (I := P₀) (f := swap)
      (y := C (coefficientIncidenceProvenanceDenominator
        root src dst active distinctChart angularChart))).2 hx
    have hswap :=
      totalRingSwapHom_universalIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart
    have hinverse : swap.symm
        (C (coefficientIncidenceProvenanceDenominator
          root src dst active distinctChart angularChart)) =
        universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart := by
      rw [← hswap]
      change swap.symm (swap
        (universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart)) = _
      exact swap.symm_apply_apply _
    apply hfullP₀
    simpa [hinverse] using hback
  have hAngular : C (activeAngularDenominator
      root src dst active angularChart) ∉ P₁ :=
    angularDenominator_not_mem_of_incidenceDenominator_not_mem
      root src dst active distinctChart angularChart P₁ hfullP₁
  have hDistinctSource : C (coefficientDistinctnessDenominator
      root distinctChart) ∉ P₁ :=
    distinctnessDenominator_not_mem_of_incidenceDenominator_not_mem
      root src dst active distinctChart angularChart P₁ hfullP₁
  let P₂ : Ideal (PrivatePresentationRing
      root src dst active angularChart) :=
    Ideal.map
      (localizedSplitPinOuterHom
        root src dst active angularChart) P₁
  letI : P₂.IsPrime := by
    dsimp [P₂]
    exact localizedSplitPinOuterHom_isPrime
      root src dst active angularChart P₁ hAngular
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active angularChart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active angularChart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let R := RetainedCoefficientRing
    root src dst active angularChart
  let Cₚ : R →+* PrivatePresentationRing
      root src dst active angularChart := C
  let Pcoeff : Ideal R := Ideal.comap Cₚ P₂
  letI : Pcoeff.IsPrime := by
    dsimp [Pcoeff]
    exact Ideal.comap_isPrime _ _
  have hsource : universalChartIdeal
      root src dst active angularChart selected ≤ P₀ := by
    intro f hf
    change finiteGenericChartHom root f ∈ Q
    exact hchart (Ideal.mem_map_of_mem _ hf)
  have hactiveSource : activeCompatibilityIdeal
      root src dst active angularChart ≤ P₀ :=
    (activeCompatibilityIdeal_le_universalChartIdeal
      root src dst active angularChart selected).trans hsource
  have hselectedSource : Ideal.span
      (selectedNullGeneratorSet root src dst active selected) ≤ P₀ :=
    (selectedNullIdeal_le_universalChartIdeal
      root src dst active angularChart selected).trans hsource
  have himage : Ideal.map
      (localizedPrivatePresentationHom
        root src dst active angularChart) P₀ = P₂ := by
    dsimp [P₂, P₁]
    rw [localizedPrivatePresentationHom, ← Ideal.map_map]
    rfl
  have hmappedActive : Ideal.map
      (localizedPrivatePresentationHom
        root src dst active angularChart)
      (activeCompatibilityIdeal
        root src dst active angularChart) ≤ P₂ := by
    rw [← himage]
    exact Ideal.map_mono hactiveSource
  have hcompat : localizedActiveCompatibilityIdeal
      root src dst active angularChart ≤ P₂ :=
    (localizedActiveCompatibilityIdeal_le_map_activeCompatibilityIdeal
      root src dst active angularChart).trans hmappedActive
  let Iselected : Ideal R := Ideal.span
    (Set.range (fun e : SelectedOccurrence active selected ↦
      retainedNullEquation
        root src dst active angularChart e.1.1))
  have hretainedSelected : Iselected ≤ Pcoeff := by
    dsimp [Iselected]
    rw [Ideal.span_le]
    rintro _ ⟨e, rfl⟩
    change C (retainedNullEquation
      root src dst active angularChart e.1.1) ∈ P₂
    rw [← localizedPrivatePresentationHom_universalNullEquation
      root src dst active angularChart e.1.1, ← himage]
    exact Ideal.mem_map_of_mem _
      (hselectedSource (Ideal.subset_span ⟨e, rfl⟩))
  have hrelative : Pcoeff.height + (2 * active.card : ℕ) ≤
      P₂.height := by
    simpa [Pcoeff, Cₚ, R] using
      (privatePresentation_prime_height_ge_coefficientContraction_add_twice_card
        root src dst active angularChart hLoop P₂ hcompat)
  have hP₀height : P₀.height = Q.height := by
    exact finiteGenericChartHom_height_comap root Q
  have hP₁height : P₁.height = P₀.height := by
    exact RingEquiv.height_map swap P₀
  have hP₂height : P₂.height = P₁.height := by
    exact localizedSplitPinOuterHom_height_map
      root src dst active angularChart hLoop P₁ hAngular
  have hP₂heightQ : P₂.height = Q.height :=
    hP₂height.trans (hP₁height.trans hP₀height)
  have hDistinctAfterAngular :=
    localizedSplitPinOuterHom_not_mem_map_of_not_mem
      root src dst active angularChart P₁ hAngular
        (C (coefficientDistinctnessDenominator root distinctChart))
        hDistinctSource
  have hretainedDistinct : retainedDistinctnessDenominator
      root src dst active angularChart distinctChart ∉ Pcoeff := by
    intro hx
    apply hDistinctAfterAngular
    change C (retainedDistinctnessDenominator
      root src dst active angularChart distinctChart) ∈ P₂ at hx
    simpa [P₂, retainedDistinctnessDenominator] using hx
  let d : R := retainedDistinctnessDenominator
    root src dst active angularChart distinctChart
  let T := Localization.Away d
  let Pfull : Ideal T := Ideal.map
    (algebraMap R T) Pcoeff
  have hdisjDistinct : Disjoint
      (Submonoid.powers d : Set R)
      (Pcoeff : Set R) :=
    (Ideal.disjoint_powers_iff_notMem
      d
      (Ideal.IsPrime.isRadical inferInstance)).2 hretainedDistinct
  have hPfullHeight : Pfull.height = Pcoeff.height := by
    dsimp [Pfull, T]
    exact IsLocalization.height_map_of_disjoint
      (Submonoid.powers d)
      Pcoeff hdisjDistinct
  let Ifull : Ideal T := Ideal.map (algebraMap R T) Iselected
  have hselectedFull : Ifull ≤ Pfull := by
    dsimp [Ifull, Pfull]
    exact Ideal.map_mono hretainedSelected
  have hselectedHeight : (selected.card : ℕ∞) ≤ Ifull.height := by
    simpa [incidenceLocalizedSelectedNullIdealHeight, R, d, T,
      Iselected, Ifull] using hselected
  have hselectedCoeff : (selected.card : ℕ∞) ≤ Pcoeff.height := by
    calc
      (selected.card : ℕ∞) ≤ Ifull.height := hselectedHeight
      _ ≤ Pfull.height := Ideal.height_mono hselectedFull
      _ = Pcoeff.height := hPfullHeight
  have hbudget := universalChartGenerator_budget
    root active angularChart selected hcard
  rw [card_activeCompatibilityIndex] at hbudget
  have hbudgetTop : (groundedTwistVariableCount root : ℕ∞) ≤
      ((2 * active.card + selected.card : ℕ) : ℕ∞) := by
    exact_mod_cast hbudget
  calc
    (groundedTwistVariableCount root : ℕ∞) ≤
        ((2 * active.card + selected.card : ℕ) : ℕ∞) := hbudgetTop
    _ = (selected.card : ℕ∞) + (2 * active.card : ℕ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (add_comm (2 * (active.card : ℕ∞))
          (selected.card : ℕ∞))
    _ ≤ Pcoeff.height + (2 * active.card : ℕ) := by
      simpa [add_comm] using
        (add_le_add_right hselectedCoeff
          (2 * active.card : ℕ∞))
    _ ≤ P₂.height := hrelative
    _ = Q.height := hP₂heightQ

end

end PinOuterFullProvenanceHeightTransfer

end RB31E2E


end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0001/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0001.json"

section BundleSource0002
/- Source: Papers/RigidityZheng_NullCellule_SelectedNullHeight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/SelectedNullHeight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/





@[expose] public section

/-!
# Selected Split--Klein null height from a function-field budget

This file isolates the commutative-algebra part of the direct
semismallness-to-height argument.  The selected null equations are first
defined literally in the grounded twist polynomial ring.  We then prove
that the target ideal is obtained from this ideal by exactly three standard
operations:

* localization at the active angular denominator;
* adjoining the retained pin variables, which are polynomial spectators;
* localization at the complete distinctness denominator.

Minimal primes and their heights are transported through all three steps.
The sole input of the public theorem is a function-field dimension budget
for the surviving minimal primes of the literal grounded selected-null
ideal.  It is a theorem parameter, not a field of an opaque structure.
-/

namespace RB31E2E

namespace SelectedNullHeight

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open PinOuterFullProvenanceHeightTransfer
open PolynomialPrimeTrdegHeight
open UniversalHomogeneousChart

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The literal grounded selected-null ideal -/

/-- One selected Split--Klein null equation before either localization and
before any retained pin variables are adjoined. -/
def coefficientNullEquation
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) :
    TwistCoefficientRing root :=
  Twist.splitKlein (coefficientRelativeTwist root src dst e)

/-- The selected null ideal in the literal grounded twist polynomial ring. -/
def coefficientSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) : Ideal (TwistCoefficientRing root) :=
  Ideal.span (Set.range (fun e : SelectedOccurrence active selected ↦
    coefficientNullEquation root src dst e.1.1))

/-- Generalized Krull height theorem for a minimal prime of the literal
selected-null ideal. -/
theorem coefficientMinimalPrime_height_le_selectedCard
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active)
    (P : Ideal (TwistCoefficientRing root))
    (hP : P ∈ (coefficientSelectedNullIdeal
      root src dst active selected).minimalPrimes) :
    P.height ≤ (selected.card : ℕ∞) := by
  classical
  let g : SelectedOccurrence active selected →
      TwistCoefficientRing root :=
    fun e ↦ coefficientNullEquation root src dst e.1.1
  have hPspan :
      P ∈ (Ideal.span (Set.range g)).minimalPrimes := by
    simpa only [coefficientSelectedNullIdeal, g] using hP
  have hKrull :
      P.height ≤ ((Set.range g).ncard : ℕ∞) :=
    Ideal.height_le_card_of_mem_minimalPrimes_span
      (Set.finite_range g) hPspan
  have hncard : (Set.range g).ncard ≤ selected.card := by
    rw [← Set.image_univ]
    simpa using Set.ncard_image_le (f := g) (s := Set.univ)
  exact hKrull.trans (by exact_mod_cast hncard)

/-- The same ideal after the active-angular localization. -/
def angularSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    Ideal (AngularCoefficientLocalization
      root src dst active angularChart) :=
  Ideal.map
    (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active angularChart))
    (coefficientSelectedNullIdeal root src dst active selected)

theorem algebraMap_coefficientNullEquation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (e : E) :
    algebraMap (TwistCoefficientRing root)
        (AngularCoefficientLocalization root src dst active angularChart)
        (coefficientNullEquation root src dst e) =
      Twist.splitKlein
        (localizedCoefficientRelativeTwist
          root src dst active angularChart e) := by
  rw [coefficientNullEquation, localizedCoefficientRelativeTwist,
    map_splitKlein_local]

theorem C_algebraMap_coefficientNullEquation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (e : E) :
    C (algebraMap (TwistCoefficientRing root)
        (AngularCoefficientLocalization root src dst active angularChart)
        (coefficientNullEquation root src dst e)) =
      retainedNullEquation root src dst active angularChart e := by
  letI : CommRing (AngularCoefficientLocalization
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  rw [algebraMap_coefficientNullEquation]
  exact map_splitKlein_local
    (C : AngularCoefficientLocalization
        root src dst active angularChart →+*
      RetainedCoefficientRing root src dst active angularChart)
    (localizedCoefficientRelativeTwist
      root src dst active angularChart e)

/-- The retained selected-null ideal is exactly the constant polynomial
extension of the angular-localized literal ideal. -/
theorem retainedSelectedNullIdeal_eq_map_C_angularSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    retainedSelectedNullIdeal root src dst active angularChart selected =
      Ideal.map
        (C : AngularCoefficientLocalization
            root src dst active angularChart →+*
          RetainedCoefficientRing root src dst active angularChart)
        (angularSelectedNullIdeal
          root src dst active angularChart selected) := by
  rw [retainedSelectedNullIdeal, angularSelectedNullIdeal,
    coefficientSelectedNullIdeal, Ideal.map_map, Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨coefficientNullEquation root src dst e.1.1, ⟨e, rfl⟩, ?_⟩
    simpa using C_algebraMap_coefficientNullEquation
      root src dst active angularChart e.1.1
  · rintro ⟨g, ⟨e, rfl⟩, rfl⟩
    refine ⟨e, ?_⟩
    simpa using (C_algebraMap_coefficientNullEquation
      root src dst active angularChart e.1.1).symm

/-! ## Polynomial spectators -/

/-- A minimal prime of a constant polynomial extension is itself the
constant extension of its contraction.  In particular, the contraction is
a minimal prime of the original ideal. -/
theorem minimalPrime_map_C_contract
    {A τ : Type*} [CommRing A]
    (I : Ideal A) (Q : Ideal (MvPolynomial τ A))
    (hQ : Q ∈ (Ideal.map (C : A →+* MvPolynomial τ A) I).minimalPrimes) :
    let P := Ideal.comap (C : A →+* MvPolynomial τ A) Q
    P ∈ I.minimalPrimes ∧
      Ideal.map (C : A →+* MvPolynomial τ A) P = Q := by
  classical
  let P := Ideal.comap (C : A →+* MvPolynomial τ A) Q
  have hQprime : Q.IsPrime := hQ.1.1
  letI : Q.IsPrime := hQprime
  have hPprime : P.IsPrime := Ideal.IsPrime.comap _
  letI : P.IsPrime := hPprime
  have hIP : I ≤ P := by
    exact Ideal.map_le_iff_le_comap.mp hQ.1.2
  have hmapPprime :
      (Ideal.map (C : A →+* MvPolynomial τ A) P).IsPrime := by
    simpa [ActivePinPrimeHeight.basePrimeCoordinateIdeal,
      NullCellulePolynomial.coordinateVariableIdeal] using
      (ActivePinPrimeHeight.basePrimeCoordinateIdeal_isPrime
        (σ := τ) P (∅ : Set τ))
  have hmapP_le_Q :
      Ideal.map (C : A →+* MvPolynomial τ A) P ≤ Q :=
    Ideal.map_comap_le
  have hmapP_eq :
      Ideal.map (C : A →+* MvPolynomial τ A) P = Q := by
    apply le_antisymm hmapP_le_Q
    exact hQ.2 ⟨hmapPprime, Ideal.map_mono hIP⟩ hmapP_le_Q
  refine ⟨⟨⟨hPprime, hIP⟩, ?_⟩, hmapP_eq⟩
  intro P' hP' hP'P
  letI : P'.IsPrime := hP'.1
  have hmapP'prime :
      (Ideal.map (C : A →+* MvPolynomial τ A) P').IsPrime := by
    simpa [ActivePinPrimeHeight.basePrimeCoordinateIdeal,
      NullCellulePolynomial.coordinateVariableIdeal] using
      (ActivePinPrimeHeight.basePrimeCoordinateIdeal_isPrime
        (σ := τ) P' (∅ : Set τ))
  have hmapP'Q :
      Ideal.map (C : A →+* MvPolynomial τ A) P' ≤ Q := by
    rw [← hmapP_eq]
    exact Ideal.map_mono hP'P
  have hQmapP' : Q ≤ Ideal.map (C : A →+* MvPolynomial τ A) P' :=
    hQ.2 ⟨hmapP'prime, Ideal.map_mono hP'.2⟩ hmapP'Q
  change P ≤ P'
  rw [← ActivePinPrimeHeight.comap_map_C_eq_self (σ := τ) P']
  exact Ideal.comap_mono hQmapP'

/-- Retained pin variables do not alter the height of a minimal prime. -/
theorem minimalPrime_map_C_height_eq
    {A τ : Type*} [CommRing A] [IsNoetherianRing A] [Finite τ]
    (I : Ideal A) (Q : Ideal (MvPolynomial τ A))
    (hQ : Q ∈ (Ideal.map (C : A →+* MvPolynomial τ A) I).minimalPrimes) :
    Q.height =
      (Ideal.comap (C : A →+* MvPolynomial τ A) Q).height := by
  let P := Ideal.comap (C : A →+* MvPolynomial τ A) Q
  obtain ⟨hP, hmap⟩ := minimalPrime_map_C_contract I Q hQ
  letI : P.IsPrime := hP.1.1
  calc
    Q.height = (Ideal.map (C : A →+* MvPolynomial τ A) P).height := by
      rw [hmap]
    _ = P.height := ActivePinPrimeHeight.height_map_C_eq (σ := τ) P
    _ = (Ideal.comap (C : A →+* MvPolynomial τ A) Q).height := rfl

/-! ## Prime height from the PF function-field inequality -/

/-- The polynomial prime height formula converts a finite function-field
dimension budget into the required lower height bound. -/
theorem polynomialPrime_height_ge_of_fractionTrdeg_add_le
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (m : ℕ)
    (hbudget :
      (Algebra.trdeg k
        (FractionRing (MvPolynomial ι k ⧸ P))).toNat + m ≤
        Nat.card ι) :
    (m : ℕ∞) ≤ P.height := by
  let t := (Algebra.trdeg k
      (FractionRing (MvPolynomial ι k ⧸ P))).toNat
  have hcast : (m : ℕ∞) + (t : ℕ∞) ≤ (Nat.card ι : ℕ∞) := by
    exact_mod_cast (by simpa [add_comm] using hbudget)
  have hformula := polynomialPrime_height_add_fractionTrdeg_eq_natCard P
  change (m : ℕ∞) ≤ P.height
  rw [← ENat.add_le_add_iff_right (by simp : (t : ℕ∞) ≠ ⊤)]
  simpa [t, add_comm, add_left_comm, add_assoc, hformula] using hcast

/-! ## Function-field budget and height -/

/-- The terminal function-field inequality supplied by the projection--fibre
argument.  It is quantified over the actual minimal
primes of the literal selected-null ideal and only over branches surviving
both provenance opens. -/
def SurvivingSelectedFunctionFieldBudget
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V) : Prop :=
  ∀ (P : Ideal (TwistCoefficientRing root)),
    P ∈ (coefficientSelectedNullIdeal
      root src dst active selected).minimalPrimes →
    activeAngularDenominator root src dst active angularChart ∉ P →
    coefficientDistinctnessDenominator root distinctChart ∉ P →
    (Algebra.trdeg ℚ
      (FractionRing (TwistCoefficientRing root ⧸ P))).toNat +
        selected.card ≤ Nat.card (GroundedTwistVariable root)

/-- The surviving function-field inequality implies the selected-null height
bound used by the incidence transfer theorem. -/
theorem incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_budget
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (_hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hPF : SurvivingSelectedFunctionFieldBudget
      root src dst active angularChart selected distinctChart) :
    (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart := by
  classical
  let R₀ := TwistCoefficientRing root
  let I₀ : Ideal R₀ := coefficientSelectedNullIdeal
    root src dst active selected
  let dₐ : R₀ := activeAngularDenominator
    root src dst active angularChart
  let A := AngularCoefficientLocalization
    root src dst active angularChart
  let Iₐ : Ideal A := Ideal.map (algebraMap R₀ A) I₀
  let B := RetainedCoefficientRing
    root src dst active angularChart
  let Ib : Ideal B := retainedSelectedNullIdeal
    root src dst active angularChart selected
  let db : B := retainedDistinctnessDenominator
    root src dst active angularChart distinctChart
  let T := Localization.Away db
  let It : Ideal T := Ideal.map (algebraMap B T) Ib
  letI : IsDomain A := angularCoefficientLocalizationIsDomain
    root src dst active angularChart _hLoop
  letI : Nontrivial B := inferInstance
  letI : CommRing B := inferInstance
  change (selected.card : ℕ∞) ≤ It.height
  rw [Ideal.height_eq_inf_minimalPrimes]
  apply le_iInf
  intro Q
  apply le_iInf
  intro hQ
  letI : Q.IsPrime := hQ.1.1
  let Qb : Ideal B := Ideal.comap (algebraMap B T) Q
  have hQb : Qb ∈ Ib.minimalPrimes := by
    have hm := (IsLocalization.minimalPrimes_map
      (Submonoid.powers db) T Ib)
    have : Q ∈ (Ideal.map (algebraMap B T) Ib).minimalPrimes := hQ
    rw [hm] at this
    exact this
  letI : Qb.IsPrime := hQb.1.1
  have hIb : Ib = Ideal.map (C : A →+* B) Iₐ := by
    exact retainedSelectedNullIdeal_eq_map_C_angularSelectedNullIdeal
      root src dst active angularChart selected
  have hQb' : Qb ∈ (Ideal.map (C : A →+* B) Iₐ).minimalPrimes := by
    rw [← hIb]
    exact hQb
  let Pₐ : Ideal A := Ideal.comap (C : A →+* B) Qb
  have hPₐ : Pₐ ∈ Iₐ.minimalPrimes :=
    (minimalPrime_map_C_contract Iₐ Qb hQb').1
  have hmapPₐ : Ideal.map (C : A →+* B) Pₐ = Qb :=
    (minimalPrime_map_C_contract Iₐ Qb hQb').2
  letI : Pₐ.IsPrime := hPₐ.1.1
  let P₀ : Ideal R₀ := Ideal.comap (algebraMap R₀ A) Pₐ
  have hP₀ : P₀ ∈ I₀.minimalPrimes := by
    have hm := (IsLocalization.minimalPrimes_map
      (Submonoid.powers dₐ) A I₀)
    have : Pₐ ∈ (Ideal.map (algebraMap R₀ A) I₀).minimalPrimes := hPₐ
    rw [hm] at this
    exact this
  letI : P₀.IsPrime := hP₀.1.1
  have hdₐ : dₐ ∉ P₀ := by
    have hdisj : Disjoint (Submonoid.powers dₐ : Set R₀) (P₀ : Set R₀) :=
      (IsLocalization.isPrime_iff_isPrime_disjoint
        (Submonoid.powers dₐ) A Pₐ).mp (inferInstance : Pₐ.IsPrime) |>.2
    intro hd
    exact hdisj.le_bot ⟨Submonoid.mem_powers dₐ, hd⟩
  have hdb : db ∉ Qb := by
    have hdisj : Disjoint (Submonoid.powers db : Set B) (Qb : Set B) :=
      (IsLocalization.isPrime_iff_isPrime_disjoint
        (Submonoid.powers db) T Q).mp (inferInstance : Q.IsPrime) |>.2
    intro hd
    exact hdisj.le_bot ⟨Submonoid.mem_powers db, hd⟩
  have hddist : coefficientDistinctnessDenominator root distinctChart ∉ P₀ := by
    intro hd
    apply hdb
    dsimp [db, retainedDistinctnessDenominator]
    rw [← hmapPₐ]
    apply Ideal.mem_map_of_mem (C : A →+* B)
    have himg := Ideal.mem_map_of_mem (algebraMap R₀ A) hd
    change _ ∈ Ideal.map (algebraMap R₀ A) (Pₐ.under R₀) at himg
    rw [IsLocalization.map_under (Submonoid.powers dₐ) A Pₐ] at himg
    exact himg
  have hbase : (selected.card : ℕ∞) ≤ P₀.height := by
    exact polynomialPrime_height_ge_of_fractionTrdeg_add_le
      P₀ selected.card (hPF P₀ hP₀ hdₐ hddist)
  have hangular : Pₐ.height = P₀.height := by
    exact (IsLocalization.height_under
      (Submonoid.powers dₐ) Pₐ).symm
  have hspectator : Qb.height = Pₐ.height := by
    simpa [Pₐ] using minimalPrime_map_C_height_eq Iₐ Qb hQb'
  have hdistinct : Q.height = Qb.height := by
    exact (IsLocalization.height_under
      (Submonoid.powers db) Q).symm
  calc
    (selected.card : ℕ∞) ≤ P₀.height := hbase
    _ = Pₐ.height := hangular.symm
    _ = Qb.height := hspectator.symm
    _ = Q.height := hdistinct.symm

end

end SelectedNullHeight

end RB31E2E


end
end BundleSource0002

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0002/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0002.json"

section BundleSource0003
/- Source: Papers/RigidityZheng_NullCellule_SelectedDirectionFibre.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/SelectedDirectionFibre.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/






@[expose] public section

/-!
# Selected Split--Klein fibres are grounded direction systems

After the explicit angular/translational split, the selected null ideal is
a coefficient-linear row ideal.  At every coefficient prime its generic
fibre is therefore the literal grounded direction-row ideal, with the
original selected occurrence provenance retained.
-/

namespace RB31E2E

namespace SelectedDirectionFibre

noncomputable section

set_option synthInstance.maxHeartbeats 100000

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open UniversalHomogeneousChart
open PolynomialPrimeTrdegHeight
open GroundedTwistSplit
open CoefficientLinearFibre

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The selected null ideal transported to the iterated
`Q[translation][angular]` presentation. -/
def splitSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) :
    Ideal (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) ℚ)) :=
  Ideal.map (splitEquiv (k := ℚ) root).symm.toRingEquiv
    (SelectedNullHeight.coefficientSelectedNullIdeal
      root src dst active selected)

/-- The split selected-null ideal is literally the coefficient-linear ideal
of its oriented grounded occurrence rows. -/
theorem splitSelectedNullIdeal_eq_linearFormIdealOver
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (selected : Finset active) :
    splitSelectedNullIdeal root src dst active selected =
      linearFormIdealOver
        (fun e : SelectedOccurrence active selected ↦
          occurrenceDirectionRow root src dst
            (coefficientPlacement (k := ℚ) root) e.1.1) := by
  classical
  rw [splitSelectedNullIdeal,
    SelectedNullHeight.coefficientSelectedNullIdeal, Ideal.map_span,
    linearFormIdealOver]
  congr 1
  ext g
  constructor
  · rintro ⟨q, ⟨e, rfl⟩, rfl⟩
    refine ⟨e, ?_⟩
    symm
    change (splitEquiv (k := ℚ) root).symm
      (Twist.splitKlein
        (coefficientRelativeTwist root src dst e.1.1)) = _
    exact splitEquiv_symm_splitKlein_coefficientRelativeTwist
      root src dst e.1.1 (hLoop e.1.1 e.1.2)
  · rintro ⟨e, rfl⟩
    refine ⟨SelectedNullHeight.coefficientNullEquation
      root src dst e.1.1, ⟨e, rfl⟩, ?_⟩
    change (splitEquiv (k := ℚ) root).symm
      (Twist.splitKlein
        (coefficientRelativeTwist root src dst e.1.1)) = _
    exact splitEquiv_symm_splitKlein_coefficientRelativeTwist
      root src dst e.1.1 (hLoop e.1.1 e.1.2)

/-- The coefficient-prime quotient function field placement, grounded at
`root`. -/
def quotientPlacement
    {V : Type*} [DecidableEq V] (root : V)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime] :
    V → Fin 3 →
      FractionRing (MvPolynomial (SpatialVariable root) ℚ ⧸ p) :=
  fun v i ↦ if h : v = root then 0 else
    FractionQuotientCoordinates.coordinate p ⟨⟨v, h⟩, i⟩

@[simp] theorem quotientPlacement_root
    {V : Type*} [DecidableEq V] (root : V)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime] :
    quotientPlacement root p root = 0 := by
  funext i
  simp [quotientPlacement]

/-- The quotient placement coordinates generate the coefficient function
field; the grounded zero coordinates introduce no extra generator. -/
theorem quotientPlacement_generated
    {V : Type*} [DecidableEq V] (root : V)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime] :
    IntermediateField.adjoin ℚ
      (Set.range (fun x : V × Fin 3 ↦
        quotientPlacement root p x.1 x.2)) = ⊤ := by
  let K := FractionRing
    (MvPolynomial (SpatialVariable root) ℚ ⧸ p)
  let L : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ
      (Set.range (fun x : V × Fin 3 ↦
        quotientPlacement root p x.1 x.2))
  apply top_unique
  have hcoord := FractionQuotientCoordinates.adjoin_coordinate_eq_top p
  rw [← hcoord]
  apply IntermediateField.adjoin.mono
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨x.1.1, x.2⟩, ?_⟩
  simp [quotientPlacement, x.1.2]

/-- Mapping the universal coefficient placement to the quotient function
field gives `quotientPlacement` exactly. -/
theorem map_coefficientPlacement_eq_quotientPlacement
    {V : Type*} [DecidableEq V] (root : V)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime]
    (v : V) (i : Fin 3) :
    algebraMap (MvPolynomial (SpatialVariable root) ℚ ⧸ p)
        (FractionRing (MvPolynomial (SpatialVariable root) ℚ ⧸ p))
      (Ideal.Quotient.mk p (coefficientPlacement root v i)) =
      quotientPlacement root p v i := by
  by_cases hv : v = root
  · simp [coefficientPlacement, quotientPlacement, hv]
  · simp [coefficientPlacement, quotientPlacement,
      FractionQuotientCoordinates.coordinate, hv]

/-- One occurrence row maps coefficientwise to the same row evaluated at
the quotient placement. -/
theorem map_occurrenceDirectionRow
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime]
    (x : SpatialVariable root) :
    algebraMap (MvPolynomial (SpatialVariable root) ℚ ⧸ p)
        (FractionRing (MvPolynomial (SpatialVariable root) ℚ ⧸ p))
      (Ideal.Quotient.mk p
        (occurrenceDirectionRow root src dst
          (coefficientPlacement (k := ℚ) root) e x)) =
      occurrenceDirectionRow root src dst
        (quotientPlacement root p) e x := by
  by_cases hs : src e = x.1.1 <;>
    by_cases hd : dst e = x.1.1 <;>
    simp [occurrenceDirectionRow, hs, hd,
      map_coefficientPlacement_eq_quotientPlacement] <;> rfl

/-- An occurrence row depends only on its unoriented active edge. -/
theorem occurrenceDirectionRow_eq_groundedDirectionRow_of_activeEdge_eq
    {k V E : Type*} [Field k] [Fintype V]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (a : V → Fin 3 → k) (e : active) (f : SimpleEdge V)
    (hef : SparseNullIncidence.activeEdge src dst active hLoop e = f) :
    occurrenceDirectionRow root src dst a e.1 =
      GroundedDirectionConstraint.groundedDirectionRow root a f := by
  have hpair : s(f.source, f.target) = s(src e.1, dst e.1) := by
    rw [f.source_target_mk, ← hef]
    rfl
  rcases Sym2.eq_iff.mp hpair with h | h
  · funext x
    simp [occurrenceDirectionRow,
      GroundedDirectionConstraint.groundedDirectionRow,
      DirectionStress.directionRow, DirectionStress.edgeDirection,
      h.1, h.2]
  · funext x
    simp [occurrenceDirectionRow,
      GroundedDirectionConstraint.groundedDirectionRow,
      DirectionStress.directionRow, DirectionStress.edgeDirection,
      h.1, h.2]
    ring

/-- For the canonical skeleton selection, the selected occurrence-row set
is exactly the grounded direction-row set of the skeleton. -/
theorem range_selectedOccurrenceRows_eq_range_groundedDirectionRows
    {k V E : Type*} [Field k] [Fintype V]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (a : V → Fin 3 → k) :
    Set.range (fun e : SelectedOccurrence active
        (SparseNullIncidence.selectedSkeletonOccurrences
          src dst active hLoop F hRepresented) ↦
      occurrenceDirectionRow root src dst a e.1.1) =
    Set.range (fun f : F ↦
      GroundedDirectionConstraint.groundedDirectionRow root a f.1) := by
  ext row
  constructor
  · rintro ⟨e, rfl⟩
    let f : F := ⟨SparseNullIncidence.activeEdge
      src dst active hLoop e.1,
      SparseNullIncidence.activeEdge_mem_of_mem_selectedSkeletonOccurrences
        src dst active hLoop F hRepresented e.1 e.2⟩
    refine ⟨f, ?_⟩
    exact (occurrenceDirectionRow_eq_groundedDirectionRow_of_activeEdge_eq
      root src dst active hLoop a e.1 f.1 rfl).symm
  · rintro ⟨f, rfl⟩
    let e : SelectedOccurrence active
        (SparseNullIncidence.selectedSkeletonOccurrences
          src dst active hLoop F hRepresented) :=
      ⟨SparseNullIncidence.representedOccurrence
          src dst active hLoop F hRepresented f,
        SparseNullIncidence.representedOccurrence_mem_selectedSkeletonOccurrences
          src dst active hLoop F hRepresented f⟩
    refine ⟨e, ?_⟩
    exact occurrenceDirectionRow_eq_groundedDirectionRow_of_activeEdge_eq
      root src dst active hLoop a e.1 f.1
        (SparseNullIncidence.representedOccurrence_activeEdge
          src dst active hLoop F hRepresented f)

end

end SelectedDirectionFibre

end RB31E2E


end
end BundleSource0003

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0003/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0003.json"

section BundleSource0004
/- Source: Papers/RigidityZheng_Linear_FiniteRowSpanStress.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/FiniteRowSpanStress.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-! # Row-span/stress rank--nullity -/

namespace RB31E2E

namespace FiniteRowSystem

noncomputable section

variable {k I J : Type*} [Field k] [Fintype I] [Fintype J]

/-- The dimension of the literal row span plus the dimension of the row
relation kernel is exactly the number of labelled rows. -/
theorem finrank_span_add_stressDim_eq_card (row : J → I → k) :
    Module.finrank k (Submodule.span k (Set.range row)) +
      stressDim row = Fintype.card J := by
  have hs := (synthesis row).finrank_range_add_finrank_ker
  have hrange :
      Module.finrank k (LinearMap.range (synthesis row)) =
        Module.finrank k (Submodule.span k (Set.range row)) := by
    change (matrix row).transpose.rank = _
    rw [Matrix.rank_transpose, Matrix.rank_eq_finrank_span_row]
    rfl
  have hdomain : Module.finrank k (J → k) = Fintype.card J := by
    rw [Module.finrank_fintype_fun_eq_card]
  change Module.finrank k (LinearMap.range (synthesis row)) +
      stressDim row = Module.finrank k (J → k) at hs
  simpa [hrange, hdomain] using hs

end

end FiniteRowSystem

end RB31E2E


end
end BundleSource0004

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0004/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0004.json"

section BundleSource0005
/- Source: Papers/RigidityZheng_NullCellule_SelectedDirectionHeight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/SelectedDirectionHeight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Height ledger for a split selected direction component

This file combines the coefficient-prime dimension formula, the exact
generic linear fibre, and direction-matrix rank--nullity.  The only
mathematical input is the global grounded function-field semismallness
theorem; no selected-null height or terminal twist-field budget is assumed.
-/

namespace RB31E2E

namespace SelectedDirectionHeight

noncomputable section

set_option synthInstance.maxHeartbeats 100000

open MvPolynomial
open PolynomialPrimeTrdegHeight
open GroundedTwistSplit
open SelectedDirectionFibre
open CoefficientLinearFibre
open MinimalPrimeLinearFibre
open UniversalHomogeneousChart

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v

/-- A minimal component of the split selected-null system has the full edge
height once the grounded PF function-field inequality is available for all
coordinate-generated distinct placements. -/
theorem splitMinimalPrime_height_ge_edgeCard_of_groundedPF
    {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (P : Ideal (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) ℚ))) [P.IsPrime]
    [(coefficientContraction P).IsPrime]
    (hP : P ∈ (splitSelectedNullIdeal root src dst active
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented)).minimalPrimes)
    (hInjective : Function.Injective
      (quotientPlacement root (coefficientContraction P)))
    (hPF : ∀ {K : Type u} [Field K] [Algebra ℚ K]
      (a : V → Fin 3 → K),
      a root = 0 →
      Function.Injective a →
      IntermediateField.adjoin ℚ
          (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
      DirectionStress.directionStressDim F a +
          (Algebra.trdeg ℚ K).toNat ≤
        Nat.card (SpatialVariable root)) :
    (F.card : ℕ∞) ≤ P.height := by
  classical
  let selected := SparseNullIncidence.selectedSkeletonOccurrences
    src dst active hLoop F hRepresented
  let τ := SpatialVariable root
  let A := MvPolynomial τ ℚ
  let p : Ideal A := coefficientContraction P
  let B := A ⧸ p
  let K := FractionRing B
  let q := coefficientQuotientMap (τ := τ) p
  let ℓ : MvPolynomial τ B →+* MvPolynomial τ K :=
    MvPolynomial.map (algebraMap B K)
  let PL : Ideal (MvPolynomial τ K) :=
    Ideal.map ℓ (Ideal.map q P)
  let a : V → Fin 3 → K := quotientPlacement root p
  let rowA : SelectedOccurrence active selected → τ → A :=
    fun e ↦ occurrenceDirectionRow root src dst
      (coefficientPlacement (k := ℚ) root) e.1.1
  let rowK : SelectedOccurrence active selected → τ → K :=
    fun e x ↦ algebraMap B K
      (Ideal.Quotient.mk p (rowA e x))
  let rowDirection : SelectedOccurrence active selected → τ → K :=
    fun e ↦ occurrenceDirectionRow root src dst a e.1.1
  have hIeq : splitSelectedNullIdeal root src dst active selected =
      linearFormIdealOver rowA := by
    exact splitSelectedNullIdeal_eq_linearFormIdealOver
      root src dst active hLoop selected
  have hPlinear : P ∈ (linearFormIdealOver rowA).minimalPrimes := by
    rw [← hIeq]
    exact hP
  have hgeneric : PL = LinearFormIdeal.linearFormIdeal rowK := by
    exact fractionFibrePrime_eq_linearFormIdeal rowA P hPlinear
  have hrow : rowK = rowDirection := by
    funext e x
    exact map_occurrenceDirectionRow root src dst e.1.1 p x
  have hPLlinear : PL = LinearFormIdeal.linearFormIdeal rowDirection := by
    rw [hgeneric, hrow]
  have hrange : Set.range rowDirection =
      Set.range (fun f : F ↦
        GroundedDirectionConstraint.groundedDirectionRow root a f.1) := by
    exact range_selectedOccurrenceRows_eq_range_groundedDirectionRows
      root src dst active hLoop F hRepresented a
  have hlinearHeight :
      (Module.finrank K
        (Submodule.span K (Set.range rowDirection)) : ℕ∞) ≤
        PL.height := by
    rw [hPLlinear]
    exact LinearFormIdeal.finrank_span_le_linearFormIdeal_height rowDirection
  let groundRow : F → τ → K := fun f ↦
    GroundedDirectionConstraint.groundedDirectionRow root a f.1
  have hspanStress :
      Module.finrank K (Submodule.span K (Set.range groundRow)) +
          DirectionStress.directionStressDim F a = F.card := by
    have hs := FiniteRowSystem.finrank_span_add_stressDim_eq_card groundRow
    have hstressEq : FiniteRowSystem.stressDim groundRow =
        DirectionStress.directionStressDim F a := by
      exact GroundedDirectionConstraint.stressDim_eq_directionStressDim
        root F a
    rw [hstressEq] at hs
    calc
      Module.finrank K (Submodule.span K (Set.range groundRow)) +
          DirectionStress.directionStressDim F a = Fintype.card F := hs
      _ = F.card := Fintype.card_coe F
  have hrankNullity :
      DirectionStress.directionStressDim F a +
          Module.finrank K
            (Submodule.span K (Set.range rowDirection)) = F.card := by
    rw [hrange]
    rw [add_comm]
    exact hspanStress
  have hgenerated : IntermediateField.adjoin ℚ
      (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ := by
    exact quotientPlacement_generated root p
  have hroot : a root = 0 := quotientPlacement_root root p
  have hPFnat : DirectionStress.directionStressDim F a +
      (Algebra.trdeg ℚ K).toNat ≤ Nat.card τ := by
    exact hPF a hroot hInjective hgenerated
  let t := (Algebra.trdeg ℚ K).toNat
  have hpFormula : p.height + (t : ℕ∞) = (Nat.card τ : ℕ∞) := by
    exact polynomialPrime_height_add_fractionTrdeg_eq_natCard p
  have hPFcast :
      (DirectionStress.directionStressDim F a : ℕ∞) + (t : ℕ∞) ≤
        (Nat.card τ : ℕ∞) := by
    exact_mod_cast hPFnat
  have hstress :
      (DirectionStress.directionStressDim F a : ℕ∞) ≤ p.height := by
    rw [← ENat.add_le_add_iff_right (by simp : (t : ℕ∞) ≠ ⊤)]
    calc
      (DirectionStress.directionStressDim F a : ℕ∞) + (t : ℕ∞) ≤
          (Nat.card τ : ℕ∞) := hPFcast
      _ = p.height + (t : ℕ∞) := hpFormula.symm
  have hheight : P.height = p.height + PL.height := by
    exact polynomialPrime_height_eq_contractionHeight_add_fractionFibreHeight P
  rw [hheight, ← hrankNullity, Nat.cast_add]
  exact add_le_add hstress hlinearHeight

end

end SelectedDirectionHeight

end RB31E2E


end
end BundleSource0005

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0005/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0005.json"

section BundleSource0006
/- Source: Papers/RigidityZheng_NullCellule_WittShearDistinctPrime.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/WittShearDistinctPrime.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Witt shearing a surviving selected-null component to an injective placement

The complete distinctness denominator says that every labelled pair of
generic twists is nonzero.  One common rational Witt shear makes the
translational half of every such difference nonzero.  After the explicit
angular/translational split, the coefficient-prime quotient placement is
therefore injective.
-/

namespace RB31E2E

namespace WittShearDistinctPrime

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open PinOuterFullProvenanceHeightTransfer
open UniversalHomogeneousChart
open SelectedNullHeight
open GroundedTwistSplit
open SelectedDirectionFibre
open PolynomialPrimeTrdegHeight

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v

/-- The map from a prime polynomial ring to its quotient function field. -/
def primeFunctionFieldMap
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] :
    R →+* FractionRing (R ⧸ P) :=
  (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp
    (Ideal.Quotient.mk P)

theorem primeFunctionFieldMap_eq_zero_iff
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] (x : R) :
    primeFunctionFieldMap P x = 0 ↔ x ∈ P := by
  constructor
  · intro hx
    have hq : Ideal.Quotient.mk P x = 0 := by
      apply (FaithfulSMul.algebraMap_injective (R ⧸ P)
        (FractionRing (R ⧸ P)))
      change primeFunctionFieldMap P x = _
      simpa using hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · intro hx
    have hq : Ideal.Quotient.mk P x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    simp [primeFunctionFieldMap, hq]

/-- Polynomial Witt shear of the root-zero universal twist assignment. -/
theorem map_coefficientGroundedTwist
    {V : Type*} [DecidableEq V] (root v : V) (s : Vec3 ℚ) :
    mapTwist (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
        (coefficientGroundedTwist root v) =
      WittShear.shear (fun j ↦ C (s j))
        (coefficientGroundedTwist root v) := by
  by_cases hv : v = root
  · subst v
    have hzero : coefficientGroundedTwist root root = 0 := by
      simp [coefficientGroundedTwist, extendOffRoot]
    rw [hzero, mapTwist_zero]
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [WittShear.shear, Vec3.cross]
  · have hground : coefficientGroundedTwist root v =
        coefficientOffRootTwist ⟨v, hv⟩ := by
      simp [coefficientGroundedTwist, extendOffRoot, hv]
    rw [hground]
    change mapTwist
      (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
        (WittShear.universalTwist (k := ℚ) ⟨v, hv⟩) =
      WittShear.shear (fun j ↦ C (s j))
        (WittShear.universalTwist (k := ℚ) ⟨v, hv⟩)
    exact WittShear.map_universalTwist (U := OffRoot root) s ⟨v, hv⟩

theorem map_coefficientRelativeTwist
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) (s : Vec3 ℚ) :
    mapTwist (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
        (coefficientRelativeTwist root src dst e) =
      WittShear.shear (fun j ↦ C (s j))
        (coefficientRelativeTwist root src dst e) := by
  rw [coefficientRelativeTwist, mapTwist_sub,
    map_coefficientGroundedTwist, map_coefficientGroundedTwist,
    ← WittShear.shear_sub]

/-- Every selected Split--Klein generator is fixed by the polynomial Witt
shear, including occurrences incident with the grounded root. -/
theorem algEquiv_coefficientNullEquation
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) (s : Vec3 ℚ) :
    WittShear.algEquiv (U := OffRoot root) s
        (coefficientNullEquation root src dst e) =
      coefficientNullEquation root src dst e := by
  rw [coefficientNullEquation]
  change (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
      (Twist.splitKlein (coefficientRelativeTwist root src dst e)) = _
  rw [WittShear.map_splitKlein, map_coefficientRelativeTwist,
    WittShear.splitKlein_shear]

/-- The literal selected-null ideal is invariant under every rational Witt
shear. -/
theorem map_coefficientSelectedNullIdeal_algEquiv
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) (s : Vec3 ℚ) :
    Ideal.map
        (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv
        (coefficientSelectedNullIdeal root src dst active selected) =
      coefficientSelectedNullIdeal root src dst active selected := by
  rw [coefficientSelectedNullIdeal, Ideal.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨x, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, (algEquiv_coefficientNullEquation
      root src dst e.1.1 s).symm⟩
  · rintro ⟨e, rfl⟩
    refine ⟨coefficientNullEquation root src dst e.1.1, ⟨e, rfl⟩, ?_⟩
    exact algEquiv_coefficientNullEquation
      root src dst e.1.1 s

/-- Minimal primes transport through a ring equivalence. -/
theorem map_mem_minimalPrimes_of_equiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I P : Ideal R) [P.IsPrime]
    (hP : P ∈ I.minimalPrimes) :
    Ideal.map e P ∈ (Ideal.map e I).minimalPrimes := by
  let Q := Ideal.map e P
  have hQprime : Q.IsPrime := Ideal.map_isPrime_of_equiv e
  refine ⟨⟨hQprime, Ideal.map_mono hP.1.2⟩, ?_⟩
  intro J hJ hJQ
  letI : J.IsPrime := hJ.1
  have hJbackPrime : (Ideal.comap e J).IsPrime :=
    Ideal.IsPrime.comap e
  have hIback : I ≤ Ideal.comap e J :=
    Ideal.map_le_iff_le_comap.mp hJ.2
  have hbackP : Ideal.comap e J ≤ P := by
    intro x hx
    have hexJ : e x ∈ J := hx
    have hex : e x ∈ Q := hJQ hexJ
    obtain ⟨y, hyP, hyx⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).mp hex
    have : y = x := e.injective hyx
    simpa [this] using hyP
  have hPback : P ≤ Ideal.comap e J :=
    hP.2 ⟨hJbackPrime, hIback⟩ hbackP
  exact (Ideal.map_mono hPback).trans Ideal.map_comap_le

/-- A factor of the complete distinctness product cannot lie in a prime
which avoids that product. -/
theorem coefficientBodyDifferenceCoordinate_not_mem_of_denominator_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root))
    (hden : coefficientDistinctnessDenominator root chart ∉ P)
    (uv : OrderedDistinctBodyPair V) :
    coefficientBodyDifferenceCoordinate root uv (chart uv) ∉ P := by
  intro hfactor
  apply hden
  rw [coefficientDistinctnessDenominator]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun w : OrderedDistinctBodyPair V ↦
      coefficientBodyDifferenceCoordinate root w (chart w))
    (Finset.mem_univ uv)]
  exact P.mul_mem_right _ hfactor

/-- Mapping a body-difference factor to the prime function field reads the
corresponding coordinate of the mapped relative twist. -/
theorem primeFunctionFieldMap_bodyDifferenceCoordinate
    {V : Type*} [DecidableEq V] (root : V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    primeFunctionFieldMap P
        (coefficientBodyDifferenceCoordinate root uv c) =
      twistCoordinates
        (mapTwist (primeFunctionFieldMap P)
          (coefficientGroundedTwist root uv.1.1 -
            coefficientGroundedTwist root uv.1.2)) c := by
  rcases c with ⟨b, i⟩
  cases b <;>
    simp [coefficientBodyDifferenceCoordinate,
      coefficientGroundedCoordinate, twistCoordinates, mapTwist, mapVec3]

/-- Every pairwise twist difference is genuinely nonzero in the function
field of a component surviving the complete distinctness open. -/
theorem mapped_pairDifference_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hden : coefficientDistinctnessDenominator root chart ∉ P)
    (uv : OrderedDistinctBodyPair V) :
    mapTwist (primeFunctionFieldMap P)
      (coefficientGroundedTwist root uv.1.1 -
        coefficientGroundedTwist root uv.1.2) ≠ 0 := by
  intro hzero
  have hcoord := congrArg
    (fun Z ↦ twistCoordinates Z (chart uv)) hzero
  have hmapzero : primeFunctionFieldMap P
      (coefficientBodyDifferenceCoordinate root uv (chart uv)) = 0 := by
    rw [primeFunctionFieldMap_bodyDifferenceCoordinate]
    simpa using hcoord
  exact coefficientBodyDifferenceCoordinate_not_mem_of_denominator_not_mem
    root chart P hden uv
      ((primeFunctionFieldMap_eq_zero_iff P _).mp hmapzero)

/-- Ring maps commute with the explicit Witt shear when the shear parameter
is mapped coefficientwise. -/
theorem mapTwist_shear
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Vec3 R) (Z : Twist R) :
    mapTwist f (WittShear.shear s Z) =
      WittShear.shear (fun i ↦ f (s i)) (mapTwist f Z) := by
  apply Prod.ext
  · rfl
  · funext i
    change f (Z.2 i + Vec3.cross Z.1 s i) =
      f (Z.2 i) + Vec3.cross (fun j ↦ f (Z.1 j))
        (fun j ↦ f (s j)) i
    rw [map_add]
    congr 1
    fin_cases i <;> simp [Vec3.cross]

/-- A translational body-difference coordinate becomes the corresponding
coordinate of the sheared pairwise twist difference. -/
theorem algEquiv_translationalBodyDifferenceCoordinate
    {V : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (i : Fin 3) (s : Vec3 ℚ) :
    WittShear.algEquiv (U := OffRoot root) s
        (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩) =
      (WittShear.shear (fun j ↦ C (s j))
        (coefficientGroundedTwist root uv.1.1 -
          coefficientGroundedTwist root uv.1.2)).2 i := by
  have hmap := congrArg (fun Z ↦ Z.2 i)
    (show mapTwist
        (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
          (coefficientGroundedTwist root uv.1.1 -
            coefficientGroundedTwist root uv.1.2) =
        WittShear.shear (fun j ↦ C (s j))
          (coefficientGroundedTwist root uv.1.1 -
            coefficientGroundedTwist root uv.1.2) by
      rw [mapTwist_sub, map_coefficientGroundedTwist,
        map_coefficientGroundedTwist, ← WittShear.shear_sub])
  simpa [coefficientBodyDifferenceCoordinate,
    coefficientGroundedCoordinate, mapTwist, mapVec3] using hmap

/-- Under the iterated split, a translational difference is a constant
coefficient polynomial in the outer angular variables. -/
theorem splitEquiv_symm_translationalBodyDifferenceCoordinate
    {V : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (i : Fin 3) :
    (splitEquiv (k := ℚ) root).symm
        (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩) =
      C (coefficientPlacement (k := ℚ) root uv.1.1 i -
        coefficientPlacement (k := ℚ) root uv.1.2 i) := by
  rw [map_sub]
  apply (splitEquiv (k := ℚ) root).injective
  rw [(splitEquiv (k := ℚ) root).apply_symm_apply, map_sub]
  change coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩ =
    splitEquiv (k := ℚ) root
        (C (coefficientPlacement root uv.1.1 i)) -
      splitEquiv (k := ℚ) root
        (C (coefficientPlacement root uv.1.2 i))
  have hu := congrArg (fun Z ↦ Z.2 i)
    (map_iteratedGroundedTwist root uv.1.1)
  have hv := congrArg (fun Z ↦ Z.2 i)
    (map_iteratedGroundedTwist root uv.1.2)
  change splitEquiv (k := ℚ) root
      ((iteratedGroundedTwist (k := ℚ) root uv.1.1).2 i) =
    (coefficientGroundedTwist root uv.1.1).2 i at hu
  change splitEquiv (k := ℚ) root
      ((iteratedGroundedTwist (k := ℚ) root uv.1.2).2 i) =
    (coefficientGroundedTwist root uv.1.2).2 i at hv
  rw [iteratedGroundedTwist_snd] at hu hv
  simpa [coefficientBodyDifferenceCoordinate,
    coefficientGroundedCoordinate] using
      (congrArg₂ (fun x y ↦ x - y) hu hv).symm

/-- A component surviving the complete distinctness open admits one
rational Witt shear whose split coefficient-prime placement is injective.
The transformed component is still a minimal selected-null component and
has the same height. -/
theorem exists_splitMinimalPrime_with_injective_placement
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (_hLoop : ∀ e ∈ active, src e ≠ dst e)
    (selected : Finset active) (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hP : P ∈ (coefficientSelectedNullIdeal
      root src dst active selected).minimalPrimes)
    (hden : coefficientDistinctnessDenominator root chart ∉ P) :
    ∃ (_s : Vec3 ℚ)
      (Psplit : Ideal (MvPolynomial (SpatialVariable root)
        (MvPolynomial (SpatialVariable root) ℚ)))
      (hp : (coefficientContraction Psplit).IsPrime),
      Psplit ∈ (splitSelectedNullIdeal
        root src dst active selected).minimalPrimes ∧
      Function.Injective
        (@quotientPlacement V _ root (coefficientContraction Psplit) hp) ∧
      Psplit.height = P.height := by
  classical
  let K := FractionRing (TwistCoefficientRing root ⧸ P)
  let φ : TwistCoefficientRing root →+* K := primeFunctionFieldMap P
  let Z : OrderedDistinctBodyPair V → Twist K := fun uv ↦
    mapTwist φ (coefficientGroundedTwist root uv.1.1 -
      coefficientGroundedTwist root uv.1.2)
  have hZ : ∀ uv, Z uv ≠ 0 := by
    intro uv
    exact mapped_pairDifference_ne_zero root chart P hden uv
  obtain ⟨s, hs⟩ := WittShear.exists_common_base_shear_snd_ne_zero
    (k := ℚ) Z hZ
  let e : TwistCoefficientRing root ≃+* TwistCoefficientRing root :=
    (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv
  let Ps : Ideal (TwistCoefficientRing root) := Ideal.map e.symm P
  have hPsPrime : Ps.IsPrime := Ideal.map_isPrime_of_equiv e.symm
  letI : Ps.IsPrime := hPsPrime
  have hmapI : Ideal.map e.symm
      (coefficientSelectedNullIdeal root src dst active selected) =
      coefficientSelectedNullIdeal root src dst active selected := by
    have hinv := map_coefficientSelectedNullIdeal_algEquiv
      root src dst active selected (-s)
    have heq : e.symm =
        (WittShear.algEquiv (U := OffRoot root) (-s)).toRingEquiv := by
      ext x
      rfl
    rw [heq]
    exact hinv
  have hPs : Ps ∈ (coefficientSelectedNullIdeal
      root src dst active selected).minimalPrimes := by
    have hm := map_mem_minimalPrimes_of_equiv e.symm
      (coefficientSelectedNullIdeal root src dst active selected) P hP
    rw [hmapI] at hm
    exact hm
  let esplit := (splitEquiv (k := ℚ) root).symm.toRingEquiv
  let Psplit : Ideal (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) ℚ)) := Ideal.map esplit Ps
  have hPsplitPrime : Psplit.IsPrime := Ideal.map_isPrime_of_equiv esplit
  letI : Psplit.IsPrime := hPsplitPrime
  have hPsplit : Psplit ∈ (splitSelectedNullIdeal
      root src dst active selected).minimalPrimes := by
    exact map_mem_minimalPrimes_of_equiv esplit
      (coefficientSelectedNullIdeal root src dst active selected) Ps hPs
  have hplain : ∀ uv : OrderedDistinctBodyPair V,
      ∃ i : Fin 3,
        coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩ ∉ Ps := by
    intro uv
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hs uv)
    refine ⟨i, ?_⟩
    intro hmem
    have hemem : e
        (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩) ∈ P := by
      dsimp [Ps] at hmem
      rw [Ideal.map_symm] at hmem
      exact hmem
    have hzero : φ (e
        (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩)) = 0 :=
      (primeFunctionFieldMap_eq_zero_iff P _).2 hemem
    apply hi
    have hpoly := algEquiv_translationalBodyDifferenceCoordinate
      root uv i s
    have hcommute := mapTwist_shear φ (fun j ↦ C (s j))
      (coefficientGroundedTwist root uv.1.1 -
        coefficientGroundedTwist root uv.1.2)
    have hsparam : (fun j ↦ φ (C (s j))) =
        (fun j ↦ algebraMap ℚ K (s j)) := by
      funext j
      rfl
    have hcoord :
        φ (e (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩)) =
          (WittShear.shear (fun j ↦ algebraMap ℚ K (s j)) (Z uv)).2 i := by
      calc
        φ (e (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩)) =
            φ ((WittShear.shear (fun j ↦ C (s j))
              (coefficientGroundedTwist root uv.1.1 -
                coefficientGroundedTwist root uv.1.2)).2 i) := by
          exact congrArg φ hpoly
        _ = (mapTwist φ
            (WittShear.shear (fun j ↦ C (s j))
              (coefficientGroundedTwist root uv.1.1 -
                coefficientGroundedTwist root uv.1.2))).2 i := rfl
        _ = (WittShear.shear (fun j ↦ φ (C (s j)))
            (mapTwist φ
              (coefficientGroundedTwist root uv.1.1 -
                coefficientGroundedTwist root uv.1.2))).2 i := by
          exact congrArg (fun T ↦ T.2 i) hcommute
        _ = (WittShear.shear
            (fun j ↦ algebraMap ℚ K (s j)) (Z uv)).2 i := by
          rw [hsparam]
    rw [hcoord] at hzero
    exact hzero
  have hinjective : Function.Injective
      (@quotientPlacement V _ root (coefficientContraction Psplit)
        (coefficientContraction_isPrime Psplit)) := by
    intro u v huv
    by_contra huvne
    let uv : OrderedDistinctBodyPair V := ⟨(u, v), huvne⟩
    obtain ⟨i, hi⟩ := hplain uv
    let p := coefficientContraction Psplit
    have hpPrime : p.IsPrime := coefficientContraction_isPrime Psplit
    letI : p.IsPrime := hpPrime
    have hcoordEq := congrFun huv i
    change quotientPlacement root p u i = quotientPlacement root p v i at hcoordEq
    have hzero : primeFunctionFieldMap p
        (coefficientPlacement root u i - coefficientPlacement root v i) = 0 := by
      change algebraMap (MvPolynomial (SpatialVariable root) ℚ ⧸ p)
          (FractionRing (MvPolynomial (SpatialVariable root) ℚ ⧸ p))
        (Ideal.Quotient.mk p
          (coefficientPlacement root u i - coefficientPlacement root v i)) = 0
      rw [map_sub, map_sub, map_coefficientPlacement_eq_quotientPlacement,
        map_coefficientPlacement_eq_quotientPlacement, hcoordEq]
      exact sub_self _
    have hp : coefficientPlacement root u i -
        coefficientPlacement root v i ∈ p :=
      (primeFunctionFieldMap_eq_zero_iff p _).1 hzero
    have hC : C (coefficientPlacement root u i -
        coefficientPlacement root v i) ∈ Psplit := hp
    have hfactorSplit :=
      splitEquiv_symm_translationalBodyDifferenceCoordinate root uv i
    have hfactorPs : coefficientBodyDifferenceCoordinate
        root uv ⟨true, i⟩ ∈ Ps := by
      have himage : (splitEquiv (k := ℚ) root).symm
          (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩) ∈
          Psplit := by
        rw [hfactorSplit]
        exact hC
      exact (Ideal.apply_mem_of_equiv_iff
        (I := Ps) (f := esplit)
        (x := coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩)).1 himage
    exact hi hfactorPs
  let hp : (coefficientContraction Psplit).IsPrime :=
    coefficientContraction_isPrime Psplit
  refine ⟨s, Psplit, hp, hPsplit, ?_, ?_⟩
  · exact hinjective
  calc
    Psplit.height = Ps.height := esplit.height_map Ps
    _ = P.height := e.symm.height_map P

/-- Lower height bound for a surviving minimal selected-null component from
the grounded PF function-field theorem.  The terminal full-twist
function-field budget does not occur in the statement. -/
theorem coefficientMinimalPrime_height_ge_edgeCard_of_groundedPF
    {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hP : P ∈ (coefficientSelectedNullIdeal root src dst active
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented)).minimalPrimes)
    (hden : coefficientDistinctnessDenominator root chart ∉ P)
    (hPF : ∀ {K : Type u} [Field K] [Algebra ℚ K]
      (a : V → Fin 3 → K),
      a root = 0 →
      Function.Injective a →
      IntermediateField.adjoin ℚ
          (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
      DirectionStress.directionStressDim F a +
          (Algebra.trdeg ℚ K).toNat ≤
        Nat.card (SpatialVariable root)) :
    (F.card : ℕ∞) ≤ P.height := by
  obtain ⟨_s, Psplit, hp, hPsplit, hinjective, hheight⟩ :=
    exists_splitMinimalPrime_with_injective_placement
      root src dst active hLoop
        (SparseNullIncidence.selectedSkeletonOccurrences
          src dst active hLoop F hRepresented)
        chart P hP hden
  have hPsplitPrime : Psplit.IsPrime := hPsplit.1.1
  letI : Psplit.IsPrime := hPsplitPrime
  letI : (coefficientContraction Psplit).IsPrime := hp
  have hsplit :=
    SelectedDirectionHeight.splitMinimalPrime_height_ge_edgeCard_of_groundedPF
      root src dst active hLoop F hRepresented Psplit hPsplit hinjective hPF
  rw [← hheight]
  exact hsplit

/-- A surviving minimal selected-null component has exactly one unit of
height per selected skeleton edge. -/
theorem coefficientMinimalPrime_height_eq_edgeCard_of_groundedPF
    {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hP : P ∈ (coefficientSelectedNullIdeal root src dst active
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented)).minimalPrimes)
    (hden : coefficientDistinctnessDenominator root chart ∉ P)
    (hPF : ∀ {K : Type u} [Field K] [Algebra ℚ K]
      (a : V → Fin 3 → K),
      a root = 0 →
      Function.Injective a →
      IntermediateField.adjoin ℚ
          (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
      DirectionStress.directionStressDim F a +
          (Algebra.trdeg ℚ K).toNat ≤
        Nat.card (SpatialVariable root)) :
    P.height = (F.card : ℕ∞) := by
  have hupper :=
    coefficientMinimalPrime_height_le_selectedCard
      root src dst active
        (SparseNullIncidence.selectedSkeletonOccurrences
          src dst active hLoop F hRepresented)
        P hP
  rw [SparseNullIncidence.card_selectedSkeletonOccurrences
    src dst active hLoop F hRepresented] at hupper
  exact le_antisymm hupper
    (coefficientMinimalPrime_height_ge_edgeCard_of_groundedPF
      root src dst active hLoop F hRepresented chart P hP hden hPF)

end

end WittShearDistinctPrime

end RB31E2E


end
end BundleSource0006

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0006/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0006.json"

section BundleSource0007
/- Source: Papers/RigidityZheng_Combinatorics_Sparse22_TightCompletion.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/Sparse22/TightCompletion.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Same-vertex tight completion for `(2,2)`-sparse simple graphs

For at least four vertices, every `(2,2)`-sparse simple edge set extends,
without adding vertices, to a set tight on the full vertex universe.  The
proof maximizes among sparse supersets of the given set and derives the
augmentation property from tight-set uncrossing.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

private theorem two_mul_card_sub_one_le_choose_two {n : ℕ} (hn : 4 ≤ n) :
    2 * (n - 1) ≤ n.choose 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hnsmall : n < 4
      · have hn3 : n = 3 := by omega
        subst n
        decide
      · have hrec := ih (by omega)
        have hchoose : n.succ.choose 2 = n + n.choose 2 := by
          simp only [Nat.choose_succ_succ, Nat.choose_one_right]
        rw [hchoose]
        omega

private theorem tightCompletion_sym2_eq_of_toFinset_eq
    {e f : Sym2 V} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (hvertices : e.toFinset = f.toFinset) : e = f := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      induction f using Sym2.inductionOn with
      | _ c d =>
          have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using he
          have hcd : c ≠ d := by simpa [Sym2.mk_isDiag_iff] using hf
          have ha : a = c ∨ a = d := by
            have : a ∈ s(c, d).toFinset := by
              rw [← hvertices]
              simp
            simpa [Sym2.toFinset_mk_eq] using this
          have hb : b = c ∨ b = d := by
            have : b ∈ s(c, d).toFinset := by
              rw [← hvertices]
              simp
            simpa [Sym2.toFinset_mk_eq] using this
          rw [Sym2.eq_iff]
          rcases ha with hac | had <;> rcases hb with hbc | hbd
          · exact (hab (hac.trans hbc.symm)).elim
          · exact Or.inl ⟨hac, hbd⟩
          · exact Or.inr ⟨had, hbc⟩
          · exact (hab (had.trans hbd.symm)).elim

private theorem card_edgesInside_le_one_of_card_eq_two
    (F : SimpleEdgeSet V) {X : Finset V} (hX : X.card = 2) :
    (edgesInside F X).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he f hf
  apply Subtype.ext
  apply tightCompletion_sym2_eq_of_toFinset_eq e.2 f.2
  have heX := (mem_edgesInside.mp he).2
  have hfX := (mem_edgesInside.mp hf).2
  have heCard : e.vertices.card = X.card := by simp [hX]
  have hfCard : f.vertices.card = X.card := by simp [hX]
  have heEq : e.vertices = X :=
    Finset.eq_of_subset_of_card_le heX (by omega)
  have hfEq : f.vertices = X :=
    Finset.eq_of_subset_of_card_le hfX (by omega)
  exact heEq.trans hfEq.symm

private theorem tight22_card_ne_two
    {F : SimpleEdgeSet V} {X : Finset V} (hX : Tight22 F X) :
    X.card ≠ 2 := by
  intro hcard
  have hle := card_edgesInside_le_one_of_card_eq_two F hcard
  rw [hX.2, hcard] at hle
  omega

/-- A maximum-cardinality sparse superset of `F` inside `J`. -/
structure IsMaximumSparseSuperedge
    (F J G : SimpleEdgeSet V) : Prop where
  base_subset : F ⊆ G
  universe_subset : G ⊆ J
  sparse : Sparse22 G
  card_max : ∀ {K : SimpleEdgeSet V},
    F ⊆ K → K ⊆ J → Sparse22 K → K.card ≤ G.card

/-- Sparse supersets of `F` contained in `J`. -/
noncomputable def sparseSuperedges
    (F J : SimpleEdgeSet V) : Finset (SimpleEdgeSet V) := by
  classical
  exact J.powerset.filter fun G => F ⊆ G ∧ Sparse22 G

@[simp]
theorem mem_sparseSuperedges {F J G : SimpleEdgeSet V} :
    G ∈ sparseSuperedges F J ↔ G ⊆ J ∧ F ⊆ G ∧ Sparse22 G := by
  classical
  simp [sparseSuperedges]

theorem exists_isMaximumSparseSuperedge
    {F J : SimpleEdgeSet V} (hFJ : F ⊆ J) (hF : Sparse22 F) :
    ∃ G : SimpleEdgeSet V, IsMaximumSparseSuperedge F J G := by
  classical
  have hne : (sparseSuperedges F J).Nonempty := by
    refine ⟨F, ?_⟩
    exact mem_sparseSuperedges.mpr ⟨hFJ, Finset.Subset.rfl, hF⟩
  obtain ⟨G, hGmem, hGmax⟩ :=
    Finset.exists_max_image (sparseSuperedges F J) Finset.card hne
  have hG := mem_sparseSuperedges.mp hGmem
  refine ⟨G, hG.2.1, hG.1, hG.2.2, ?_⟩
  intro K hFK hKJ hKsparse
  exact hGmax K (mem_sparseSuperedges.mpr ⟨hKJ, hFK, hKsparse⟩)

theorem IsMaximumSparseSuperedge.not_sparse_insert
    {F J G : SimpleEdgeSet V} (hG : IsMaximumSparseSuperedge F J G)
    {e : SimpleEdge V} (heJ : e ∈ J) (heG : e ∉ G) :
    ¬ Sparse22 (insert e G) := by
  intro hins
  have hbase : F ⊆ insert e G := hG.base_subset.trans (Finset.subset_insert e G)
  have huniv : insert e G ⊆ J := Finset.insert_subset heJ hG.universe_subset
  have hcard := hG.card_max hbase huniv hins
  rw [Finset.card_insert_of_notMem heG] at hcard
  omega

/-- Every omitted complete-universe edge is internal to the tight partition. -/
theorem IsMaximumSparseSuperedge.internal_missing_edge
    [Fintype V]
    {F J G : SimpleEdgeSet V} (hG : IsMaximumSparseSuperedge F J G)
    {e : SimpleEdge V} (heJ : e ∈ J) (heG : e ∉ G) :
    InternalTo (tightPartition G hG.sparse) e := by
  obtain ⟨X, hXne, heX, hXtight⟩ :=
    exists_tight22_of_not_sparse22_insert hG.sparse heG
      (hG.not_sparse_insert heJ heG)
  obtain ⟨v, hvX⟩ := hXne
  refine ⟨(tightPartition G hG.sparse).part v, ?_, ?_⟩
  · exact (tightPartition G hG.sparse).part_mem.mpr (by simp)
  · rw [tightPartition_part_eq_tightHull]
    exact heX.trans (tight_subset_tightHull hXtight hvX)

/-- Edges induced by `A ∪ B` which are internal to neither side. -/
def betweenEdges (F : SimpleEdgeSet V) (A B : Finset V) : SimpleEdgeSet V :=
  edgesInside F (A ∪ B) \ (edgesInside F A ∪ edgesInside F B)

@[simp]
theorem mem_betweenEdges
    {F : SimpleEdgeSet V} {A B : Finset V} {e : SimpleEdge V} :
    e ∈ betweenEdges F A B ↔
      e ∈ F ∧ e.vertices ⊆ A ∪ B ∧
        ¬ e.vertices ⊆ A ∧ ¬ e.vertices ⊆ B := by
  simp only [betweenEdges, Finset.mem_sdiff, Finset.mem_union, mem_edgesInside]
  aesop

/-- Two disjoint tight sets can have at most two edges between them. -/
theorem card_betweenEdges_le_two_of_disjoint_tight
    {F : SimpleEdgeSet V} {A B : Finset V}
    (hF : Sparse22 F) (hA : Tight22 F A) (hB : Tight22 F B)
    (hAB : Disjoint A B) :
    (betweenEdges F A B).card ≤ 2 := by
  have hEdgeDisjoint : Disjoint (edgesInside F A) (edgesInside F B) := by
    rw [Finset.disjoint_left]
    intro e heA heB
    have hverts : e.vertices.Nonempty := Finset.card_pos.mp (by simp)
    obtain ⟨v, hv⟩ := hverts
    exact (Finset.disjoint_left.mp hAB)
      ((mem_edgesInside.mp heA).2 hv) ((mem_edgesInside.mp heB).2 hv)
  have hInternalSubset :
      edgesInside F A ∪ edgesInside F B ⊆ edgesInside F (A ∪ B) :=
    union_edgesInside_subset F A B
  have hUnionNonempty : (A ∪ B).Nonempty :=
    hA.1.mono Finset.subset_union_left
  have hSparseUnion := hF (A ∪ B) hUnionNonempty
  have hVertexCard : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint hAB
  rw [hVertexCard] at hSparseUnion
  unfold betweenEdges
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hInternalSubset,
    Finset.card_union_of_disjoint hEdgeDisjoint, hA.2, hB.2]
  have hApos : 0 < A.card := Finset.card_pos.mpr hA.1
  have hBpos : 0 < B.card := Finset.card_pos.mpr hB.1
  omega

/-- Join every vertex of `A` to one vertex outside `A`. -/
def starEdgeEmbedding (A : Finset V) (b : V) (hb : b ∉ A) :
    {a // a ∈ A} ↪ SimpleEdge V where
  toFun a := ⟨s(a.1, b), by
    rw [Sym2.mk_isDiag_iff]
    intro hab
    exact hb (hab ▸ a.2)⟩
  inj' := by
    intro a c hac
    apply Subtype.ext
    have hp : s(a.1, b) = s(c.1, b) := congr_arg Subtype.val hac
    rw [Sym2.eq_iff] at hp
    rcases hp with hp | hp
    · exact hp.1
    · exact (hb (hp.1 ▸ a.2)).elim

/-- The simple star from `A` to an outside vertex `b`. -/
noncomputable def starEdges (A : Finset V) (b : V) (hb : b ∉ A) :
    SimpleEdgeSet V := by
  classical
  exact Finset.univ.map (starEdgeEmbedding A b hb)

omit [DecidableEq V] in
@[simp]
theorem card_starEdges (A : Finset V) (b : V) (hb : b ∉ A) :
    (starEdges A b hb).card = A.card := by
  classical
  simp [starEdges]

omit [DecidableEq V] in
@[simp]
theorem mem_starEdges_iff (A : Finset V) (b : V) (hb : b ∉ A)
    (e : SimpleEdge V) :
    e ∈ starEdges A b hb ↔
      ∃ a : V, a ∈ A ∧ e.1 = s(a, b) := by
  classical
  simp only [starEdges, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, a.2, rfl⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact he.symm

def completeEdgeEquivForTightCompletion [Fintype V] :
    (⊤ : SimpleGraph V).edgeFinset ≃ SimpleEdge V where
  toFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet] using e.2⟩
  invFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet] using e.2⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

private theorem card_univ_simpleEdges [Fintype V] :
    (Finset.univ : SimpleEdgeSet V).card = (Fintype.card V).choose 2 := by
  rw [Finset.card_univ]
  calc
    Fintype.card (SimpleEdge V) =
        Fintype.card (⊤ : SimpleGraph V).edgeFinset :=
      Fintype.card_congr completeEdgeEquivForTightCompletion.symm
    _ = (⊤ : SimpleGraph V).edgeFinset.card :=
      Fintype.card_coe (⊤ : SimpleGraph V).edgeFinset
    _ = (Fintype.card V).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two

private theorem IsMaximumSparseSuperedge.starEdges_subset_betweenEdges
    [Fintype V]
    {F G : SimpleEdgeSet V}
    (hG : IsMaximumSparseSuperedge F (Finset.univ : SimpleEdgeSet V) G)
    (A B : (tightPartition G hG.sparse).parts) (hAB : A ≠ B)
    (b : V) (hbB : b ∈ B.1) (hbA : b ∉ A.1) :
    starEdges A.1 b hbA ⊆ betweenEdges G A.1 B.1 := by
  intro e heStar
  obtain ⟨a, haA, heval⟩ := (mem_starEdges_iff A.1 b hbA e).mp heStar
  let ea : SimpleEdge V := starEdgeEmbedding A.1 b hbA ⟨a, haA⟩
  have heq : e = ea := by
    apply Subtype.ext
    exact heval
  subst e
  have hab : a ≠ b := by
    intro hab
    exact hbA (hab ▸ haA)
  have haNotB : a ∉ B.1 := by
    have hABval : A.1 ≠ B.1 := fun h => hAB (Subtype.ext h)
    exact (Finset.disjoint_left.mp
      ((tightPartition G hG.sparse).disjoint A.2 B.2 hABval)) haA
  have hnotInternal : ¬ InternalTo (tightPartition G hG.sparse) ea := by
    rintro ⟨X, hX, heX⟩
    have haX : a ∈ X := heX (by
      simp [ea, starEdgeEmbedding, SimpleEdge.vertices, Sym2.toFinset_mk_eq])
    have hbX : b ∈ X := heX (by
      simp [ea, starEdgeEmbedding, SimpleEdge.vertices, Sym2.toFinset_mk_eq])
    have hAX : A.1 = X := by
      exact ((tightPartition G hG.sparse).part_eq_of_mem A.2 haA).symm.trans
        ((tightPartition G hG.sparse).part_eq_of_mem hX haX)
    have hBX : B.1 = X := by
      exact ((tightPartition G hG.sparse).part_eq_of_mem B.2 hbB).symm.trans
        ((tightPartition G hG.sparse).part_eq_of_mem hX hbX)
    apply hAB
    apply Subtype.ext
    exact hAX.trans hBX.symm
  have heaG : ea ∈ G := by
    by_contra heaG
    exact hnotInternal (hG.internal_missing_edge (by simp) heaG)
  rw [mem_betweenEdges]
  refine ⟨heaG, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : v = a ∨ v = b := by
      have : v ∈ ea.1 := Sym2.mem_toFinset.mp hv
      simpa [ea, starEdgeEmbedding] using this
    rcases hv' with hva | hvb
    · subst v
      exact Finset.mem_union_left _ haA
    · subst v
      exact Finset.mem_union_right _ hbB
  · intro hsub
    exact hbA (hsub (by
      simp [ea, starEdgeEmbedding, SimpleEdge.vertices, Sym2.toFinset_mk_eq]))
  · intro hsub
    exact haNotB (hsub (by
      simp [ea, starEdgeEmbedding, SimpleEdge.vertices, Sym2.toFinset_mk_eq]))

/--
Every `(2,2)`-sparse simple edge set on at least four vertices has a
same-vertex `(2,2)`-tight completion.
-/
theorem exists_tight22_completion
    [Fintype V]
    (F : SimpleEdgeSet V) (hF : Sparse22 F) (hcard : 4 ≤ Fintype.card V) :
    ∃ G : SimpleEdgeSet V,
      F ⊆ G ∧ Sparse22 G ∧ Tight22 G (Finset.univ : Finset V) := by
  classical
  let J : SimpleEdgeSet V := Finset.univ
  obtain ⟨G, hG⟩ := exists_isMaximumSparseSuperedge
    (F := F) (J := J) (by simp [J]) hF
  refine ⟨G, hG.base_subset, hG.sparse, ?_⟩
  have hUnivNonempty : (Finset.univ : Finset V).Nonempty := by
    apply Finset.card_pos.mp
    simp only [Finset.card_univ]
    omega
  refine ⟨hUnivNonempty, ?_⟩
  by_contra hnotTight
  have hGupper := hG.sparse (Finset.univ : Finset V) hUnivNonempty
  have hGstrict : G.card < 2 * (Fintype.card V - 1) := by
    have hInside : edgesInside G (Finset.univ : Finset V) = G := by
      ext e
      simp [edgesInside]
    rw [hInside, Finset.card_univ] at hGupper hnotTight
    omega
  let P := tightPartition G hG.sparse
  have hpartsTwo : 2 ≤ P.parts.card := by
    by_contra hnotTwo
    have hpartsNonempty : P.parts.Nonempty := by
      obtain ⟨v, hv⟩ := hUnivNonempty
      exact ⟨P.part v, P.part_mem.mpr (by simp)⟩
    have hpartsCard : P.parts.card = 1 := by
      have hpos := Finset.card_pos.mpr hpartsNonempty
      omega
    obtain ⟨X, hpartsEq⟩ := Finset.card_eq_one.mp hpartsCard
    have hXmem : X ∈ P.parts := by simp [hpartsEq]
    have hXuniv : X = (Finset.univ : Finset V) := by
      apply Finset.eq_univ_of_forall
      intro v
      have hvpart : P.part v ∈ P.parts := P.part_mem.mpr (by simp)
      have hvpartEq : P.part v = X := by
        rw [hpartsEq] at hvpart
        simpa using hvpart
      rw [← hvpartEq]
      exact P.mem_part (by simp)
    have hXtight : Tight22 G X := by
      exact tight_of_mem_tightPartition hG.sparse hXmem
    rw [hXuniv] at hXtight
    exact hnotTight hXtight.2
  by_cases hlarge : ∃ A : P.parts, 1 < A.1.card
  · obtain ⟨A, hAcardTwo⟩ := hlarge
    have hAtight : Tight22 G A.1 := by
      exact tight_of_mem_tightPartition hG.sparse A.2
    have hAcardThree : 3 ≤ A.1.card := by
      have hAneTwo := tight22_card_ne_two hAtight
      omega
    obtain ⟨B0, hB0mem, hB0ne⟩ :=
      Finset.exists_mem_ne (by omega : 1 < P.parts.card) A.1
    let B : P.parts := ⟨B0, hB0mem⟩
    have hAB : A ≠ B := by
      intro hEq
      exact hB0ne (congr_arg Subtype.val hEq).symm
    have hABval : A.1 ≠ B.1 := fun hEq => hAB (Subtype.ext hEq)
    have hABdisjoint : Disjoint A.1 B.1 := P.disjoint A.2 B.2 hABval
    obtain ⟨b, hbB⟩ := P.nonempty_of_mem_parts B.2
    have hbA : b ∉ A.1 := by
      intro hbA
      exact (Finset.disjoint_left.mp hABdisjoint) hbA hbB
    have hstarSubset :
        starEdges A.1 b hbA ⊆ betweenEdges G A.1 B.1 := by
      exact hG.starEdges_subset_betweenEdges A B hAB b hbB hbA
    have hstarCard : A.1.card ≤ (betweenEdges G A.1 B.1).card := by
      rw [← card_starEdges A.1 b hbA]
      exact Finset.card_le_card hstarSubset
    have hBtight : Tight22 G B.1 := by
      exact tight_of_mem_tightPartition hG.sparse B.2
    have hbetween := card_betweenEdges_le_two_of_disjoint_tight
      hG.sparse hAtight hBtight hABdisjoint
    omega
  · have hcompleteBudget :
        2 * (Fintype.card V - 1) ≤
          (Finset.univ : SimpleEdgeSet V).card := by
      rw [card_univ_simpleEdges]
      exact two_mul_card_sub_one_le_choose_two hcard
    have hGcardLt : G.card < (Finset.univ : SimpleEdgeSet V).card :=
      hGstrict.trans_le hcompleteBudget
    have hGne : G ≠ (Finset.univ : SimpleEdgeSet V) := by
      intro hEq
      rw [hEq] at hGcardLt
      omega
    have hGproper : G ⊂ (Finset.univ : SimpleEdgeSet V) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨by simp, hGne⟩
    obtain ⟨e, heUniv, heG⟩ := Finset.exists_of_ssubset hGproper
    have heInternal : InternalTo P e := by
      exact hG.internal_missing_edge (by simp [J]) heG
    obtain ⟨X, hXmem, heX⟩ := heInternal
    have hXcard : X.card ≤ 1 := by
      have hnotLarge : ¬ 1 < X.card := by
        intro hXlarge
        apply hlarge
        exact ⟨⟨X, hXmem⟩, hXlarge⟩
      omega
    have hvertices := Finset.card_le_card heX
    rw [e.card_vertices] at hvertices
    omega

end RB31E2E


end
end BundleSource0007

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0007/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0007.json"

section BundleSource0008
/- Source: Papers/RigidityZheng_Combinatorics_Sparse22_Construction.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/Sparse22/Construction.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Nixon--Owen reductions for simple `(2,2)`-tight graphs

This file gives literal edge-set semantics to the four inverse moves in
Nixon--Owen's construction theorem: inverse Henneberg 1, inverse
Henneberg 2, `K₄`-to-vertex, and `K₃`-to-edge.  A graph is represented by
an ambient simple edge set together with its active vertex set.  The
`SupportedOn` condition is load bearing: `Tight22 F X` alone only counts
the edges of `F` induced by `X` and does not rule out edges outside `X`.

The first reduction branch is closed below: deleting any degree-two
vertex of a supported `(2,2)`-tight graph produces a strictly smaller
supported `(2,2)`-tight graph.  The full Nixon--Owen reduction disjunction
additionally needs the degree-three admissibility and triangle-sequence
arguments.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- Every edge of `F` has both endpoints in the active vertex set `X`. -/
def SupportedOn (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  ∀ ⦃e : SimpleEdge V⦄, e ∈ F → e.vertices ⊆ X

/-- A simple `(2,2)`-tight graph on an explicit active vertex set. -/
structure SimpleTight22On (F : SimpleEdgeSet V) (X : Finset V) : Prop where
  supported : SupportedOn F X
  sparse : Sparse22 F
  tight : Tight22 F X

theorem edgesInside_eq_self_of_supported {F : SimpleEdgeSet V} {X : Finset V}
    (hF : SupportedOn F X) : edgesInside F X = F := by
  ext e
  simp only [mem_edgesInside]
  constructor
  · exact And.left
  · intro he
    exact ⟨he, hF he⟩

/-- Edges incident with `v`. -/
def incidentEdges (F : SimpleEdgeSet V) (v : V) : SimpleEdgeSet V :=
  F.filter fun e => v ∈ e.vertices

/-- The degree of `v` in the simple edge set `F`. -/
def edgeSetDegree (F : SimpleEdgeSet V) (v : V) : ℕ :=
  (incidentEdges F v).card

/-- Delete `v` and every edge incident with it. -/
def deleteVertexEdges (F : SimpleEdgeSet V) (v : V) : SimpleEdgeSet V :=
  F.filter fun e => v ∉ e.vertices

@[simp]
theorem mem_incidentEdges {F : SimpleEdgeSet V} {v : V} {e : SimpleEdge V} :
    e ∈ incidentEdges F v ↔ e ∈ F ∧ v ∈ e.vertices := by
  simp [incidentEdges]

@[simp]
theorem mem_deleteVertexEdges {F : SimpleEdgeSet V} {v : V} {e : SimpleEdge V} :
    e ∈ deleteVertexEdges F v ↔ e ∈ F ∧ v ∉ e.vertices := by
  simp [deleteVertexEdges]

theorem deleteVertexEdges_subset (F : SimpleEdgeSet V) (v : V) :
    deleteVertexEdges F v ⊆ F := by
  intro e he
  exact (mem_deleteVertexEdges.mp he).1

theorem incidentEdges_disjoint_deleteVertexEdges (F : SimpleEdgeSet V) (v : V) :
    Disjoint (incidentEdges F v) (deleteVertexEdges F v) := by
  rw [Finset.disjoint_left]
  intro e heIncident heDelete
  exact (mem_deleteVertexEdges.mp heDelete).2 (mem_incidentEdges.mp heIncident).2

theorem incidentEdges_union_deleteVertexEdges (F : SimpleEdgeSet V) (v : V) :
    incidentEdges F v ∪ deleteVertexEdges F v = F := by
  ext e
  by_cases hev : v ∈ e.vertices <;> simp [hev]

theorem card_incidentEdges_add_card_deleteVertexEdges
    (F : SimpleEdgeSet V) (v : V) :
    (incidentEdges F v).card + (deleteVertexEdges F v).card = F.card := by
  rw [← Finset.card_union_of_disjoint
    (incidentEdges_disjoint_deleteVertexEdges F v)]
  rw [incidentEdges_union_deleteVertexEdges]

theorem deleteVertexEdges_supported {F : SimpleEdgeSet V} {X : Finset V} {v : V}
    (hF : SupportedOn F X) :
    SupportedOn (deleteVertexEdges F v) (X.erase v) := by
  intro e he y hy
  have heF := (mem_deleteVertexEdges.mp he).1
  have hvNot := (mem_deleteVertexEdges.mp he).2
  rw [Finset.mem_erase]
  exact ⟨fun hyv => hvNot (hyv ▸ hy), hF heF hy⟩

theorem edgesInside_deleteVertexEdges_erase {F : SimpleEdgeSet V} {X : Finset V} {v : V}
    (hF : SupportedOn F X) :
    edgesInside (deleteVertexEdges F v) (X.erase v) = deleteVertexEdges F v :=
  edgesInside_eq_self_of_supported (deleteVertexEdges_supported hF)

theorem edgesInside_erase_eq_deleteVertexEdges
    {F : SimpleEdgeSet V} {X : Finset V} {v : V}
    (hF : SupportedOn F X) :
    edgesInside F (X.erase v) = deleteVertexEdges F v := by
  ext e
  simp only [mem_edgesInside, mem_deleteVertexEdges]
  constructor
  · rintro ⟨heF, heX⟩
    refine ⟨heF, ?_⟩
    intro hv
    exact (Finset.mem_erase.mp (heX hv)).1 rfl
  · rintro ⟨heF, hv⟩
    refine ⟨heF, ?_⟩
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun hyv => hv (hyv ▸ hy), hF heF hy⟩

theorem edgesInside_deleteVertexEdges_erase_eq
    (F : SimpleEdgeSet V) (Y : Finset V) (v : V) :
    edgesInside (deleteVertexEdges F v) (Y.erase v) =
      edgesInside (deleteVertexEdges F v) Y := by
  ext e
  simp only [mem_edgesInside, mem_deleteVertexEdges]
  constructor
  · rintro ⟨⟨heF, hvNot⟩, heY⟩
    exact ⟨⟨heF, hvNot⟩, heY.trans (Finset.erase_subset v Y)⟩
  · rintro ⟨⟨heF, hvNot⟩, heY⟩
    refine ⟨⟨heF, hvNot⟩, ?_⟩
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun hyv => hvNot (hyv ▸ hy), heY hy⟩

/-- A tight blocking set in a vertex-deleted graph cannot contain the deleted vertex. -/
theorem not_mem_of_tight22_deleteVertexEdges
    {F : SimpleEdgeSet V} {Y : Finset V} {v a : V}
    (hSparse : Sparse22 (deleteVertexEdges F v))
    (hTight : Tight22 (deleteVertexEdges F v) Y)
    (haY : a ∈ Y) (hva : v ≠ a) :
    v ∉ Y := by
  intro hvY
  have hEraseNonempty : (Y.erase v).Nonempty :=
    ⟨a, Finset.mem_erase.mpr ⟨Ne.symm hva, haY⟩⟩
  have hUpper := hSparse (Y.erase v) hEraseNonempty
  rw [edgesInside_deleteVertexEdges_erase_eq F Y v, hTight.2] at hUpper
  have hEraseCard := Finset.card_erase_of_mem hvY
  have hYcardTwo : 2 ≤ Y.card := by
    exact Finset.one_lt_card.mpr ⟨v, hvY, a, haY, hva⟩
  omega

/--
Exact local degree bookkeeping: after adjoining `v` to a set `Y` not
containing it, the induced edges split into the incident edges at `v` and
the old vertex-deleted induced edges, provided all incident edges land in
`insert v Y`.
-/
theorem card_edgesInside_insert_eq_degree_add
    (F : SimpleEdgeSet V) (Y : Finset V) (v : V) (hvY : v ∉ Y)
    (hIncident : SupportedOn (incidentEdges F v) (insert v Y)) :
    (edgesInside F (insert v Y)).card =
      edgeSetDegree F v + (edgesInside (deleteVertexEdges F v) Y).card := by
  have hSplit :
      edgesInside F (insert v Y) =
        edgesInside (incidentEdges F v) (insert v Y) ∪
          edgesInside (deleteVertexEdges F v) (insert v Y) := by
    ext e
    simp only [mem_edgesInside, mem_incidentEdges, mem_deleteVertexEdges,
      Finset.mem_union]
    constructor
    · rintro ⟨heF, heZ⟩
      by_cases hev : v ∈ e.vertices
      · exact Or.inl ⟨⟨heF, hev⟩, heZ⟩
      · exact Or.inr ⟨⟨heF, hev⟩, heZ⟩
    · rintro (⟨⟨heF, _hev⟩, heZ⟩ | ⟨⟨heF, _hev⟩, heZ⟩) <;>
        exact ⟨heF, heZ⟩
  have hDeleteInside :
      edgesInside (deleteVertexEdges F v) (insert v Y) =
        edgesInside (deleteVertexEdges F v) Y := by
    ext e
    simp only [mem_edgesInside, mem_deleteVertexEdges]
    constructor
    · rintro ⟨⟨heF, hev⟩, heZ⟩
      refine ⟨⟨heF, hev⟩, ?_⟩
      intro y hy
      have hyZ := heZ hy
      rw [Finset.mem_insert] at hyZ
      rcases hyZ with rfl | hyY
      · exact (hev hy).elim
      · exact hyY
    · rintro ⟨he, heY⟩
      exact ⟨he, heY.trans (Finset.subset_insert v Y)⟩
  have hDisjoint :
      Disjoint (edgesInside (incidentEdges F v) (insert v Y))
        (edgesInside (deleteVertexEdges F v) (insert v Y)) := by
    rw [Finset.disjoint_left]
    intro e heIncident heDelete
    exact (mem_deleteVertexEdges.mp (mem_edgesInside.mp heDelete).1).2
      (mem_incidentEdges.mp (mem_edgesInside.mp heIncident).1).2
  rw [hSplit, Finset.card_union_of_disjoint hDisjoint,
    edgesInside_eq_self_of_supported hIncident, hDeleteInside]
  rfl

/-- A simple edge with ordered input and unordered output. -/
def simpleEdge (a b : V) (hab : a ≠ b) : SimpleEdge V :=
  ⟨s(a, b), by simpa [Sym2.mk_isDiag_iff]⟩

@[simp]
theorem vertices_simpleEdge (a b : V) (hab : a ≠ b) :
    (simpleEdge a b hab).vertices = {a, b} := by
  simp [simpleEdge, SimpleEdge.vertices, Sym2.toFinset_mk_eq]

omit [DecidableEq V] in
@[simp]
theorem simpleEdge_eq_simpleEdge_iff
    (a b c d : V) (hab : a ≠ b) (hcd : c ≠ d) :
    simpleEdge a b hab = simpleEdge c d hcd ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  simp only [simpleEdge, Subtype.mk.injEq, Sym2.eq_iff]

omit [DecidableEq V] in
theorem simpleEdge_comm (a b : V) (hab : a ≠ b) :
    simpleEdge a b hab = simpleEdge b a (Ne.symm hab) := by
  apply Subtype.ext
  simp [simpleEdge]

theorem sym2_eq_of_toFinset_eq
    {e f : Sym2 V} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (hvertices : e.toFinset = f.toFinset) : e = f := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      induction f using Sym2.inductionOn with
      | _ c d =>
          have hab : a ≠ b := by
            simpa [Sym2.mk_isDiag_iff] using he
          have hcd : c ≠ d := by
            simpa [Sym2.mk_isDiag_iff] using hf
          have ha : a = c ∨ a = d := by
            have : a ∈ s(c, d).toFinset := by
              rw [← hvertices]
              simp
            simpa [Sym2.toFinset_mk_eq] using this
          have hb : b = c ∨ b = d := by
            have : b ∈ s(c, d).toFinset := by
              rw [← hvertices]
              simp
            simpa [Sym2.toFinset_mk_eq] using this
          rw [Sym2.eq_iff]
          rcases ha with hac | had <;> rcases hb with hbc | hbd
          · exact (hab (hac.trans hbc.symm)).elim
          · exact Or.inl ⟨hac, hbd⟩
          · exact Or.inr ⟨had, hbc⟩
          · exact (hab (had.trans hbd.symm)).elim

theorem SimpleEdge.eq_of_vertices_eq {e f : SimpleEdge V}
    (hvertices : e.vertices = f.vertices) : e = f := by
  apply Subtype.ext
  exact sym2_eq_of_toFinset_eq e.2 f.2 hvertices

/-- An incident simple edge has a unique other endpoint. -/
theorem exists_otherEndpoint (e : SimpleEdge V) {v : V}
    (hv : v ∈ e.vertices) :
    ∃ a : V, ∃ hva : v ≠ a, e = simpleEdge v a hva := by
  obtain ⟨a, ha, hav⟩ :=
    Finset.exists_mem_ne (by simp : 1 < e.vertices.card) v
  have hva : v ≠ a := Ne.symm hav
  have hPairSubset : {v, a} ⊆ e.vertices := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hv
    · exact ha
  have hPairCard : ({v, a} : Finset V).card = 2 := by simp [hva]
  have hVertices : e.vertices = {v, a} := by
    exact (Finset.eq_of_subset_of_card_le hPairSubset (by
      rw [hPairCard, e.card_vertices])).symm
  have hEdgeEq : e = simpleEdge v a hva := by
    apply SimpleEdge.eq_of_vertices_eq
    rw [hVertices, vertices_simpleEdge]
  exact ⟨a, hva, hEdgeEq⟩

/-- `F` contains every simple edge whose endpoints lie in `K`. -/
def IsCliqueEdgeSet (F : SimpleEdgeSet V) (K : Finset V) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, ∀ hab : a ≠ b, simpleEdge a b hab ∈ F

/-- Four named vertices, with all six simple edges, form a copy of `K₄`. -/
structure NamedK4Witness
    (F : SimpleEdgeSet V) (v a b c : V) : Prop where
  hva : v ≠ a
  hvb : v ≠ b
  hvc : v ≠ c
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  va_mem : simpleEdge v a hva ∈ F
  vb_mem : simpleEdge v b hvb ∈ F
  vc_mem : simpleEdge v c hvc ∈ F
  ab_mem : simpleEdge a b hab ∈ F
  ac_mem : simpleEdge a c hac ∈ F
  bc_mem : simpleEdge b c hbc ∈ F

/-- Three named distinct neighbours exhaust a degree-three incidence set. -/
theorem incidentEdges_eq_three
    {F : SimpleEdgeSet V} {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F) :
    incidentEdges F v =
      {simpleEdge v a hva, simpleEdge v b hvb, simpleEdge v c hvc} := by
  let S : SimpleEdgeSet V :=
    {simpleEdge v a hva, simpleEdge v b hvb, simpleEdge v c hvc}
  have hSsub : S ⊆ incidentEdges F v := by
    intro e he
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact mem_incidentEdges.mpr ⟨hvaF, by simp⟩
    · exact mem_incidentEdges.mpr ⟨hvbF, by simp⟩
    · exact mem_incidentEdges.mpr ⟨hvcF, by simp⟩
  have hScard : S.card = 3 := by
    simp [S, hvb, hvc, hab, hac, hbc]
  have hIncidentCard : (incidentEdges F v).card = 3 := hDegree
  exact (Finset.eq_of_subset_of_card_le hSsub (by omega)).symm

/--
`F'` is the simple push-forward of `F` along `φ`.  Edges mapped to loops
have no witness in the simple target type, and coincident images are merged
by the set semantics.  Thus legality below detects precisely when a
contraction remains a simple tight graph.
-/
def IsSimpleEdgePushForward (φ : V → V)
    (F F' : SimpleEdgeSet V) : Prop :=
  ∀ e' : SimpleEdge V,
    e' ∈ F' ↔ ∃ e : SimpleEdge V, e ∈ F ∧ e'.1 = e.1.map φ

/-- Collapse all vertices of `K` to its retained representative `r`. -/
def collapseSet (K : Finset V) (r : V) (x : V) : V :=
  if x ∈ K then r else x

/-- Merge `b` into the retained vertex `a`. -/
def mergeVertex (a b x : V) : V :=
  if x = b then a else x

/-- The exact graph surgery underlying an inverse Henneberg 1 move. -/
def IsInverseHennebergOne
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ v : V,
    v ∈ X ∧ edgeSetDegree F v = 2 ∧
      X' = X.erase v ∧ F' = deleteVertexEdges F v

/-- The exact graph surgery underlying an inverse Henneberg 2 move. -/
def IsInverseHennebergTwo
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ v a b : V, ∃ hva : v ≠ a, ∃ hvb : v ≠ b, ∃ hab : a ≠ b,
    v ∈ X ∧ a ∈ X ∧ b ∈ X ∧
      edgeSetDegree F v = 3 ∧
      simpleEdge v a hva ∈ F ∧ simpleEdge v b hvb ∈ F ∧
      simpleEdge a b hab ∉ F ∧
      X' = X.erase v ∧
      F' = insert (simpleEdge a b hab) (deleteVertexEdges F v)

/--
The exact `K₄`-to-vertex contraction, inverse to vertex-to-`K₄`.
The representative `r` stays active; the other three clique vertices are
removed.  Parallel images are collapsed, so the separate legality predicate
below is essential.
-/
def IsInverseVertexToK4
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ K : Finset V, ∃ r : V,
    K.card = 4 ∧ K ⊆ X ∧ r ∈ K ∧ IsCliqueEdgeSet F K ∧
      X' = insert r (X \ K) ∧
      IsSimpleEdgePushForward (collapseSet K r) F F'

/-- Three distinct vertices span all three edges of a triangle. -/
def IsTriangleEdgeSet (F : SimpleEdgeSet V) (u a b : V) : Prop :=
  ∃ hua : u ≠ a, ∃ hub : u ≠ b, ∃ hab : a ≠ b,
    simpleEdge u a hua ∈ F ∧
      simpleEdge u b hub ∈ F ∧ simpleEdge a b hab ∈ F

/--
The exact `K₃`-to-edge contraction, inverse to edge-to-`K₃`: in the
triangle on `u,a,b`, vertex `b` is merged into `a`.  The two edges to `u`
coalesce to the retained edge and `ab` becomes a loop and disappears.
-/
def IsInverseEdgeToK3
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ u a b : V,
    u ∈ X ∧ a ∈ X ∧ b ∈ X ∧ IsTriangleEdgeSet F u a b ∧
      X' = X.erase b ∧
      IsSimpleEdgePushForward (mergeVertex a b) F F'

/-- An inverse Henneberg 1 move whose output remains simple `(2,2)`-tight. -/
def LegalInverseHennebergOne
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseHennebergOne F X F' X' ∧ SimpleTight22On F' X'

/-- An inverse Henneberg 2 move whose output remains simple `(2,2)`-tight. -/
def LegalInverseHennebergTwo
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseHennebergTwo F X F' X' ∧ SimpleTight22On F' X'

/-- An allowable `K₄`-to-vertex move. -/
def LegalInverseVertexToK4
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseVertexToK4 F X F' X' ∧ SimpleTight22On F' X'

/-- An allowable `K₃`-to-edge move. -/
def LegalInverseEdgeToK3
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseEdgeToK3 F X F' X' ∧ SimpleTight22On F' X'

/-- The literal four-way reduction conclusion of Nixon--Owen Lemma 3.11. -/
def HasNixonOwenReduction (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  ∃ F' : SimpleEdgeSet V, ∃ X' : Finset V,
    X'.card < X.card ∧
      (LegalInverseHennebergOne F X F' X' ∨
        LegalInverseHennebergTwo F X F' X' ∨
        LegalInverseVertexToK4 F X F' X' ∨
        LegalInverseEdgeToK3 F X F' X')

/-- The exact `K₄` base object, including its complete-edge semantics. -/
def IsK4Base (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  X.card = 4 ∧ SimpleTight22On F X ∧ IsCliqueEdgeSet F X

theorem IsInverseHennebergOne.card_lt
    {F F' : SimpleEdgeSet V} {X X' : Finset V}
    (h : IsInverseHennebergOne F X F' X') :
    X'.card < X.card := by
  obtain ⟨v, hv, _hDegree, rfl, _hEdges⟩ := h
  rw [Finset.card_erase_of_mem hv]
  exact Nat.sub_lt (Finset.card_pos.mpr ⟨v, hv⟩) (by decide)

theorem IsInverseHennebergTwo.card_lt
    {F F' : SimpleEdgeSet V} {X X' : Finset V}
    (h : IsInverseHennebergTwo F X F' X') :
    X'.card < X.card := by
  obtain ⟨v, _a, _b, _hva, _hvb, _hab, hv, _ha, _hb, _hDegree,
    _hvaF, _hvbF, _habF, rfl, _hEdges⟩ := h
  rw [Finset.card_erase_of_mem hv]
  exact Nat.sub_lt (Finset.card_pos.mpr ⟨v, hv⟩) (by decide)

theorem IsInverseVertexToK4.card_lt
    {F F' : SimpleEdgeSet V} {X X' : Finset V}
    (h : IsInverseVertexToK4 F X F' X') :
    X'.card < X.card := by
  obtain ⟨K, r, hKcard, hKX, hrK, _hClique, rfl, _hPush⟩ := h
  have hrNot : r ∉ X \ K := by simp [hrK]
  rw [Finset.card_insert_of_notMem hrNot,
    Finset.card_sdiff_of_subset hKX, hKcard]
  have hFourLe : 4 ≤ X.card := by
    rw [← hKcard]
    exact Finset.card_le_card hKX
  omega

theorem IsInverseEdgeToK3.card_lt
    {F F' : SimpleEdgeSet V} {X X' : Finset V}
    (h : IsInverseEdgeToK3 F X F' X') :
    X'.card < X.card := by
  obtain ⟨_u, _a, b, _hu, _ha, hb, _hTriangle, rfl, _hPush⟩ := h
  rw [Finset.card_erase_of_mem hb]
  exact Nat.sub_lt (Finset.card_pos.mpr ⟨b, hb⟩) (by decide)

/-- Every vertex of a supported tight graph with at least two vertices has degree at least two. -/
theorem two_le_edgeSetDegree_of_simpleTight22On
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v : V} (hv : v ∈ X) (hXcard : 2 ≤ X.card) :
    2 ≤ edgeSetDegree F v := by
  have hEraseNonempty : (X.erase v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcardZero : (X.erase v).card = 0 := by simp [hEmpty]
    rw [Finset.card_erase_of_mem hv] at hcardZero
    omega
  have hSparseErase := hG.sparse (X.erase v) hEraseNonempty
  rw [edgesInside_erase_eq_deleteVertexEdges hG.supported] at hSparseErase
  have hPartition := card_incidentEdges_add_card_deleteVertexEdges F v
  have hTotal : F.card = 2 * (X.card - 1) := by
    rw [← edgesInside_eq_self_of_supported hG.supported]
    exact hG.tight.2
  have hEraseCard := Finset.card_erase_of_mem hv
  unfold edgeSetDegree
  omega

/-- Handshaking for an edge set supported on its active vertex set. -/
theorem sum_edgeSetDegree_eq_twice_card
    {F : SimpleEdgeSet V} {X : Finset V} (hF : SupportedOn F X) :
    (∑ v ∈ X, edgeSetDegree F v) = 2 * F.card := by
  classical
  have hDegreeAsSum (v : V) :
      edgeSetDegree F v =
        ∑ e ∈ F, if v ∈ e.vertices then 1 else 0 := by
    rw [edgeSetDegree, incidentEdges, Finset.card_eq_sum_ones,
      Finset.sum_filter]
  calc
    (∑ v ∈ X, edgeSetDegree F v) =
        ∑ v ∈ X, ∑ e ∈ F, if v ∈ e.vertices then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact hDegreeAsSum v
    _ = ∑ e ∈ F, ∑ v ∈ X, if v ∈ e.vertices then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ F, e.vertices.card := by
      apply Finset.sum_congr rfl
      intro e he
      have hfilter : X.filter (fun v => v ∈ e.vertices) = e.vertices := by
        ext v
        simp only [Finset.mem_filter]
        exact and_iff_right_of_imp (fun hv => hF he hv)
      calc
        (∑ v ∈ X, if v ∈ e.vertices then 1 else 0) =
            (X.filter fun v => v ∈ e.vertices).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = e.vertices.card := congrArg Finset.card hfilter
    _ = ∑ _e ∈ F, 2 := by simp
    _ = 2 * F.card := by simp [Nat.mul_comm]

/-- Every nonempty supported tight graph has a vertex of degree at most three. -/
theorem exists_edgeSetDegree_le_three
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X) :
    ∃ v ∈ X, edgeSetDegree F v ≤ 3 := by
  by_contra hNoLow
  push Not at hNoLow
  have hLower :
      ∑ v ∈ X, 4 ≤ ∑ v ∈ X, edgeSetDegree F v := by
    exact Finset.sum_le_sum fun v hv => hNoLow v hv
  have hHandshake := sum_edgeSetDegree_eq_twice_card hG.supported
  have hTotal : F.card = 2 * (X.card - 1) := by
    rw [← edgesInside_eq_self_of_supported hG.supported]
    exact hG.tight.2
  have hXpos : 0 < X.card := Finset.card_pos.mpr hG.tight.1
  have hLower' :
      4 * X.card ≤ ∑ v ∈ X, edgeSetDegree F v := by
    simpa [Nat.mul_comm] using hLower
  rw [hHandshake, hTotal] at hLower'
  omega

/-- On at least two vertices, the low-degree vertex has degree exactly two or three. -/
theorem exists_edgeSetDegree_eq_two_or_three
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    ∃ v ∈ X, edgeSetDegree F v = 2 ∨ edgeSetDegree F v = 3 := by
  obtain ⟨v, hv, hUpper⟩ := exists_edgeSetDegree_le_three hG
  have hLower := two_le_edgeSetDegree_of_simpleTight22On hG hv hXcard
  exact ⟨v, hv, by omega⟩

/--
The degree-two branch of the Nixon--Owen reduction theorem.  No
admissibility hypothesis is needed: mere deletion preserves sparsity, and
the exact two-edge loss preserves tightness.
-/
theorem legalInverseHennebergOne_of_degree_two
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v : V} (hv : v ∈ X) (hDegree : edgeSetDegree F v = 2) :
    LegalInverseHennebergOne F X
      (deleteVertexEdges F v) (X.erase v) := by
  refine ⟨⟨v, hv, hDegree, rfl, rfl⟩, ?_⟩
  refine ⟨deleteVertexEdges_supported hG.supported,
    hG.sparse.mono (deleteVertexEdges_subset F v), ?_⟩
  have hPartition := card_incidentEdges_add_card_deleteVertexEdges F v
  have hTotal : F.card = 2 * (X.card - 1) := by
    rw [← edgesInside_eq_self_of_supported hG.supported]
    exact hG.tight.2
  have hEraseCard := Finset.card_erase_of_mem hv
  have hDeleteCard :
      (deleteVertexEdges F v).card = 2 * ((X.erase v).card - 1) := by
    unfold edgeSetDegree at hDegree
    omega
  have hEraseNonempty : (X.erase v).Nonempty := by
    apply Finset.card_pos.mp
    unfold edgeSetDegree at hDegree
    omega
  refine ⟨hEraseNonempty, ?_⟩
  rw [edgesInside_deleteVertexEdges_erase hG.supported]
  exact hDeleteCard

/--
Once a missing pair of neighbours is known to be admissible for sparsity,
the inverse Henneberg 2 surgery automatically has the correct global count
and active-vertex support.
-/
theorem legalInverseHennebergTwo_of_sparse_insert
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b : V} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hSparse :
      Sparse22 (insert (simpleEdge a b hab) (deleteVertexEdges F v))) :
    LegalInverseHennebergTwo F X
      (insert (simpleEdge a b hab) (deleteVertexEdges F v)) (X.erase v) := by
  refine ⟨?_, ?_⟩
  · exact ⟨v, a, b, hva, hvb, hab, hvX, haX, hbX, hDegree,
      hvaF, hvbF, habF, rfl, rfl⟩
  · refine ⟨?_, hSparse, ?_⟩
    · intro e he
      rw [Finset.mem_insert] at he
      rcases he with rfl | heDelete
      · rw [vertices_simpleEdge]
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_erase.mpr ⟨Ne.symm hva, haX⟩
        · exact Finset.mem_erase.mpr ⟨Ne.symm hvb, hbX⟩
      · exact deleteVertexEdges_supported hG.supported heDelete
    · have hCandidateDelete :
          simpleEdge a b hab ∉ deleteVertexEdges F v := by
        intro he
        exact habF (deleteVertexEdges_subset F v he)
      have hPartition := card_incidentEdges_add_card_deleteVertexEdges F v
      have hTotal : F.card = 2 * (X.card - 1) := by
        rw [← edgesInside_eq_self_of_supported hG.supported]
        exact hG.tight.2
      have hEraseCard := Finset.card_erase_of_mem hvX
      have hResultCard :
          (insert (simpleEdge a b hab) (deleteVertexEdges F v)).card =
            2 * ((X.erase v).card - 1) := by
        rw [Finset.card_insert_of_notMem hCandidateDelete]
        unfold edgeSetDegree at hDegree
        omega
      refine ⟨⟨a, Finset.mem_erase.mpr ⟨Ne.symm hva, haX⟩⟩, ?_⟩
      rw [edgesInside_eq_self_of_supported]
      · exact hResultCard
      · intro e he
        rw [Finset.mem_insert] at he
        rcases he with rfl | heDelete
        · rw [vertices_simpleEdge]
          intro y hy
          rw [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Finset.mem_erase.mpr ⟨Ne.symm hva, haX⟩
          · exact Finset.mem_erase.mpr ⟨Ne.symm hvb, hbX⟩
        · exact deleteVertexEdges_supported hG.supported heDelete

/--
Failure of a proposed inverse Henneberg 2 edge is witnessed by a tight
set in the vertex-deleted graph containing both proposed endpoints.  This
is the exact obstruction consumed by the Nixon--Owen uncrossing argument.
-/
theorem exists_tight22_obstruction_of_not_hennebergTwo_admissible
    {F : SimpleEdgeSet V} {v a b : V} (hva : v ≠ a) (hab : a ≠ b)
    (hSparseDelete : Sparse22 (deleteVertexEdges F v))
    (habF : simpleEdge a b hab ∉ F)
    (hBad :
      ¬ Sparse22 (insert (simpleEdge a b hab) (deleteVertexEdges F v))) :
    ∃ Y : Finset V,
      Y.Nonempty ∧ a ∈ Y ∧ b ∈ Y ∧ v ∉ Y ∧
        Tight22 (deleteVertexEdges F v) Y := by
  have habDelete : simpleEdge a b hab ∉ deleteVertexEdges F v := by
    intro he
    exact habF (deleteVertexEdges_subset F v he)
  obtain ⟨Y, hYne, hedgeY, hYtight⟩ :=
    exists_tight22_of_not_sparse22_insert hSparseDelete habDelete hBad
  have habVertices : (simpleEdge a b hab).vertices = {a, b} :=
    vertices_simpleEdge a b hab
  rw [habVertices] at hedgeY
  have haY : a ∈ Y := hedgeY (by simp)
  have hbY : b ∈ Y := hedgeY (by simp)
  have hvY : v ∉ Y :=
    not_mem_of_tight22_deleteVertexEdges hSparseDelete hYtight haY hva
  exact ⟨Y, hYne, haY, hbY, hvY, hYtight⟩

/--
Provenance-preserving degree-three dichotomy for one proposed neighbour
pair: either the inverse Henneberg 2 move is legal, or a concrete tight
blocking set containing that pair is returned.
-/
theorem legalInverseHennebergTwo_or_tightObstruction
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b : V} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (habF : simpleEdge a b hab ∉ F) :
    LegalInverseHennebergTwo F X
        (insert (simpleEdge a b hab) (deleteVertexEdges F v)) (X.erase v) ∨
      ∃ Y : Finset V,
        Y.Nonempty ∧ a ∈ Y ∧ b ∈ Y ∧ v ∉ Y ∧
          Tight22 (deleteVertexEdges F v) Y := by
  have hSparseDelete : Sparse22 (deleteVertexEdges F v) :=
    hG.sparse.mono (deleteVertexEdges_subset F v)
  by_cases hSparse :
      Sparse22 (insert (simpleEdge a b hab) (deleteVertexEdges F v))
  · exact Or.inl (legalInverseHennebergTwo_of_sparse_insert hG hva hvb hab
      hvX haX hbX hDegree hvaF hvbF habF hSparse)
  · exact Or.inr
      (exists_tight22_obstruction_of_not_hennebergTwo_admissible
        hva hab hSparseDelete habF hSparse)

/--
Nixon--Owen's degree-three admissibility argument in the branch where two
edges among the three neighbours already exist.  The third, missing edge
can always be inserted after deleting the degree-three vertex.
-/
theorem legalInverseHennebergTwo_of_other_two_neighbor_edges
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X) (hcX : c ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hacF : simpleEdge a c hac ∈ F)
    (hbcF : simpleEdge b c hbc ∈ F) :
    LegalInverseHennebergTwo F X
      (insert (simpleEdge a b hab) (deleteVertexEdges F v)) (X.erase v) := by
  rcases legalInverseHennebergTwo_or_tightObstruction hG hva hvb hab
      hvX haX hbX hDegree hvaF hvbF habF with hLegal | hBlocked
  · exact hLegal
  · obtain ⟨Y, hYne, haY, hbY, hvY, hYtight⟩ := hBlocked
    have hIncidentEq := incidentEdges_eq_three hva hvb hvc hab hac hbc
      hDegree hvaF hvbF hvcF
    have hcY : c ∉ Y := by
      intro hcY
      have hIncidentSupported :
          SupportedOn (incidentEdges F v) (insert v Y) := by
        intro e he
        rw [hIncidentEq] at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · rw [vertices_simpleEdge]
          simp [haY]
        · rw [vertices_simpleEdge]
          simp [hbY]
        · rw [vertices_simpleEdge]
          simp [hcY]
      have hCard := card_edgesInside_insert_eq_degree_add F Y v hvY hIncidentSupported
      have hSparseZ := hG.sparse (insert v Y) ⟨v, by simp⟩
      have hZcard : (insert v Y).card = Y.card + 1 := by
        rw [Finset.card_insert_of_notMem hvY]
      rw [hCard, hDegree, hYtight.2, hZcard] at hSparseZ
      have hYpos : 0 < Y.card := Finset.card_pos.mpr hYne
      omega
    let eac : SimpleEdge V := simpleEdge a c hac
    let ebc : SimpleEdge V := simpleEdge b c hbc
    let R : SimpleEdgeSet V := deleteVertexEdges F v
    have eacR : eac ∈ R := by
      rw [mem_deleteVertexEdges]
      refine ⟨hacF, ?_⟩
      rw [vertices_simpleEdge]
      simp [hva, hvc]
    have ebcR : ebc ∈ R := by
      rw [mem_deleteVertexEdges]
      refine ⟨hbcF, ?_⟩
      rw [vertices_simpleEdge]
      simp [hvb, hvc]
    have eacNew : eac ∈ edgesInside R (insert c Y) := by
      rw [mem_edgesInside]
      refine ⟨eacR, ?_⟩
      rw [vertices_simpleEdge]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_insert_of_mem haY
      · exact Finset.mem_insert_self _ _
    have ebcNew : ebc ∈ edgesInside R (insert c Y) := by
      rw [mem_edgesInside]
      refine ⟨ebcR, ?_⟩
      rw [vertices_simpleEdge]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_insert_of_mem hbY
      · exact Finset.mem_insert_self _ _
    have hPairCard : ({eac, ebc} : SimpleEdgeSet V).card = 2 := by
      simp [eac, ebc, hab, hac]
    have hPairDisjoint :
        Disjoint (edgesInside R Y) ({eac, ebc} : SimpleEdgeSet V) := by
      rw [Finset.disjoint_left]
      intro e heOld hePair
      simp only [Finset.mem_insert, Finset.mem_singleton] at hePair
      rcases hePair with rfl | rfl
      · exact hcY ((mem_edgesInside.mp heOld).2 (by simp [eac]))
      · exact hcY ((mem_edgesInside.mp heOld).2 (by simp [ebc]))
    have hUnionSubset :
        edgesInside R Y ∪ ({eac, ebc} : SimpleEdgeSet V) ⊆
          edgesInside R (insert c Y) := by
      intro e he
      rw [Finset.mem_union] at he
      rcases he with heOld | hePair
      · exact edgesInside_mono_vertices R (Finset.subset_insert c Y) heOld
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hePair
        rcases hePair with rfl | rfl
        · exact eacNew
        · exact ebcNew
    have hDeletedLower :
        (edgesInside R Y).card + 2 ≤
          (edgesInside R (insert c Y)).card := by
      rw [← hPairCard,
        ← Finset.card_union_of_disjoint hPairDisjoint]
      exact Finset.card_le_card hUnionSubset
    have hvInsertCY : v ∉ insert c Y := by
      simp [hvc, hvY]
    have hIncidentSupported :
        SupportedOn (incidentEdges F v) (insert v (insert c Y)) := by
      intro e he
      rw [hIncidentEq] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · rw [vertices_simpleEdge]
        simp [haY]
      · rw [vertices_simpleEdge]
        simp [hbY]
      · rw [vertices_simpleEdge]
        simp
    have hCard := card_edgesInside_insert_eq_degree_add
      F (insert c Y) v hvInsertCY hIncidentSupported
    have hSparseZ := hG.sparse (insert v (insert c Y)) ⟨v, by simp⟩
    have hCYcard : (insert c Y).card = Y.card + 1 := by
      rw [Finset.card_insert_of_notMem hcY]
    have hZcard : (insert v (insert c Y)).card = Y.card + 2 := by
      rw [Finset.card_insert_of_notMem hvInsertCY, hCYcard]
    rw [hCard, hDegree, hZcard] at hSparseZ
    dsimp [R] at hDeletedLower
    rw [hYtight.2] at hDeletedLower
    have hYpos : 0 < Y.card := Finset.card_pos.mpr hYne
    omega

/--
Nixon--Owen's second degree-three branch: if two consecutive neighbour
pairs are missing, at least one of the two corresponding inverse
Henneberg 2 moves is legal.  Two hypothetical blocking sets uncross along
their common neighbour; adjoining the deleted vertex to their tight union
then violates sparsity by one edge.
-/
theorem legalInverseHennebergTwo_of_two_missing_neighbor_edges
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X) (hcX : c ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hbcF : simpleEdge b c hbc ∉ F) :
    LegalInverseHennebergTwo F X
        (insert (simpleEdge a b hab) (deleteVertexEdges F v)) (X.erase v) ∨
      LegalInverseHennebergTwo F X
        (insert (simpleEdge b c hbc) (deleteVertexEdges F v)) (X.erase v) := by
  rcases legalInverseHennebergTwo_or_tightObstruction hG hva hvb hab
      hvX haX hbX hDegree hvaF hvbF habF with hLegalAB | hBlockedAB
  · exact Or.inl hLegalAB
  rcases legalInverseHennebergTwo_or_tightObstruction hG hvb hvc hbc
      hvX hbX hcX hDegree hvbF hvcF hbcF with hLegalBC | hBlockedBC
  · exact Or.inr hLegalBC
  obtain ⟨Yab, _hYabNe, haYab, hbYab, hvYab, hYabTight⟩ := hBlockedAB
  obtain ⟨Ybc, _hYbcNe, hbYbc, hcYbc, hvYbc, hYbcTight⟩ := hBlockedBC
  let R : SimpleEdgeSet V := deleteVertexEdges F v
  have hSparseR : Sparse22 R :=
    hG.sparse.mono (deleteVertexEdges_subset F v)
  have hInterNonempty : (Yab ∩ Ybc).Nonempty :=
    ⟨b, Finset.mem_inter.mpr ⟨hbYab, hbYbc⟩⟩
  have hUnionTight : Tight22 R (Yab ∪ Ybc) :=
    (tight22_union_inter hSparseR hYabTight hYbcTight hInterNonempty).1
  have hvUnion : v ∉ Yab ∪ Ybc := by
    simp [hvYab, hvYbc]
  have hIncidentEq := incidentEdges_eq_three hva hvb hvc hab hac hbc
    hDegree hvaF hvbF hvcF
  have hIncidentSupported :
      SupportedOn (incidentEdges F v) (insert v (Yab ∪ Ybc)) := by
    intro e he
    rw [hIncidentEq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [vertices_simpleEdge]
      simp [haYab]
    · rw [vertices_simpleEdge]
      simp [hbYab]
    · rw [vertices_simpleEdge]
      simp [hcYbc]
  have hCard := card_edgesInside_insert_eq_degree_add
    F (Yab ∪ Ybc) v hvUnion hIncidentSupported
  have hSparseZ := hG.sparse (insert v (Yab ∪ Ybc)) ⟨v, by simp⟩
  have hZcard :
      (insert v (Yab ∪ Ybc)).card = (Yab ∪ Ybc).card + 1 := by
    rw [Finset.card_insert_of_notMem hvUnion]
  rw [hCard, hDegree, hZcard] at hSparseZ
  have hUnionCount := hUnionTight.2
  dsimp [R] at hUnionCount
  rw [hUnionCount] at hSparseZ
  have hUnionPos : 0 < (Yab ∪ Ybc).card :=
    Finset.card_pos.mpr hUnionTight.1
  omega

/--
Formal Nixon--Owen Lemma 3.1 for three named neighbours: a degree-three
vertex is either contained in the `K₄` on those neighbours, or admits a
legal inverse Henneberg 2 move.  This theorem combines the one-missing and
two-missing obstruction arguments above.
-/
theorem named_degree_three_k4_or_legalInverseHennebergTwo
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X) (hcX : c ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F) :
    NamedK4Witness F v a b c ∨
      ∃ F' : SimpleEdgeSet V,
        LegalInverseHennebergTwo F X F' (X.erase v) := by
  by_cases hAB : simpleEdge a b hab ∈ F
  · by_cases hAC : simpleEdge a c hac ∈ F
    · by_cases hBC : simpleEdge b c hbc ∈ F
      · exact Or.inl ⟨hva, hvb, hvc, hab, hac, hbc,
          hvaF, hvbF, hvcF, hAB, hAC, hBC⟩
      · have hBA : simpleEdge b a (Ne.symm hab) ∈ F := by
          rw [← simpleEdge_comm a b hab]
          exact hAB
        have hCA : simpleEdge c a (Ne.symm hac) ∈ F := by
          rw [← simpleEdge_comm a c hac]
          exact hAC
        have hLegal := legalInverseHennebergTwo_of_other_two_neighbor_edges
          hG hvb hvc hva hbc (Ne.symm hab) (Ne.symm hac)
          hvX hbX hcX haX hDegree hvbF hvcF hvaF hBC hBA hCA
        exact Or.inr ⟨_, hLegal⟩
    · by_cases hBC : simpleEdge b c hbc ∈ F
      · have hCB : simpleEdge c b (Ne.symm hbc) ∈ F := by
          rw [← simpleEdge_comm b c hbc]
          exact hBC
        have hLegal := legalInverseHennebergTwo_of_other_two_neighbor_edges
          hG hva hvc hvb hac hab (Ne.symm hbc)
          hvX haX hcX hbX hDegree hvaF hvcF hvbF hAC hAB hCB
        exact Or.inr ⟨_, hLegal⟩
      · have hCB : simpleEdge c b (Ne.symm hbc) ∉ F := by
          rw [← simpleEdge_comm b c hbc]
          exact hBC
        rcases legalInverseHennebergTwo_of_two_missing_neighbor_edges
            hG hva hvc hvb hac hab (Ne.symm hbc)
            hvX haX hcX hbX hDegree hvaF hvcF hvbF hAC hCB with hLegal | hLegal
        · exact Or.inr ⟨_, hLegal⟩
        · exact Or.inr ⟨_, hLegal⟩
  · by_cases hBC : simpleEdge b c hbc ∈ F
    · by_cases hAC : simpleEdge a c hac ∈ F
      · have hLegal := legalInverseHennebergTwo_of_other_two_neighbor_edges
          hG hva hvb hvc hab hac hbc
          hvX haX hbX hcX hDegree hvaF hvbF hvcF hAB hAC hBC
        exact Or.inr ⟨_, hLegal⟩
      · have hCA : simpleEdge c a (Ne.symm hac) ∉ F := by
          rw [← simpleEdge_comm a c hac]
          exact hAC
        rcases legalInverseHennebergTwo_of_two_missing_neighbor_edges
            hG hvc hva hvb (Ne.symm hac) (Ne.symm hbc) hab
            hvX hcX haX hbX hDegree hvcF hvaF hvbF hCA hAB with hLegal | hLegal
        · exact Or.inr ⟨_, hLegal⟩
        · exact Or.inr ⟨_, hLegal⟩
    · rcases legalInverseHennebergTwo_of_two_missing_neighbor_edges
          hG hva hvb hvc hab hac hbc
          hvX haX hbX hcX hDegree hvaF hvbF hvcF hAB hBC with hLegal | hLegal
      · exact Or.inr ⟨_, hLegal⟩
      · exact Or.inr ⟨_, hLegal⟩

/-- Coordinate-free form of the preceding theorem for an arbitrary degree-three vertex. -/
theorem degree_three_k4_or_legalInverseHennebergTwo
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v : V} (hvX : v ∈ X) (hDegree : edgeSetDegree F v = 3) :
    (∃ a b c : V, NamedK4Witness F v a b c) ∨
      ∃ F' : SimpleEdgeSet V,
        LegalInverseHennebergTwo F X F' (X.erase v) := by
  have hIncidentCard : (incidentEdges F v).card = 3 := hDegree
  obtain ⟨e₁, e₂, e₃, he₁₂, he₁₃, he₂₃, hIncidentEq⟩ :=
    Finset.card_eq_three.mp hIncidentCard
  have he₁Incident : e₁ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  have he₂Incident : e₂ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  have he₃Incident : e₃ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  obtain ⟨a, hva, he₁⟩ :=
    exists_otherEndpoint e₁ (mem_incidentEdges.mp he₁Incident).2
  obtain ⟨b, hvb, he₂⟩ :=
    exists_otherEndpoint e₂ (mem_incidentEdges.mp he₂Incident).2
  obtain ⟨c, hvc, he₃⟩ :=
    exists_otherEndpoint e₃ (mem_incidentEdges.mp he₃Incident).2
  have hab : a ≠ b := by
    intro hab
    subst b
    apply he₁₂
    calc
      e₁ = simpleEdge v a hva := he₁
      _ = simpleEdge v a hvb := by rfl
      _ = e₂ := he₂.symm
  have hac : a ≠ c := by
    intro hac
    subst c
    apply he₁₃
    calc
      e₁ = simpleEdge v a hva := he₁
      _ = simpleEdge v a hvc := by rfl
      _ = e₃ := he₃.symm
  have hbc : b ≠ c := by
    intro hbc
    subst c
    apply he₂₃
    calc
      e₂ = simpleEdge v b hvb := he₂
      _ = simpleEdge v b hvc := by rfl
      _ = e₃ := he₃.symm
  have hvaF : simpleEdge v a hva ∈ F := by
    rw [← he₁]
    exact (mem_incidentEdges.mp he₁Incident).1
  have hvbF : simpleEdge v b hvb ∈ F := by
    rw [← he₂]
    exact (mem_incidentEdges.mp he₂Incident).1
  have hvcF : simpleEdge v c hvc ∈ F := by
    rw [← he₃]
    exact (mem_incidentEdges.mp he₃Incident).1
  have haX : a ∈ X := hG.supported hvaF (by simp)
  have hbX : b ∈ X := hG.supported hvbF (by simp)
  have hcX : c ∈ X := hG.supported hvcF (by simp)
  rcases named_degree_three_k4_or_legalInverseHennebergTwo
      hG hva hvb hvc hab hac hbc hvX haX hbX hcX
      hDegree hvaF hvbF hvcF with hK4 | hLegal
  · exact Or.inl ⟨a, b, c, hK4⟩
  · exact Or.inr hLegal

/-- A degree-two vertex supplies the first disjunct of the full reduction theorem. -/
theorem hasNixonOwenReduction_of_degree_two
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v : V} (hv : v ∈ X) (hDegree : edgeSetDegree F v = 2) :
    HasNixonOwenReduction F X := by
  refine ⟨deleteVertexEdges F v, X.erase v, ?_, Or.inl ?_⟩
  · rw [Finset.card_erase_of_mem hv]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨v, hv⟩) (by decide)
  · exact legalInverseHennebergOne_of_degree_two hG hv hDegree

/-- The elementary counting step in Nixon--Owen Lemma 3.2: either inverse
Henneberg 1 applies, or the graph has a vertex of degree three. -/
theorem hasNixonOwenReduction_or_exists_degree_three
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    HasNixonOwenReduction F X ∨
      ∃ v ∈ X, edgeSetDegree F v = 3 := by
  obtain ⟨v, hv, hDegree | hDegree⟩ :=
    exists_edgeSetDegree_eq_two_or_three hG hXcard
  · exact Or.inl (hasNixonOwenReduction_of_degree_two hG hv hDegree)
  · exact Or.inr ⟨v, hv, hDegree⟩

/--
Closed low-degree boundary of Nixon--Owen Lemmas 3.1--3.2: every supported
`(2,2)`-tight graph with at least two vertices either already has one of
the four legal reductions (in fact Henneberg 1 or 2 at this stage), or a
degree-three vertex is certified inside a named `K₄`.
-/
theorem hasNixonOwenReduction_or_degree_three_in_K4
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    HasNixonOwenReduction F X ∨
      ∃ v ∈ X, ∃ a b c : V, NamedK4Witness F v a b c := by
  obtain ⟨v, hv, hDegree | hDegree⟩ :=
    exists_edgeSetDegree_eq_two_or_three hG hXcard
  · exact Or.inl (hasNixonOwenReduction_of_degree_two hG hv hDegree)
  · rcases degree_three_k4_or_legalInverseHennebergTwo hG hv hDegree with
      hK4 | ⟨F', hLegal⟩
    · exact Or.inr ⟨v, hv, hK4⟩
    · refine Or.inl ⟨F', X.erase v, hLegal.1.card_lt, ?_⟩
      exact Or.inr (Or.inl hLegal)

end RB31E2E


end
end BundleSource0008

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0008/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0008.json"

section BundleSource0009
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlag.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlag.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Provenance-carrying collinearity flags

This file introduces the finite combinatorial state used by the
provenance-flag induction.  The vertex type `V` is exactly the type of live
vertices and the type `Flag` is exactly the type of active flags.  Thus no
ambient labels, inactive flags, or support predicates occur in the state.

Every flag records three live terminals, one missing terminal edge, and one
private ghost vertex.  The completion restores the missing edge and joins
the ghost to the three terminals.  Its vertex type is literally
`V ⊕ Flag`.

No semismallness or height conclusion is stored in the structure.  The
combinatorial hypothesis used later is the transparent proposition that the
actual completed edge set is `(2,2)`-sparse.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-! ## Transporting live edges to the completed vertex type -/

/-- A live simple edge transported along the left injection into
`V ⊕ Flag`. -/
def liftLiveEdge (e : SimpleEdge V) : SimpleEdge (V ⊕ Flag) :=
  ⟨e.1.map Sum.inl, by
    rw [Sym2.isDiag_map Sum.inl_injective]
    exact e.2⟩

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
@[simp]
theorem liftLiveEdge_val (e : SimpleEdge V) :
    (liftLiveEdge (Flag := Flag) e).1 = e.1.map Sum.inl := rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
theorem liftLiveEdge_injective :
    Function.Injective (liftLiveEdge (V := V) (Flag := Flag)) := by
  intro e f hef
  apply Subtype.ext
  exact Sym2.map.injective Sum.inl_injective (Subtype.mk.inj hef)

/-- The embedding version used by `Finset.map`. -/
def liftLiveEdgeEmbedding : SimpleEdge V ↪ SimpleEdge (V ⊕ Flag) where
  toFun := liftLiveEdge
  inj' := liftLiveEdge_injective

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
@[simp]
theorem mem_map_liftLiveEdgeEmbedding
    {F : SimpleEdgeSet V} {e : SimpleEdge V} :
    liftLiveEdge (Flag := Flag) e ∈
        F.map (liftLiveEdgeEmbedding (V := V) (Flag := Flag)) ↔
      e ∈ F := by
  constructor
  · intro he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_map.mp he
    have : f = e := liftLiveEdge_injective hfe
    simpa [this] using hf
  · intro he
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩

/-- The private ghost-to-terminal edge belonging to one active flag. -/
def ghostEdge (t : Flag) (v : V) : SimpleEdge (V ⊕ Flag) :=
  simpleEdge (Sum.inr t) (Sum.inl v) (by simp)

omit [Fintype V] [Fintype Flag] in
@[simp]
theorem vertices_ghostEdge (t : Flag) (v : V) :
    (ghostEdge t v).vertices = {Sum.inr t, Sum.inl v} := by
  simp [ghostEdge]

/-! ## Flag states and their literal completion -/

/--
Finite provenance-flag data on a live simple graph.

`V` contains exactly the live vertices and `Flag` contains exactly the
active flags.  Consequently every edge and terminal label is active by its
type.  Each terminal set has three elements; `missing t` is one of its three
pairs and is absent from the live graph; every other terminal pair is live.
-/
structure State (V Flag : Type*)
    [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] where
  edges : SimpleEdgeSet V
  terminals : Flag → Finset V
  missing : Flag → SimpleEdge V
  terminals_card : ∀ t, (terminals t).card = 3
  missing_supported : ∀ t, (missing t).vertices ⊆ terminals t
  missing_not_live : ∀ t, missing t ∉ edges
  other_terminal_edges_live :
    ∀ t, ∀ e : SimpleEdge V,
      e.vertices ⊆ terminals t → e ≠ missing t → e ∈ edges

/-- Live edges, transported to the completed vertex type. -/
def State.liftedLiveEdges (S : State V Flag) : SimpleEdgeSet (V ⊕ Flag) :=
  S.edges.map (liftLiveEdgeEmbedding (V := V) (Flag := Flag))

/-- The restored distinguished terminal edge of every active flag. -/
def State.restoredMissingEdges (S : State V Flag) :
    SimpleEdgeSet (V ⊕ Flag) :=
  Finset.univ.image fun t ↦ liftLiveEdge (Flag := Flag) (S.missing t)

/-- All private ghost stars, one for every inhabitant of `Flag`. -/
def State.ghostStarEdges (S : State V Flag) : SimpleEdgeSet (V ⊕ Flag) :=
  Finset.univ.biUnion fun t ↦
    (S.terminals t).image fun v ↦ ghostEdge t v

/-- The literal completed edge set: restore one terminal edge and attach
one private three-star for every active flag. -/
def State.completionEdges (S : State V Flag) : SimpleEdgeSet (V ⊕ Flag) :=
  S.liftedLiveEdges ∪ S.restoredMissingEdges ∪ S.ghostStarEdges

/-- Sparsity of the actual completed edge set. -/
def State.CompletionSparse (S : State V Flag) : Prop :=
  Sparse22 S.completionEdges

@[simp]
theorem State.mem_liftedLiveEdges (S : State V Flag) (e : SimpleEdge V) :
    liftLiveEdge (Flag := Flag) e ∈ S.liftedLiveEdges ↔ e ∈ S.edges := by
  exact mem_map_liftLiveEdgeEmbedding

theorem State.liftedLiveEdges_subset_completionEdges (S : State V Flag) :
    S.liftedLiveEdges ⊆ S.completionEdges := by
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_union_left _ he)

theorem State.restoredMissingEdges_subset_completionEdges (S : State V Flag) :
    S.restoredMissingEdges ⊆ S.completionEdges := by
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_union_right _ he)

theorem State.ghostStarEdges_subset_completionEdges (S : State V Flag) :
    S.ghostStarEdges ⊆ S.completionEdges := by
  intro e he
  exact Finset.mem_union_right _ he

/-- Every active flag's restored missing edge is present in the completion. -/
theorem State.lifted_missing_mem_completionEdges
    (S : State V Flag) (t : Flag) :
    liftLiveEdge (Flag := Flag) (S.missing t) ∈ S.completionEdges := by
  apply S.restoredMissingEdges_subset_completionEdges
  exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩

/-- Every ghost-terminal incidence is present in the completion. -/
theorem State.ghostEdge_mem_completionEdges
    (S : State V Flag) (t : Flag) {v : V} (hv : v ∈ S.terminals t) :
    ghostEdge t v ∈ S.completionEdges := by
  apply S.ghostStarEdges_subset_completionEdges
  exact Finset.mem_biUnion.mpr
    ⟨t, Finset.mem_univ t, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-- Completion sparsity immediately restricts to the transported live graph. -/
theorem State.completionSparse_mono_live (S : State V Flag)
    (hS : S.CompletionSparse) : Sparse22 S.liftedLiveEdges := by
  exact hS.mono S.liftedLiveEdges_subset_completionEdges

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0009

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0009/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0009.json"

section BundleSource0010
/- Source: Papers/RigidityZheng_Algebra_FiniteCoordinateTrdeg.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/FiniteCoordinateTrdeg.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Transcendence degree of a finitely generated function field

These lemmas turn the literal statement that a field is generated by a
finite labelled coordinate family into a cardinal bound on its
transcendence degree.  They are used by the function-field formulation of
provenance-flag semismallness.
-/

namespace RB31E2E

noncomputable section

namespace FiniteCoordinateTrdeg

open scoped IntermediateField.algebraAdjoinAdjoin

universe u v w

variable {k : Type u} {K : Type v} {ι : Type w}
  [Field k] [Field K] [Algebra k K]

/-- A field generated by the range of `x` has transcendence degree at most
the cardinality of the source labels. -/
theorem trdeg_le_cardinalMk_of_adjoin_range_eq_top
    (x : ι → K)
    (hgen : IntermediateField.adjoin k (Set.range x) = ⊤) :
    Cardinal.lift.{w} (Algebra.trdeg k K) ≤
      Cardinal.lift.{v} (Cardinal.mk ι) := by
  let L := IntermediateField.adjoin k (Set.range x)
  have hL : Algebra.IsAlgebraic L K := ⟨fun y ↦ by
    have hy : y ∈ L := by
      change y ∈ IntermediateField.adjoin k (Set.range x)
      rw [hgen]
      exact trivial
    have hmap : algebraMap L K (⟨y, hy⟩ : L) = y := rfl
    rw [← hmap]
    exact isAlgebraic_algebraMap _⟩
  have hA : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) K :=
    (IntermediateField.isAlgebraic_adjoin_iff_top (s := Set.range x)).mp hL
  letI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) K := hA
  have hraw := Algebra.IsAlgebraic.trdeg_le_cardinalMk
    k (Set.range x)
  exact (Cardinal.lift_monotone hraw).trans Cardinal.mk_range_le_lift

/-- Finite-type version of the preceding bound. -/
theorem trdeg_le_card_of_adjoin_range_eq_top
    [Fintype ι] (x : ι → K)
    (hgen : IntermediateField.adjoin k (Set.range x) = ⊤) :
    Algebra.trdeg k K ≤ (Fintype.card ι : Cardinal) := by
  simpa using trdeg_le_cardinalMk_of_adjoin_range_eq_top x hgen

/-- If a finite coordinate family generates the whole field and its number
of labels is no larger than the transcendence degree, then the coordinates
are algebraically independent.  This coefficient comparison is used in the
exceptional local steps of provenance-flag induction. -/
theorem algebraicIndependent_of_card_le_trdeg_of_adjoin_range_eq_top
    [Fintype ι] (x : ι → K)
    (hgen : IntermediateField.adjoin k (Set.range x) = ⊤)
    (hle : (Fintype.card ι : Cardinal) ≤ Algebra.trdeg k K) :
    AlgebraicIndependent k x := by
  let L := IntermediateField.adjoin k (Set.range x)
  have hL : Algebra.IsAlgebraic L K := ⟨fun y ↦ by
    have hy : y ∈ L := by
      change y ∈ IntermediateField.adjoin k (Set.range x)
      rw [hgen]
      exact trivial
    have hmap : algebraMap L K (⟨y, hy⟩ : L) = y := rfl
    rw [← hmap]
    exact isAlgebraic_algebraMap _⟩
  have hA : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) K :=
    (IntermediateField.isAlgebraic_adjoin_iff_top (s := Set.range x)).mp hL
  letI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) K := hA
  letI : FaithfulSMul k K :=
    (faithfulSMul_iff_algebraMap_injective k K).2 (RingHom.injective _)
  have hleLift :
      Cardinal.lift.{v} (Cardinal.mk ι) ≤
        Cardinal.lift.{w} (Algebra.trdeg k K) := by
    simpa using Cardinal.lift_monotone.{v, w} hle
  have htb : IsTranscendenceBasis k x :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite.{w, v, u}
      k x hleLift
  exact htb.1

/-- A field generated by `V × Fin 3` coordinate functions has dimension at
most `3 * |V|`. -/
theorem trdeg_le_three_mul_card
    {V : Type*} [Fintype V]
    (x : V × Fin 3 → K)
    (hgen : IntermediateField.adjoin k (Set.range x) = ⊤) :
    Algebra.trdeg k K ≤ 3 * (Fintype.card V : Cardinal) := by
  calc
    Algebra.trdeg k K ≤ (Fintype.card (V × Fin 3) : Cardinal) :=
      trdeg_le_card_of_adjoin_range_eq_top x hgen
    _ = 3 * (Fintype.card V : Cardinal) := by
      simp [mul_comm]

end FiniteCoordinateTrdeg

end

end RB31E2E


end
end BundleSource0010

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0010/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0010.json"

section BundleSource0011
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagBranch.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagBranch.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Function-field branches for provenance flags

An irreducible configuration branch is represented by its actual function
field `K` over a base field `k`, together with the labelled coordinate
functions which generate `K`.  The live coordinate index is literally
`V × Fin 3`: the type `V` contains exactly the live vertices.  Likewise,
every inhabitant of `Flag` is an active provenance flag.

Thus branch dimension is mathlib's native `Algebra.trdeg k K`; it is not an opaque
user-supplied number.  Collinearity and pairwise distinctness are literal
conditions on the coordinate functions.  The structure stores no
codimension, semismallness inequality, or height conclusion.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {k K V Flag : Type*}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The exact finite index type of all live spatial coordinate functions. -/
abbrev LiveCoordinate (V : Type*) := V × Fin 3

/-- The coordinate family of a placement on all (and only) live vertices. -/
def liveCoordinateFamily (a : V → Fin 3 → K) : LiveCoordinate V → K :=
  fun x ↦ a x.1 x.2

/-- The function field is generated by the labelled live coordinates. -/
def GeneratedByLiveCoordinates (a : V → Fin 3 → K) : Prop :=
  IntermediateField.adjoin k (Set.range (liveCoordinateFamily a)) = ⊤

/-- Literal pairwise distinctness on the exact live vertex type. -/
def PairwiseDistinctOnLive (a : V → Fin 3 → K) : Prop :=
  Function.Injective a

/-- All labelled points in `X` lie on one affine line.  The direction is
not required to be nonzero; pairwise distinctness supplies nondegeneracy on
the three-terminal flags where it is needed. -/
def AffinelyCollinearOn (a : V → Fin 3 → K) (X : Finset V) : Prop :=
  ∃ origin direction : Fin 3 → K,
    ∀ v ∈ X, ∃ t : K, a v = origin + t • direction

/-- Every active provenance triple is collinear. -/
def FlagCollinearities (S : State V Flag) (a : V → Fin 3 → K) : Prop :=
  ∀ t : Flag, AffinelyCollinearOn a (S.terminals t)

/--
Honest function-field data for one irreducible flagged configuration branch.
No codimension, stress bound, semismallness statement, or generic-correctness
theorem is a field.
-/
structure FunctionFieldBranch (S : State V Flag) where
  position : V → Fin 3 → K
  generated : GeneratedByLiveCoordinates (k := k) position
  distinct : PairwiseDistinctOnLive position
  collinear : FlagCollinearities S position

/-- The direction-stress dimension at the generic point of the branch. -/
def FunctionFieldBranch.stressDim
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S) : ℕ :=
  DirectionStress.directionStressDim S.edges Y.position

/--
The flag-semismall numerical statement in subtraction-free form:

`stress dimension + branch dimension + 2 * number of active flags`
is at most the full `3 * number of live vertices` ambient dimension.

All dimensions in this definition are read from actual Lean objects:
`ker`, `trdeg`, and the cardinalities of the exact active types.
-/
def FunctionFieldBranch.SemismallBudget
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S) : Prop :=
  (Y.stressDim S : Cardinal) + Algebra.trdeg k K +
      2 * (Fintype.card Flag : Cardinal) ≤
    3 * (Fintype.card V : Cardinal)

/-- The coordinate-generation hypothesis alone gives the ambient branch
dimension bound. -/
theorem FunctionFieldBranch.trdeg_le_ambient
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S) :
    Algebra.trdeg k K ≤ 3 * (Fintype.card V : Cardinal) := by
  exact FiniteCoordinateTrdeg.trdeg_le_three_mul_card
    (liveCoordinateFamily Y.position) Y.generated

/-- Empty-flag specialization of the same transparent budget. -/
theorem FunctionFieldBranch.semismallBudget_of_flag_card_zero_iff
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (hflags : Fintype.card Flag = 0) :
    Y.SemismallBudget S ↔
      (Y.stressDim S : Cardinal) + Algebra.trdeg k K ≤
        3 * (Fintype.card V : Cardinal) := by
  simp [FunctionFieldBranch.SemismallBudget, hflags]

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0011

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0011/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0011.json"

section BundleSource0012
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagPlacement.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagPlacement.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Provenance-flag placements over their intrinsic coordinate fields

For deletion induction it is inconvenient to replace the ambient function
field by a subtype at every step.  Instead, this file measures branch
dimension by the intermediate field generated by the current live
coordinates inside one ambient field.  Direction-stress rank is unchanged
after passing to that intrinsic field; this scalar-extension fact is proved
separately.

The original `FunctionFieldBranch` embeds into this representation, and
its generation equation identifies the intrinsic coordinate field with the
whole ambient field.  No semismallness conclusion is stored as data.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {k K V Flag : Type*}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The field intrinsically generated by the current live coordinates. -/
abbrev liveCoordinateField (a : V → Fin 3 → K) :
    IntermediateField k K :=
  IntermediateField.adjoin k (Set.range (liveCoordinateFamily a))

/-- A flagged placement in an ambient field.  Its intrinsic branch field is
`liveCoordinateField position`; no generation equation or budget is a
field of the structure. -/
structure PlacementBranch (S : State V Flag) where
  position : V → Fin 3 → K
  distinct : PairwiseDistinctOnLive position
  collinear : FlagCollinearities S position

/-- Stress dimension at the actual ambient-field placement. -/
def PlacementBranch.stressDim
    (S : State V Flag) (Y : PlacementBranch (K := K) S) : ℕ :=
  DirectionStress.directionStressDim S.edges Y.position

/-- Subtraction-free flag budget measured over the intrinsic coordinate
field. -/
def PlacementBranch.SemismallBudget
    (S : State V Flag) (Y : PlacementBranch (K := K) S) : Prop :=
  (Y.stressDim S : Cardinal) +
      Algebra.trdeg k (liveCoordinateField (k := k) Y.position) +
      2 * (Fintype.card Flag : Cardinal) ≤
    3 * (Fintype.card V : Cardinal)

/-- Forget only the redundant whole-field generation certificate. -/
def FunctionFieldBranch.toPlacement
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S) :
    PlacementBranch (K := K) S where
  position := Y.position
  distinct := Y.distinct
  collinear := Y.collinear

@[simp]
theorem FunctionFieldBranch.toPlacement_position
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S) :
    (Y.toPlacement S).position = Y.position := rfl

/-- On a coordinate-generated function-field branch the intrinsic and
original flag budgets are literally equivalent. -/
theorem FunctionFieldBranch.toPlacement_semismallBudget_iff
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S) :
    PlacementBranch.SemismallBudget (k := k) S (Y.toPlacement S) ↔
      Y.SemismallBudget S := by
  rw [PlacementBranch.SemismallBudget,
    FunctionFieldBranch.SemismallBudget]
  change
    (Y.stressDim S : Cardinal) +
          Algebra.trdeg k
            (IntermediateField.adjoin k
              (Set.range (liveCoordinateFamily Y.position))) +
          2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal) ↔ _
  rw [Y.generated]
  rw [(IntermediateField.topEquiv :
    (⊤ : IntermediateField k K) ≃ₐ[k] K).trdeg_eq]

/-- The intrinsic coordinate-field dimension is always bounded by the
three coordinates per live vertex. -/
theorem PlacementBranch.trdeg_le_ambient
    (S : State V Flag) (Y : PlacementBranch (K := K) S) :
    Algebra.trdeg k (liveCoordinateField (k := k) Y.position) ≤
      3 * (Fintype.card V : Cardinal) := by
  let L := liveCoordinateField (k := k) Y.position
  let x : V × Fin 3 → L := fun c ↦
    ⟨Y.position c.1 c.2,
      IntermediateField.subset_adjoin k
        (Set.range (liveCoordinateFamily Y.position)) ⟨c, rfl⟩⟩
  have hxgen : IntermediateField.adjoin k (Set.range x) = ⊤ := by
    apply top_unique
    intro y _hy
    exact IntermediateField.adjoin_induction k
      (motive := fun z hz ↦
        (⟨z, hz⟩ : L) ∈ IntermediateField.adjoin k (Set.range x))
      (fun z hz ↦ by
        obtain ⟨c, rfl⟩ := hz
        exact IntermediateField.subset_adjoin k (Set.range x) ⟨c, rfl⟩)
      (fun z ↦ (IntermediateField.adjoin k (Set.range x)).algebraMap_mem z)
      (fun _ _ _ _ hx hy ↦
        (IntermediateField.adjoin k (Set.range x)).add_mem hx hy)
      (fun _ _ hx ↦
        (IntermediateField.adjoin k (Set.range x)).inv_mem hx)
      (fun _ _ _ _ hx hy ↦
        (IntermediateField.adjoin k (Set.range x)).mul_mem hx hy)
      y.property
  exact FiniteCoordinateTrdeg.trdeg_le_three_mul_card
    (k := k)
    (K := L) x hxgen

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0012

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0012/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0012.json"

section BundleSource0013
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagArithmetic.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagArithmetic.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Arithmetic ledger for provenance flags

The graph-theoretic flag proof eventually reduces its two counting steps to
the elementary natural-number inequalities recorded here.  Keeping these
lemmas separate prevents later formalization from hiding a truncated
subtraction or an off-by-one error inside graph notation.
-/

namespace RB31E2E

namespace ProvenanceFlag

/-- A sparse union of `j` completed flag `K₄`s using `q` live terminals
must use at least `2*j+1` terminals.  The premise is written without
truncated subtraction. -/
theorem terminal_count_ge_two_mul_add_one
    {j q : ℕ} (_hj : 1 ≤ j) (hsparse : 6 * j + 2 ≤ 2 * (q + j)) :
    2 * j + 1 ≤ q := by
  omega

/-- The numerical contradiction underlying the low-degree selection lemma.

`o,p,s` count live vertices contained in zero, one, or at least two flags;
`h` is the total flag incidence contributed by the last class.  If every
zero-flag vertex had degree at least four and every private terminal had
degree at least three, the sparse completion edge budget would contradict
the incidence ledger. -/
theorem not_all_flag_degrees_large
    {n m k o p s h : ℕ}
    (hvertices : n = o + p + s)
    (hedges : m + 2 * k + 2 ≤ 2 * n)
    (hdegree : 4 * o + 3 * p + h ≤ 2 * m)
    (hincidence : p + h = 3 * k)
    (hmultiple : 2 * s ≤ h) : False := by
  omega

/-- Contrapositive packaging of the same ledger: under the sparse and flag
incidence budgets, the asserted global degree lower bound cannot hold. -/
theorem flag_selection_arithmetic
    {n m k o p s h : ℕ}
    (hvertices : n = o + p + s)
    (hedges : m + 2 * k + 2 ≤ 2 * n)
    (hincidence : p + h = 3 * k)
    (hmultiple : 2 * s ≤ h) :
    ¬ (4 * o + 3 * p + h ≤ 2 * m) := by
  intro hdegree
  exact not_all_flag_degrees_large hvertices hedges hdegree hincidence hmultiple

end ProvenanceFlag

end RB31E2E


end
end BundleSource0013

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0013/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0013.json"

section BundleSource0014
/- Source: Papers/RigidityZheng_Combinatorics_Sparse22_TriangleSequence.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/Sparse22/TriangleSequence.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# The `K₄` boundary of the Nixon--Owen triangle-sequence argument

The low-degree part of the Nixon--Owen reduction theorem ends with a
degree-three vertex contained in a named `K₄`.  This file isolates the
next, genuinely different, combinatorial layer.  In particular it proves
that a named `K₄` is the base graph as soon as the active graph has at most
four vertices, with no appeal to an informal graph identification.

The later declarations record the exact local overlap obstructions which
feed the triangle-sequence argument.  They deliberately retain named
vertices and edge provenance: no assertion that the full construction
theorem has already been proved is hidden in an interface hypothesis.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- The four vertices carried by a named `K₄` witness. -/
def namedK4Vertices (v a b c : V) : Finset V := {v, a, b, c}

@[simp]
theorem mem_namedK4Vertices {v a b c x : V} :
    x ∈ namedK4Vertices v a b c ↔ x = v ∨ x = a ∨ x = b ∨ x = c := by
  simp [namedK4Vertices]

theorem card_namedK4Vertices
    {F : SimpleEdgeSet V} {v a b c : V}
    (hK : NamedK4Witness F v a b c) :
    (namedK4Vertices v a b c).card = 4 := by
  simp [namedK4Vertices, hK.hva, hK.hvb, hK.hvc,
    hK.hab, hK.hac, hK.hbc]

theorem namedK4Vertices_subset
    {F : SimpleEdgeSet V} {X : Finset V} {v a b c : V}
    (hG : SimpleTight22On F X) (hK : NamedK4Witness F v a b c) :
    namedK4Vertices v a b c ⊆ X := by
  intro x hx
  rw [mem_namedK4Vertices] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hG.supported hK.va_mem (by simp)
  · exact hG.supported hK.va_mem (by simp)
  · exact hG.supported hK.vb_mem (by simp)
  · exact hG.supported hK.vc_mem (by simp)

theorem namedK4_isCliqueEdgeSet
    {F : SimpleEdgeSet V} {v a b c : V}
    (hK : NamedK4Witness F v a b c) :
    IsCliqueEdgeSet F (namedK4Vertices v a b c) := by
  intro x hx y hy hxy
  rw [mem_namedK4Vertices] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl
  all_goals try exact (hxy rfl).elim
  · exact hK.va_mem
  · exact hK.vb_mem
  · exact hK.vc_mem
  · rw [simpleEdge_comm]
    exact hK.va_mem
  · exact hK.ab_mem
  · exact hK.ac_mem
  · rw [simpleEdge_comm]
    exact hK.vb_mem
  · rw [simpleEdge_comm]
    exact hK.ab_mem
  · exact hK.bc_mem
  · rw [simpleEdge_comm]
    exact hK.vc_mem
  · rw [simpleEdge_comm]
    exact hK.ac_mem
  · rw [simpleEdge_comm]
    exact hK.bc_mem

/-- A named `K₄` occupying an active graph of cardinality at most four is
definitionally promoted to the exact `K₄` base object. -/
theorem isK4Base_of_namedK4_of_card_le_four
    {F : SimpleEdgeSet V} {X : Finset V} {v a b c : V}
    (hG : SimpleTight22On F X) (hK : NamedK4Witness F v a b c)
    (hXcard : X.card ≤ 4) :
    IsK4Base F X := by
  have hKX := namedK4Vertices_subset hG hK
  have hKcard := card_namedK4Vertices hK
  have hXeq : X = namedK4Vertices v a b c := by
    apply Finset.Subset.antisymm
    · exact Finset.eq_of_subset_of_card_le hKX (by omega) |>.symm.subset
    · exact hKX
  subst X
  exact ⟨hKcard, hG, namedK4_isCliqueEdgeSet hK⟩

/-- The existing degree-three reduction theorem, sharpened at the four-
vertex boundary: either a genuine reduction exists, the graph is exactly
`K₄`, or the certified named `K₄` lies in a graph with at least five active
vertices. -/
theorem hasNixonOwenReduction_or_isK4Base_or_large_namedK4
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    HasNixonOwenReduction F X ∨ IsK4Base F X ∨
      ∃ v ∈ X, ∃ a b c : V,
        NamedK4Witness F v a b c ∧ 5 ≤ X.card := by
  rcases hasNixonOwenReduction_or_degree_three_in_K4 hG hXcard with
      hReduce | ⟨v, hv, a, b, c, hK⟩
  · exact Or.inl hReduce
  · by_cases hFour : X.card ≤ 4
    · exact Or.inr (Or.inl (isK4Base_of_namedK4_of_card_le_four hG hK hFour))
    · exact Or.inr (Or.inr ⟨v, hv, a, b, c, hK, by omega⟩)

end RB31E2E


end
end BundleSource0014

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0014/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0014.json"

section BundleSource0015
/- Source: Papers/RigidityZheng_Combinatorics_Sparse22_GraphExtension.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/Sparse22/GraphExtension.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Proper tight modules and graph-extension reduction

This file develops the shorter replacement for the long triangle-sequence
branch in the simple `(2,2)`-tight construction theorem.  Starting from a
proper tight seed (in the intended application, the named `K₄` around a
degree-three vertex), we choose a maximum-cardinality proper tight
superset.  Tightness alone then forces every outside vertex to send at most
one edge into the module, unless that vertex already has degree two and
supplies an inverse Henneberg-one reduction.

The formulation keeps the exact source edge sets.  In particular,
`newEdgesAt` is not a numerical proxy: its elements are precisely the
source edges acquired when one outside vertex is adjoined to the module.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- The six provenance edges of a named `K₄` make its four-vertex set
`(2,2)`-tight.  This is the seed used by the graph-extension branch. -/
theorem tight22_namedK4Vertices
    {F : SimpleEdgeSet V} {v a b c : V}
    (hSparse : Sparse22 F) (hK : NamedK4Witness F v a b c) :
    Tight22 F (namedK4Vertices v a b c) := by
  let K : Finset V := namedK4Vertices v a b c
  let E : SimpleEdgeSet V :=
    { simpleEdge v a hK.hva,
      simpleEdge v b hK.hvb,
      simpleEdge v c hK.hvc,
      simpleEdge a b hK.hab,
      simpleEdge a c hK.hac,
      simpleEdge b c hK.hbc }
  have he₁ : simpleEdge v a hK.hva ∉
      ({ simpleEdge v b hK.hvb, simpleEdge v c hK.hvc,
        simpleEdge a b hK.hab, simpleEdge a c hK.hac,
        simpleEdge b c hK.hbc } : SimpleEdgeSet V) := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hva, hK.hvb, hK.hvc,
      hK.hab, hK.hac]
  have he₂ : simpleEdge v b hK.hvb ∉
      ({ simpleEdge v c hK.hvc, simpleEdge a b hK.hab,
        simpleEdge a c hK.hac, simpleEdge b c hK.hbc } : SimpleEdgeSet V) := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hva, hK.hvb, hK.hvc, hK.hbc]
  have he₃ : simpleEdge v c hK.hvc ∉
      ({ simpleEdge a b hK.hab, simpleEdge a c hK.hac,
        simpleEdge b c hK.hbc } : SimpleEdgeSet V) := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hva, hK.hvb, hK.hvc]
  have he₄ : simpleEdge a b hK.hab ∉
      ({simpleEdge a c hK.hac, simpleEdge b c hK.hbc} : SimpleEdgeSet V) := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hab, hK.hac, hK.hbc]
  have he₅ : simpleEdge a c hK.hac ≠ simpleEdge b c hK.hbc := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hab, hK.hac]
  have hEcard : E.card = 6 := by
    dsimp [E]
    rw [Finset.card_insert_of_notMem he₁,
      Finset.card_insert_of_notMem he₂,
      Finset.card_insert_of_notMem he₃,
      Finset.card_insert_of_notMem he₄]
    simp [he₅]
  have pair_subset_K {x y : V} (hx : x ∈ K) (hy : y ∈ K) :
      ({x, y} : Finset V) ⊆ K := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hx
    · exact hy
  have hEsub : E ⊆ edgesInside F K := by
    intro e he
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · apply mem_edgesInside.mpr
      refine ⟨hK.va_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.vb_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.vc_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.ab_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.ac_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.bc_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
  have hLower : 6 ≤ (edgesInside F K).card := by
    rw [← hEcard]
    exact Finset.card_le_card hEsub
  have hKcard : K.card = 4 := card_namedK4Vertices hK
  have hUpper := hSparse K ⟨v, by simp [K, namedK4Vertices]⟩
  rw [hKcard] at hUpper
  have hEq : (edgesInside F K).card = 2 * (K.card - 1) := by
    rw [hKcard]
    omega
  exact ⟨⟨v, by simp [namedK4Vertices]⟩, hEq⟩

/-- Source edges acquired by adjoining one vertex `u` to a vertex set `K`. -/
def newEdgesAt (F : SimpleEdgeSet V) (K : Finset V) (u : V) :
    SimpleEdgeSet V :=
  edgesInside F (insert u K) \ edgesInside F K

@[simp]
theorem mem_newEdgesAt {F : SimpleEdgeSet V} {K : Finset V} {u : V}
    {e : SimpleEdge V} :
    e ∈ newEdgesAt F K u ↔
      e ∈ F ∧ e.vertices ⊆ insert u K ∧ ¬ e.vertices ⊆ K := by
  simp only [newEdgesAt, Finset.mem_sdiff, mem_edgesInside]
  aesop

theorem edgesInside_union_newEdgesAt
    (F : SimpleEdgeSet V) (K : Finset V) (u : V) :
    edgesInside F K ∪ newEdgesAt F K u = edgesInside F (insert u K) := by
  unfold newEdgesAt
  rw [Finset.union_sdiff_of_subset]
  exact edgesInside_mono_vertices F (Finset.subset_insert u K)

theorem edgesInside_disjoint_newEdgesAt
    (F : SimpleEdgeSet V) (K : Finset V) (u : V) :
    Disjoint (edgesInside F K) (newEdgesAt F K u) := by
  rw [Finset.disjoint_left]
  intro e heK heNew
  exact (Finset.mem_sdiff.mp heNew).2 heK

theorem card_edgesInside_add_card_newEdgesAt
    (F : SimpleEdgeSet V) (K : Finset V) (u : V) :
    (edgesInside F K).card + (newEdgesAt F K u).card =
      (edgesInside F (insert u K)).card := by
  rw [← Finset.card_union_of_disjoint
    (edgesInside_disjoint_newEdgesAt F K u)]
  exact congrArg Finset.card (edgesInside_union_newEdgesAt F K u)

/-- At most two source edges can be acquired by adding one vertex to a
tight set in a `(2,2)`-sparse graph. -/
theorem card_newEdgesAt_le_two
    {F : SimpleEdgeSet V} {K : Finset V} {u : V}
    (hSparse : Sparse22 F) (hK : Tight22 F K) (huK : u ∉ K) :
    (newEdgesAt F K u).card ≤ 2 := by
  have hSplit := card_edgesInside_add_card_newEdgesAt F K u
  have hUpper := hSparse (insert u K) ⟨u, by simp⟩
  have hInsertCard : (insert u K).card = K.card + 1 := by
    rw [Finset.card_insert_of_notMem huK]
  rw [hK.2] at hSplit
  rw [hInsertCard] at hUpper
  have hKpos : 0 < K.card := Finset.card_pos.mpr hK.1
  omega

/-- Acquiring exactly two edges makes the one-vertex enlargement tight. -/
theorem tight22_insert_of_card_newEdgesAt_eq_two
    {F : SimpleEdgeSet V} {K : Finset V} {u : V}
    (hK : Tight22 F K) (huK : u ∉ K)
    (hTwo : (newEdgesAt F K u).card = 2) :
    Tight22 F (insert u K) := by
  refine ⟨⟨u, by simp⟩, ?_⟩
  have hSplit := card_edgesInside_add_card_newEdgesAt F K u
  have hInsertCard : (insert u K).card = K.card + 1 := by
    rw [Finset.card_insert_of_notMem huK]
  rw [hK.2, hTwo] at hSplit
  rw [hInsertCard]
  have hKpos : 0 < K.card := Finset.card_pos.mpr hK.1
  omega

/-- `K` is maximum by cardinality among proper tight supersets of the seed
`K₀` inside the active vertex set `X`. -/
structure IsMaximumProperTightSuperset
    (F : SimpleEdgeSet V) (X K₀ K : Finset V) : Prop where
  seed_subset : K₀ ⊆ K
  subset_active : K ⊆ X
  proper : K ≠ X
  tight : Tight22 F K
  card_max : ∀ {L : Finset V},
    K₀ ⊆ L → L ⊆ X → L ≠ X → Tight22 F L → L.card ≤ K.card

/-- Candidate proper tight supersets, retained as an explicit finite search
space so that maximality needs only ordinary finite classical choice. -/
noncomputable def properTightSupersets
    (F : SimpleEdgeSet V) (X K₀ : Finset V) : Finset (Finset V) := by
  classical
  exact X.powerset.filter fun K => K₀ ⊆ K ∧ K ≠ X ∧ Tight22 F K

@[simp]
theorem mem_properTightSupersets
    {F : SimpleEdgeSet V} {X K₀ K : Finset V} :
    K ∈ properTightSupersets F X K₀ ↔
      K ⊆ X ∧ K₀ ⊆ K ∧ K ≠ X ∧ Tight22 F K := by
  classical
  simp [properTightSupersets, and_left_comm]

theorem exists_isMaximumProperTightSuperset
    {F : SimpleEdgeSet V} {X K₀ : Finset V}
    (hK₀X : K₀ ⊆ X) (hK₀proper : K₀ ≠ X)
    (hK₀tight : Tight22 F K₀) :
    ∃ K : Finset V, IsMaximumProperTightSuperset F X K₀ K := by
  classical
  have hne : (properTightSupersets F X K₀).Nonempty := by
    exact ⟨K₀, mem_properTightSupersets.mpr
      ⟨hK₀X, Finset.Subset.rfl, hK₀proper, hK₀tight⟩⟩
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image (properTightSupersets F X K₀) Finset.card hne
  have hK := mem_properTightSupersets.mp hKmem
  refine ⟨K, hK.2.1, hK.1, hK.2.2.1, hK.2.2.2, ?_⟩
  intro L hseed hLX hproper htight
  exact hKmax L (mem_properTightSupersets.mpr
    ⟨hLX, hseed, hproper, htight⟩)

/-- If `K` is maximum proper tight and `K ∪ {u}` is still proper, then
`u` contributes at most one edge into `K`. -/
theorem card_newEdgesAt_le_one_of_insert_ne_active
    {F : SimpleEdgeSet V} {X K₀ K : Finset V} {u : V}
    (hSparse : Sparse22 F)
    (hK : IsMaximumProperTightSuperset F X K₀ K)
    (huX : u ∈ X) (huK : u ∉ K) (hInsertProper : insert u K ≠ X) :
    (newEdgesAt F K u).card ≤ 1 := by
  have hAtMostTwo := card_newEdgesAt_le_two hSparse hK.tight huK
  by_contra hNot
  have hTwo : (newEdgesAt F K u).card = 2 := by omega
  have hInsertTight := tight22_insert_of_card_newEdgesAt_eq_two
    hK.tight huK hTwo
  have hSeedInsert : K₀ ⊆ insert u K :=
    hK.seed_subset.trans (Finset.subset_insert u K)
  have hInsertX : insert u K ⊆ X :=
    Finset.insert_subset huX hK.subset_active
  have hCardMax := hK.card_max hSeedInsert hInsertX hInsertProper hInsertTight
  rw [Finset.card_insert_of_notMem huK] at hCardMax
  omega

/-- When the active graph is exactly `K ∪ {u}`, every edge newly
acquired by adjoining `u` is precisely an edge incident with `u`. -/
theorem incidentEdges_eq_newEdgesAt_of_active_eq_insert
    {F : SimpleEdgeSet V} {X K : Finset V} {u : V}
    (hSupported : SupportedOn F X) (huK : u ∉ K)
    (hX : X = insert u K) :
    incidentEdges F u = newEdgesAt F K u := by
  ext e
  simp only [mem_incidentEdges, mem_newEdgesAt]
  constructor
  · rintro ⟨heF, hue⟩
    refine ⟨heF, ?_, ?_⟩
    · rw [← hX]
      exact hSupported heF
    · intro heK
      exact huK (heK hue)
  · rintro ⟨heF, heInsert, heNotK⟩
    refine ⟨heF, ?_⟩
    by_contra huNot
    apply heNotK
    intro x hx
    have hxInsert := heInsert hx
    rw [Finset.mem_insert] at hxInsert
    rcases hxInsert with rfl | hxK
    · exact (huNot hx).elim
    · exact hxK

/-- A maximum proper tight module has simple external incidence unless an
outside vertex is already an inverse-Henneberg-one witness. -/
theorem exists_degree_two_or_all_outside_newEdgesAt_le_one
    {F : SimpleEdgeSet V} {X K₀ K : Finset V}
    (hG : SimpleTight22On F X)
    (hK : IsMaximumProperTightSuperset F X K₀ K) :
    (∃ u ∈ X, edgeSetDegree F u = 2) ∨
      ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1 := by
  classical
  by_cases hDegree : ∃ u ∈ X, edgeSetDegree F u = 2
  · exact Or.inl hDegree
  · refine Or.inr ?_
    intro u huX huK
    by_cases hInsert : insert u K = X
    · have hSplit := card_edgesInside_add_card_newEdgesAt F K u
      have hGlobal : F.card = 2 * (X.card - 1) := by
        rw [← edgesInside_eq_self_of_supported hG.supported]
        exact hG.tight.2
      have hInsideInsert : edgesInside F (insert u K) = F := by
        rw [hInsert]
        exact edgesInside_eq_self_of_supported hG.supported
      have hInsertCard : X.card = K.card + 1 := by
        rw [← hInsert, Finset.card_insert_of_notMem huK]
      rw [hK.tight.2, hInsideInsert, hGlobal, hInsertCard] at hSplit
      have hKpos : 0 < K.card := Finset.card_pos.mpr hK.tight.1
      have hTwo : (newEdgesAt F K u).card = 2 := by omega
      have hIncident := incidentEdges_eq_newEdgesAt_of_active_eq_insert
        hG.supported huK hInsert.symm
      exfalso
      apply hDegree
      refine ⟨u, huX, ?_⟩
      unfold edgeSetDegree
      rw [hIncident, hTwo]
    · exact card_newEdgesAt_le_one_of_insert_ne_active
        hG.sparse hK huX huK hInsert

/-- A proper tight module whose external incidence is simple after the
module is collapsed: every outside vertex is incident with at most one
source edge entering the module. -/
structure IsSimpleGraphExtensionModule
    (F : SimpleEdgeSet V) (X K : Finset V) : Prop where
  subset_active : K ⊆ X
  proper : K ≠ X
  tight : Tight22 F K
  outside_simple : ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1

theorem IsMaximumProperTightSuperset.toSimpleGraphExtensionModule
    {F : SimpleEdgeSet V} {X K₀ K : Finset V}
    (hK : IsMaximumProperTightSuperset F X K₀ K)
    (hOutside : ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1) :
    IsSimpleGraphExtensionModule F X K :=
  ⟨hK.subset_active, hK.proper, hK.tight, hOutside⟩

/-- The complete structural replacement for the triangle-sequence branch.
Every supported simple `(2,2)`-tight graph is either already reducible by
Henneberg 1/2, is the base `K₄`, or contains a proper tight module whose
contraction has no parallel-edge provenance collision.

The returned module contains the named `K₄` seed, so it has at least four
vertices and contraction strictly decreases the vertex count. -/
theorem hasNixonOwenReduction_or_isK4Base_or_graphExtensionModule
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    HasNixonOwenReduction F X ∨ IsK4Base F X ∨
      ∃ K : Finset V,
        IsSimpleGraphExtensionModule F X K ∧ 4 ≤ K.card := by
  rcases hasNixonOwenReduction_or_isK4Base_or_large_namedK4 hG hXcard with
      hReduce | hBase | ⟨v, _hvX, a, b, c, hNamed, hLarge⟩
  · exact Or.inl hReduce
  · exact Or.inr (Or.inl hBase)
  · let K₀ : Finset V := namedK4Vertices v a b c
    have hK₀X : K₀ ⊆ X := namedK4Vertices_subset hG hNamed
    have hK₀card : K₀.card = 4 := card_namedK4Vertices hNamed
    have hK₀proper : K₀ ≠ X := by
      intro hEq
      rw [← hEq, hK₀card] at hLarge
      omega
    have hK₀tight : Tight22 F K₀ :=
      tight22_namedK4Vertices hG.sparse hNamed
    obtain ⟨K, hKmax⟩ := exists_isMaximumProperTightSuperset
      hK₀X hK₀proper hK₀tight
    rcases exists_degree_two_or_all_outside_newEdgesAt_le_one hG hKmax with
        ⟨u, huX, huDegree⟩ | hOutside
    · exact Or.inl (hasNixonOwenReduction_of_degree_two hG huX huDegree)
    · refine Or.inr (Or.inr ⟨K,
        hKmax.toSimpleGraphExtensionModule hOutside, ?_⟩)
      rw [← hK₀card]
      exact Finset.card_le_card hKmax.seed_subset

/-! ## Provenance partition for a tight-module contraction -/

/-- All source edges from vertices in `U` into the module `K`. -/
def crossEdgesTo (F : SimpleEdgeSet V) (K U : Finset V) :
    SimpleEdgeSet V :=
  U.biUnion fun u => newEdgesAt F K u

@[simp]
theorem mem_crossEdgesTo {F : SimpleEdgeSet V} {K U : Finset V}
    {e : SimpleEdge V} :
    e ∈ crossEdgesTo F K U ↔ ∃ u ∈ U, e ∈ newEdgesAt F K u := by
  simp [crossEdgesTo]

theorem disjoint_newEdgesAt_of_ne
    {F : SimpleEdgeSet V} {K : Finset V} {u w : V}
    (huw : u ≠ w) :
    Disjoint (newEdgesAt F K u) (newEdgesAt F K w) := by
  rw [Finset.disjoint_left]
  intro e heu hew
  have heu' := mem_newEdgesAt.mp heu
  have hew' := mem_newEdgesAt.mp hew
  have hExists : ∃ x ∈ e.vertices, x ∉ K := by
    by_contra hNot
    apply heu'.2.2
    intro x hx
    by_contra hxK
    exact hNot ⟨x, hx, hxK⟩
  obtain ⟨x, hxe, hxK⟩ := hExists
  have hxu : x = u := by
    rcases Finset.mem_insert.mp (heu'.2.1 hxe) with hxu | hxK'
    · exact hxu
    · exact (hxK hxK').elim
  have hxw : x = w := by
    rcases Finset.mem_insert.mp (hew'.2.1 hxe) with hxw | hxK'
    · exact hxw
    · exact (hxK hxK').elim
  exact huw (hxu.symm.trans hxw)

theorem pairwiseDisjoint_newEdgesAt
    {F : SimpleEdgeSet V} {K U : Finset V} (_hUK : Disjoint U K) :
    (U : Set V).PairwiseDisjoint fun u => newEdgesAt F K u := by
  intro u huU w hwU huw
  exact disjoint_newEdgesAt_of_ne huw

theorem card_crossEdgesTo
    {F : SimpleEdgeSet V} {K U : Finset V} (hUK : Disjoint U K) :
    (crossEdgesTo F K U).card = ∑ u ∈ U, (newEdgesAt F K u).card := by
  unfold crossEdgesTo
  exact Finset.card_biUnion (pairwiseDisjoint_newEdgesAt hUK)

theorem internalEdges_disjoint_crossEdgesTo
    (F : SimpleEdgeSet V) (K U : Finset V) :
    Disjoint (edgesInside F K) (crossEdgesTo F K U) := by
  rw [Finset.disjoint_left]
  intro e heK heCross
  obtain ⟨u, _huU, heu⟩ := mem_crossEdgesTo.mp heCross
  exact (mem_newEdgesAt.mp heu).2.2 (mem_edgesInside.mp heK).2

theorem internalEdges_disjoint_exteriorEdges
    (F : SimpleEdgeSet V) {K U : Finset V} (hUK : Disjoint U K) :
    Disjoint (edgesInside F K) (edgesInside F U) := by
  rw [Finset.disjoint_left]
  intro e heK heU
  have hne : e.vertices.Nonempty := Finset.card_pos.mp (by simp)
  obtain ⟨x, hxe⟩ := hne
  exact (Finset.disjoint_left.mp hUK)
    ((mem_edgesInside.mp heU).2 hxe) ((mem_edgesInside.mp heK).2 hxe)

theorem exteriorEdges_disjoint_newEdgesAt
    {F : SimpleEdgeSet V} {K U : Finset V} {u : V}
    (hUK : Disjoint U K) (_huU : u ∈ U) :
    Disjoint (edgesInside F U) (newEdgesAt F K u) := by
  rw [Finset.disjoint_left]
  intro e heU heNew
  have hUsub := (mem_edgesInside.mp heU).2
  have hNew := mem_newEdgesAt.mp heNew
  have hAllU : e.vertices ⊆ ({u} : Finset V) := by
    intro x hx
    have hxU := hUsub hx
    rcases Finset.mem_insert.mp (hNew.2.1 hx) with hxu | hxK
    · simp [hxu]
    · exact (Finset.disjoint_left.mp hUK hxU hxK).elim
  have hCardLe : e.vertices.card ≤ ({u} : Finset V).card :=
    Finset.card_le_card hAllU
  rw [e.card_vertices] at hCardLe
  simp at hCardLe

theorem exteriorEdges_disjoint_crossEdgesTo
    (F : SimpleEdgeSet V) {K U : Finset V} (hUK : Disjoint U K) :
    Disjoint (edgesInside F U) (crossEdgesTo F K U) := by
  rw [Finset.disjoint_left]
  intro e heU heCross
  obtain ⟨u, huU, heNew⟩ := mem_crossEdgesTo.mp heCross
  exact (Finset.disjoint_left.mp
    (exteriorEdges_disjoint_newEdgesAt (F := F) hUK huU)) heU heNew

theorem module_exterior_cross_union_subset
    {F : SimpleEdgeSet V} {K U : Finset V} :
    edgesInside F K ∪ edgesInside F U ∪ crossEdgesTo F K U ⊆
      edgesInside F (K ∪ U) := by
  intro e he
  rw [Finset.mem_union] at he
  rcases he with heInternalOrExterior | heCross
  · rw [Finset.mem_union] at heInternalOrExterior
    rcases heInternalOrExterior with heK | heU
    · exact edgesInside_mono_vertices F Finset.subset_union_left heK
    · exact edgesInside_mono_vertices F Finset.subset_union_right heU
  · obtain ⟨u, huU, heNew⟩ := mem_crossEdgesTo.mp heCross
    have hNew := mem_newEdgesAt.mp heNew
    apply mem_edgesInside.mpr
    refine ⟨hNew.1, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp (hNew.2.1 hx) with rfl | hxK
    · exact Finset.mem_union_right K huU
    · exact Finset.mem_union_left U hxK

/-- Exact lower-bound packet used in the quotient sparsity proof: internal
module edges, exterior edges and all provenance-labelled crossing edges
are pairwise disjoint source edges inside `K ∪ U`. -/
theorem card_module_add_exterior_add_cross_le
    {F : SimpleEdgeSet V} {K U : Finset V} (hUK : Disjoint U K) :
    (edgesInside F K).card + (edgesInside F U).card +
        (crossEdgesTo F K U).card ≤
      (edgesInside F (K ∪ U)).card := by
  have hInternalExterior := internalEdges_disjoint_exteriorEdges F hUK
  have hUnionCross :
      Disjoint (edgesInside F K ∪ edgesInside F U)
        (crossEdgesTo F K U) := by
    rw [Finset.disjoint_left]
    intro e heUnion heCross
    rw [Finset.mem_union] at heUnion
    rcases heUnion with heK | heU
    · exact (Finset.disjoint_left.mp
        (internalEdges_disjoint_crossEdgesTo F K U)) heK heCross
    · exact (Finset.disjoint_left.mp
        (exteriorEdges_disjoint_crossEdgesTo F hUK)) heU heCross
  calc
    (edgesInside F K).card + (edgesInside F U).card +
          (crossEdgesTo F K U).card =
        ((edgesInside F K ∪ edgesInside F U) ∪
          crossEdgesTo F K U).card := by
      rw [Finset.card_union_of_disjoint hUnionCross,
        Finset.card_union_of_disjoint hInternalExterior]
    _ ≤ (edgesInside F (K ∪ U)).card :=
      Finset.card_le_card module_exterior_cross_union_subset

/-! ## Explicit simple quotient edge set -/

/-- Collapsing `K` to `r` sends an outside vertex to the simple edge
joining it to `r`. -/
def collapsedBoundaryEmbedding
    (K U : Finset V) (r : V) (hrK : r ∈ K) (hUK : Disjoint U K) :
    {u // u ∈ U} ↪ SimpleEdge V where
  toFun u := simpleEdge r u.1 (by
    intro hru
    exact (Finset.disjoint_left.mp hUK u.2 (hru ▸ hrK)))
  inj' := by
    intro u w huw
    apply Subtype.ext
    have hEdge := congrArg Subtype.val huw
    change s(r, u.1) = s(r, w.1) at hEdge
    rw [Sym2.eq_iff] at hEdge
    rcases hEdge with hEdge | hEdge
    · exact hEdge.2
    · exfalso
      exact (Finset.disjoint_left.mp hUK u.2 (hEdge.2.symm ▸ hrK))

/-- Quotient boundary edges, one for each outside vertex with nonempty
source provenance into `K`. -/
noncomputable def collapsedBoundaryEdges
    (F : SimpleEdgeSet V) (K U : Finset V) (r : V)
    (hrK : r ∈ K) (hUK : Disjoint U K) : SimpleEdgeSet V := by
  classical
  exact (U.attach.filter fun u => (newEdgesAt F K u.1).Nonempty).map
    (collapsedBoundaryEmbedding K U r hrK hUK)

@[simp]
theorem mem_collapsedBoundaryEdges
    {F : SimpleEdgeSet V} {K U : Finset V} {r : V}
    {hrK : r ∈ K} {hUK : Disjoint U K} {e : SimpleEdge V} :
    e ∈ collapsedBoundaryEdges F K U r hrK hUK ↔
      ∃ u : V, u ∈ U ∧ (newEdgesAt F K u).Nonempty ∧
        ∃ hru : r ≠ u, e = simpleEdge r u hru := by
  classical
  simp only [collapsedBoundaryEdges, Finset.mem_map, Finset.mem_filter,
    Finset.mem_attach, true_and]
  constructor
  · rintro ⟨u, ⟨huNew, rfl⟩⟩
    refine ⟨u.1, u.2, huNew, ?_⟩
    refine ⟨?_, rfl⟩
    intro hru
    exact (Finset.disjoint_left.mp hUK u.2 (hru ▸ hrK))
  · rintro ⟨u, huU, huNew, hru, rfl⟩
    refine ⟨⟨u, huU⟩, ⟨huNew, ?_⟩⟩
    apply Subtype.ext
    simp [collapsedBoundaryEmbedding, simpleEdge]

theorem card_filter_nonempty_eq_sum_card_of_le_one
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : A → Finset B)
    (hOne : ∀ a ∈ S, (T a).card ≤ 1) :
    (S.filter fun a => (T a).Nonempty).card = ∑ a ∈ S, (T a).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hOneS : ∀ x ∈ S, (T x).card ≤ 1 := by
        intro x hx
        exact hOne x (Finset.mem_insert_of_mem hx)
      have ih' := ih hOneS
      have hOneA := hOne a (by simp)
      by_cases hne : (T a).Nonempty
      · have hCardA : (T a).card = 1 := by
          have hpos : 0 < (T a).card := Finset.card_pos.mpr hne
          omega
        have haFilter : a ∉ S.filter fun x => (T x).Nonempty := by
          simp [ha]
        rw [Finset.filter_insert, if_pos hne,
          Finset.card_insert_of_notMem haFilter, Finset.sum_insert ha,
          hCardA, ih']
        omega
      · have hCardA : (T a).card = 0 := by
          exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
        rw [Finset.filter_insert, if_neg hne, Finset.sum_insert ha,
          hCardA, ih']
        omega

theorem card_collapsedBoundaryEdges
    {F : SimpleEdgeSet V} {K U : Finset V} {r : V}
    (hrK : r ∈ K) (hUK : Disjoint U K)
    (hOne : ∀ u ∈ U, (newEdgesAt F K u).card ≤ 1) :
    (collapsedBoundaryEdges F K U r hrK hUK).card =
      (crossEdgesTo F K U).card := by
  classical
  have hAttachCard :
      (U.attach.filter fun u => (newEdgesAt F K u.1).Nonempty).card =
        (U.filter fun u => (newEdgesAt F K u).Nonempty).card := by
    apply Finset.card_bij (fun u _hu => u.1)
    · intro u hu
      have hu' := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨u.2, hu'.2⟩
    · intro u₁ _hu₁ u₂ _hu₂ hval
      exact Subtype.ext hval
    · intro u hu
      have hu' := Finset.mem_filter.mp hu
      refine ⟨⟨u, hu'.1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨by simp, hu'.2⟩
  rw [collapsedBoundaryEdges, Finset.card_map, hAttachCard,
    card_crossEdgesTo hUK]
  exact card_filter_nonempty_eq_sum_card_of_le_one U
    (newEdgesAt F K) hOne

theorem exteriorEdges_disjoint_collapsedBoundaryEdges
    {F : SimpleEdgeSet V} {K U : Finset V} {r : V}
    (hrK : r ∈ K) (hUK : Disjoint U K) :
    Disjoint (edgesInside F U)
      (collapsedBoundaryEdges F K U r hrK hUK) := by
  rw [Finset.disjoint_left]
  intro e heExterior heBoundary
  obtain ⟨u, huU, _huNew, hru, rfl⟩ :=
    mem_collapsedBoundaryEdges.mp heBoundary
  have hrVertices : r ∈ (simpleEdge r u hru).vertices := by
    rw [vertices_simpleEdge]
    simp
  have hrU := (mem_edgesInside.mp heExterior).2 hrVertices
  exact (Finset.disjoint_left.mp hUK hrU hrK)

/-- The explicit simple graph obtained by collapsing `K` to `r`: exterior
source edges are retained, while all source edges entering `K` at one
outside vertex are represented by the single edge to `r`. -/
noncomputable def graphExtensionQuotientEdges
    (F : SimpleEdgeSet V) (X K : Finset V) (r : V) (hrK : r ∈ K) :
    SimpleEdgeSet V := by
  classical
  let U := X \ K
  exact edgesInside F U ∪
    collapsedBoundaryEdges F K U r hrK (Finset.sdiff_disjoint)

/-- Active vertices after collapsing `K` to its retained representative. -/
def graphExtensionQuotientVertices (X K : Finset V) (r : V) : Finset V :=
  insert r (X \ K)

theorem graphExtensionQuotientEdges_supported
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V} (hrK : r ∈ K) :
    SupportedOn (graphExtensionQuotientEdges F X K r hrK)
      (graphExtensionQuotientVertices X K r) := by
  intro e he
  rw [graphExtensionQuotientEdges, Finset.mem_union] at he
  rcases he with heExterior | heBoundary
  · exact (mem_edgesInside.mp heExterior).2.trans
      (Finset.subset_insert r (X \ K))
  · obtain ⟨u, huU, _huNew, hru, rfl⟩ :=
      mem_collapsedBoundaryEdges.mp heBoundary
    rw [vertices_simpleEdge]
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem huU

/-- Every supported source edge is uniquely classified as internal to the
module, exterior to it, or crossing from one outside vertex into it. -/
theorem module_exterior_cross_union_eq
    {F : SimpleEdgeSet V} {X K : Finset V}
    (hSupported : SupportedOn F X) (_hKX : K ⊆ X) :
    edgesInside F K ∪ edgesInside F (X \ K) ∪
        crossEdgesTo F K (X \ K) = F := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [Finset.mem_union] at he
    rcases he with heInternalOrExterior | heCross
    · rw [Finset.mem_union] at heInternalOrExterior
      rcases heInternalOrExterior with heK | heU
      · exact (mem_edgesInside.mp heK).1
      · exact (mem_edgesInside.mp heU).1
    · obtain ⟨u, _huU, heNew⟩ := mem_crossEdgesTo.mp heCross
      exact (mem_newEdgesAt.mp heNew).1
  · intro e heF
    have heX := hSupported heF
    have hVerticesNonempty : e.vertices.Nonempty :=
      Finset.card_pos.mp (by simp)
    by_cases heK : e.vertices ⊆ K
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (mem_edgesInside.mpr ⟨heF, heK⟩))
    · have hOutside : ∃ x ∈ e.vertices, x ∉ K := by
        by_contra hNot
        apply heK
        intro x hx
        by_contra hxK
        exact hNot ⟨x, hx, hxK⟩
      obtain ⟨x, hxEdge, hxK⟩ := hOutside
      obtain ⟨a, hxa, heEq⟩ := exists_otherEndpoint e hxEdge
      have hxX : x ∈ X := heX hxEdge
      have haEdge : a ∈ e.vertices := by
        rw [heEq, vertices_simpleEdge]
        simp
      have haX : a ∈ X := heX haEdge
      have hxU : x ∈ X \ K := Finset.mem_sdiff.mpr ⟨hxX, hxK⟩
      by_cases haK : a ∈ K
      · apply Finset.mem_union_right
        apply mem_crossEdgesTo.mpr
        refine ⟨x, hxU, ?_⟩
        apply mem_newEdgesAt.mpr
        refine ⟨heF, ?_, heK⟩
        rw [heEq, vertices_simpleEdge]
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem haK
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply mem_edgesInside.mpr
        refine ⟨heF, ?_⟩
        rw [heEq, vertices_simpleEdge]
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hxU
        · exact Finset.mem_sdiff.mpr ⟨haX, haK⟩

/-- Global edge count of the explicit quotient. -/
theorem card_graphExtensionQuotientEdges
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hSupported : SupportedOn F X) (hKX : K ⊆ X) (hrK : r ∈ K)
    (hOne : ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1) :
    (graphExtensionQuotientEdges F X K r hrK).card +
        (edgesInside F K).card = F.card := by
  let U := X \ K
  have hUK : Disjoint U K := Finset.sdiff_disjoint
  have hOneU : ∀ u ∈ U, (newEdgesAt F K u).card ≤ 1 := by
    intro u huU
    exact hOne u (Finset.mem_sdiff.mp huU).1 (Finset.mem_sdiff.mp huU).2
  have hBoundaryCard := card_collapsedBoundaryEdges hrK hUK hOneU
  have hExteriorBoundary :=
    exteriorEdges_disjoint_collapsedBoundaryEdges (F := F) hrK hUK
  have hInternalExterior := internalEdges_disjoint_exteriorEdges F hUK
  have hInternalCross := internalEdges_disjoint_crossEdgesTo F K U
  have hExteriorCross := exteriorEdges_disjoint_crossEdgesTo F hUK
  have hSourceUnion :
      edgesInside F K ∪ edgesInside F U ∪ crossEdgesTo F K U = F := by
    exact module_exterior_cross_union_eq hSupported hKX
  have hSourceUnionDisjoint :
      Disjoint (edgesInside F K ∪ edgesInside F U) (crossEdgesTo F K U) := by
    rw [Finset.disjoint_left]
    intro e heUnion heCross
    rw [Finset.mem_union] at heUnion
    rcases heUnion with heK | heU
    · exact (Finset.disjoint_left.mp hInternalCross) heK heCross
    · exact (Finset.disjoint_left.mp hExteriorCross) heU heCross
  have hSourceCard :
      (edgesInside F K).card + (edgesInside F U).card +
          (crossEdgesTo F K U).card = F.card := by
    calc
      (edgesInside F K).card + (edgesInside F U).card +
            (crossEdgesTo F K U).card =
          ((edgesInside F K ∪ edgesInside F U) ∪
            crossEdgesTo F K U).card := by
        rw [Finset.card_union_of_disjoint hSourceUnionDisjoint,
          Finset.card_union_of_disjoint hInternalExterior]
      _ = F.card := congrArg Finset.card hSourceUnion
  have hQuotientCard :
      (graphExtensionQuotientEdges F X K r hrK).card =
        (edgesInside F U).card + (crossEdgesTo F K U).card := by
    rw [graphExtensionQuotientEdges,
      Finset.card_union_of_disjoint hExteriorBoundary, hBoundaryCard]
  rw [hQuotientCard]
  omega

theorem card_graphExtensionQuotientVertices
    {X K : Finset V} {r : V} (hKX : K ⊆ X) (hrK : r ∈ K) :
    (graphExtensionQuotientVertices X K r).card = X.card - K.card + 1 := by
  have hrNot : r ∉ X \ K := by simp [hrK]
  rw [graphExtensionQuotientVertices, Finset.card_insert_of_notMem hrNot,
    Finset.card_sdiff_of_subset hKX]

/-- Once quotient sparsity is available, global tightness follows by exact
subtraction of the tight module's internal edge count.  This lemma is kept
separate because the same count identity is also used by the null-cellule
dimension induction. -/
theorem graphExtensionQuotient_tight
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hG : SimpleTight22On F X) (hModule : IsSimpleGraphExtensionModule F X K)
    (hrK : r ∈ K) :
    Tight22 (graphExtensionQuotientEdges F X K r hrK)
      (graphExtensionQuotientVertices X K r) := by
  refine ⟨⟨r, by simp [graphExtensionQuotientVertices]⟩, ?_⟩
  rw [edgesInside_eq_self_of_supported
    (graphExtensionQuotientEdges_supported hrK)]
  have hCard := card_graphExtensionQuotientEdges hG.supported
    hModule.subset_active hrK hModule.outside_simple
  have hGlobal : F.card = 2 * (X.card - 1) := by
    rw [← edgesInside_eq_self_of_supported hG.supported]
    exact hG.tight.2
  have hVertices := card_graphExtensionQuotientVertices
    hModule.subset_active hrK
  rw [hModule.tight.2, hGlobal] at hCard
  rw [hVertices]
  have hKpos : 0 < K.card := Finset.card_pos.mpr hModule.tight.1
  have hKle : K.card ≤ X.card :=
    Finset.card_le_card hModule.subset_active
  omega

/-! ## Subset lifting and quotient sparsity -/

/-- Outside vertices of a quotient test set, with the retained module
representative removed. -/
def quotientOutsideSubset (Y X K : Finset V) (r : V) : Finset V :=
  Y.erase r ∩ (X \ K)

theorem quotientOutsideSubset_subset_Y
    (Y X K : Finset V) (r : V) :
    quotientOutsideSubset Y X K r ⊆ Y := by
  intro u hu
  exact (Finset.mem_erase.mp (Finset.mem_inter.mp hu).1).2

theorem quotientOutsideSubset_subset_outside
    (Y X K : Finset V) (r : V) :
    quotientOutsideSubset Y X K r ⊆ X \ K := by
  intro u hu
  exact (Finset.mem_inter.mp hu).2

theorem quotientOutsideSubset_disjoint
    (Y X K : Finset V) (r : V) :
    Disjoint (quotientOutsideSubset Y X K r) K :=
  (Finset.disjoint_of_subset_left
    (quotientOutsideSubset_subset_outside Y X K r)
    Finset.sdiff_disjoint)

theorem edgesInside_exterior_eq_quotientOutsideSubset
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V} (hrK : r ∈ K) :
    edgesInside (edgesInside F (X \ K)) Y =
      edgesInside F (quotientOutsideSubset Y X K r) := by
  ext e
  simp only [mem_edgesInside]
  constructor
  · rintro ⟨⟨heF, heOutside⟩, heY⟩
    refine ⟨heF, ?_⟩
    intro u huEdge
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, heY huEdge⟩, heOutside huEdge⟩
    intro hur
    subst u
    exact (Finset.mem_sdiff.mp (heOutside huEdge)).2 hrK
  · rintro ⟨heF, heLift⟩
    refine ⟨⟨heF, ?_⟩, ?_⟩
    · intro u huEdge
      exact (Finset.mem_inter.mp (heLift huEdge)).2
    · intro u huEdge
      exact (Finset.mem_erase.mp
        (Finset.mem_inter.mp (heLift huEdge)).1).2

theorem edgesInside_collapsedBoundaryEdges_eq_of_mem
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V}
    (hrK : r ∈ K) (hrY : r ∈ Y) :
    edgesInside
        (collapsedBoundaryEdges F K (X \ K) r hrK Finset.sdiff_disjoint) Y =
      collapsedBoundaryEdges F K (quotientOutsideSubset Y X K r) r hrK
        (quotientOutsideSubset_disjoint Y X K r) := by
  ext e
  constructor
  · intro he
    have he' := mem_edgesInside.mp he
    obtain ⟨u, huOutside, huNew, hru, heEq⟩ :=
      mem_collapsedBoundaryEdges.mp he'.1
    apply mem_collapsedBoundaryEdges.mpr
    refine ⟨u, ?_, huNew, hru, heEq⟩
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hru, ?_⟩, huOutside⟩
    have huVertices : u ∈ (simpleEdge r u hru).vertices := by
      rw [vertices_simpleEdge]
      simp
    exact he'.2 (heEq.symm ▸ huVertices)
  · intro he
    obtain ⟨u, huLift, huNew, hru, heEq⟩ :=
      mem_collapsedBoundaryEdges.mp he
    apply mem_edgesInside.mpr
    refine ⟨?_, ?_⟩
    · apply mem_collapsedBoundaryEdges.mpr
      exact ⟨u, (Finset.mem_inter.mp huLift).2, huNew, hru, heEq⟩
    · rw [heEq, vertices_simpleEdge]
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hrY
      · exact (Finset.mem_erase.mp (Finset.mem_inter.mp huLift).1).2

theorem edgesInside_collapsedBoundaryEdges_eq_empty_of_not_mem
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V}
    (hrK : r ∈ K) (hrY : r ∉ Y) :
    edgesInside
      (collapsedBoundaryEdges F K (X \ K) r hrK Finset.sdiff_disjoint) Y =
      ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨e, he⟩ := hne
  have he' := mem_edgesInside.mp he
  obtain ⟨u, _huOutside, _huNew, hru, heEq⟩ :=
    mem_collapsedBoundaryEdges.mp he'.1
  apply hrY
  have hrVertices : r ∈ (simpleEdge r u hru).vertices := by
    rw [vertices_simpleEdge]
    simp
  exact he'.2 (heEq.symm ▸ hrVertices)

theorem edgesInside_union_edges
    (A B : SimpleEdgeSet V) (Y : Finset V) :
    edgesInside (A ∪ B) Y = edgesInside A Y ∪ edgesInside B Y := by
  ext e
  simp only [mem_edgesInside, Finset.mem_union]
  aesop

theorem card_edgesInside_graphExtensionQuotient_of_mem
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V}
    (hrK : r ∈ K) (hrY : r ∈ Y)
    (hOne : ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1) :
    (edgesInside (graphExtensionQuotientEdges F X K r hrK) Y).card =
      (edgesInside F (quotientOutsideSubset Y X K r)).card +
        (crossEdgesTo F K (quotientOutsideSubset Y X K r)).card := by
  let UY := quotientOutsideSubset Y X K r
  have hUYdisjoint : Disjoint UY K := quotientOutsideSubset_disjoint Y X K r
  have hOneUY : ∀ u ∈ UY, (newEdgesAt F K u).card ≤ 1 := by
    intro u huUY
    have huOutside := quotientOutsideSubset_subset_outside Y X K r huUY
    exact hOne u (Finset.mem_sdiff.mp huOutside).1
      (Finset.mem_sdiff.mp huOutside).2
  have hDisjoint := exteriorEdges_disjoint_collapsedBoundaryEdges
    (F := F) hrK hUYdisjoint
  rw [graphExtensionQuotientEdges,
    edgesInside_union_edges,
    edgesInside_exterior_eq_quotientOutsideSubset hrK,
    edgesInside_collapsedBoundaryEdges_eq_of_mem hrK hrY,
    Finset.card_union_of_disjoint hDisjoint,
    card_collapsedBoundaryEdges hrK hUYdisjoint hOneUY]

theorem card_edgesInside_graphExtensionQuotient_of_not_mem
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V}
    (hrK : r ∈ K) (hrY : r ∉ Y) :
    (edgesInside (graphExtensionQuotientEdges F X K r hrK) Y).card =
      (edgesInside F (quotientOutsideSubset Y X K r)).card := by
  rw [graphExtensionQuotientEdges,
    edgesInside_union_edges,
    edgesInside_exterior_eq_quotientOutsideSubset hrK,
    edgesInside_collapsedBoundaryEdges_eq_empty_of_not_mem hrK hrY]
  simp

/-- Every induced quotient edge set obeys the `(2,2)` count.  A set
containing the collapse point is lifted to
`K ∪ U`, and the exact tight count of `K` is subtracted from the source
sparsity inequality. -/
theorem graphExtensionQuotient_sparse
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hG : SimpleTight22On F X)
    (hModule : IsSimpleGraphExtensionModule F X K) (hrK : r ∈ K) :
    Sparse22 (graphExtensionQuotientEdges F X K r hrK) := by
  intro Y hY
  let UY := quotientOutsideSubset Y X K r
  have hUYdisjoint : Disjoint UY K := quotientOutsideSubset_disjoint Y X K r
  have hUYsubsetY : UY ⊆ Y := quotientOutsideSubset_subset_Y Y X K r
  by_cases hrY : r ∈ Y
  · rw [card_edgesInside_graphExtensionQuotient_of_mem
      hrK hrY hModule.outside_simple]
    change (edgesInside F UY).card + (crossEdgesTo F K UY).card ≤
      2 * (Y.card - 1)
    have hPacket := card_module_add_exterior_add_cross_le
      (F := F) hUYdisjoint
    have hLiftNonempty : (K ∪ UY).Nonempty :=
      hModule.tight.1.mono Finset.subset_union_left
    have hSourceUpper := hG.sparse (K ∪ UY) hLiftNonempty
    have hUnionCard : (K ∪ UY).card = K.card + UY.card := by
      rw [Finset.card_union_of_disjoint hUYdisjoint.symm]
    rw [hModule.tight.2] at hPacket
    rw [hUnionCard] at hSourceUpper
    have hEraseCard : (Y.erase r).card = Y.card - 1 :=
      Finset.card_erase_of_mem hrY
    have hUYsubsetErase : UY ⊆ Y.erase r := by
      intro u hu
      exact (Finset.mem_inter.mp hu).1
    have hUYcard : UY.card ≤ Y.card - 1 := by
      rw [← hEraseCard]
      exact Finset.card_le_card hUYsubsetErase
    have hKpos : 0 < K.card := Finset.card_pos.mpr hModule.tight.1
    omega
  · rw [card_edgesInside_graphExtensionQuotient_of_not_mem hrK hrY]
    change (edgesInside F UY).card ≤ 2 * (Y.card - 1)
    by_cases hUYne : UY.Nonempty
    · have hUpper := hG.sparse UY hUYne
      have hUYcard : UY.card ≤ Y.card :=
        Finset.card_le_card hUYsubsetY
      have hYpos : 0 < Y.card := Finset.card_pos.mpr hY
      omega
    · have hUYempty : UY = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUYne
      rw [hUYempty]
      have hEdgesEmpty : edgesInside F (∅ : Finset V) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hne
        obtain ⟨e, he⟩ := hne
        have hSub := (mem_edgesInside.mp he).2
        have hCardLe := Finset.card_le_card hSub
        rw [e.card_vertices] at hCardLe
        simp at hCardLe
      rw [hEdgesEmpty]
      simp

/-- The explicit contraction of a simple graph-extension module is again
a supported simple `(2,2)`-tight graph. -/
theorem graphExtensionQuotient_simpleTight22On
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hG : SimpleTight22On F X)
    (hModule : IsSimpleGraphExtensionModule F X K) (hrK : r ∈ K) :
    SimpleTight22On (graphExtensionQuotientEdges F X K r hrK)
      (graphExtensionQuotientVertices X K r) :=
  ⟨graphExtensionQuotientEdges_supported hrK,
    graphExtensionQuotient_sparse hG hModule hrK,
    graphExtensionQuotient_tight hG hModule hrK⟩

theorem graphExtensionQuotientVertices_card_lt
    {X K : Finset V} {r : V} (hKX : K ⊆ X) (hrK : r ∈ K)
    (hKcard : 2 ≤ K.card) :
    (graphExtensionQuotientVertices X K r).card < X.card := by
  rw [card_graphExtensionQuotientVertices hKX hrK]
  have hKle : K.card ≤ X.card := Finset.card_le_card hKX
  omega

/-! ## Closed extended reduction theorem -/

/-- Exact inverse graph-extension surgery: a proper tight module `K` is
replaced by one retained representative `r`, with quotient edges given by
the explicit provenance construction above. -/
def IsInverseGraphExtension
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ K : Finset V, ∃ r : V, ∃ hrK : r ∈ K,
    IsSimpleGraphExtensionModule F X K ∧
      X' = graphExtensionQuotientVertices X K r ∧
      F' = graphExtensionQuotientEdges F X K r hrK

/-- An inverse graph-extension whose explicit quotient remains supported
simple `(2,2)`-tight. -/
def LegalInverseGraphExtension
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseGraphExtension F X F' X' ∧ SimpleTight22On F' X'

/-- The reduction class naturally suited to the bulk--interface induction:
the four Nixon--Owen local moves are retained, but an arbitrary proper
tight module may also be contracted in one exact graph-extension step. -/
def HasNixonOwenOrGraphExtensionReduction
    (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  HasNixonOwenReduction F X ∨
    ∃ F' : SimpleEdgeSet V, ∃ X' : Finset V,
      X'.card < X.card ∧ LegalInverseGraphExtension F X F' X'

theorem legalInverseGraphExtension_of_module
    {F : SimpleEdgeSet V} {X K : Finset V}
    (hG : SimpleTight22On F X)
    (hModule : IsSimpleGraphExtensionModule F X K)
    (hKcard : 2 ≤ K.card) :
    ∃ r : V, ∃ hrK : r ∈ K,
      (graphExtensionQuotientVertices X K r).card < X.card ∧
      LegalInverseGraphExtension F X
        (graphExtensionQuotientEdges F X K r hrK)
        (graphExtensionQuotientVertices X K r) := by
  obtain ⟨r, hrK⟩ := hModule.tight.1
  refine ⟨r, hrK,
    graphExtensionQuotientVertices_card_lt hModule.subset_active hrK hKcard,
    ?_, graphExtensionQuotient_simpleTight22On hG hModule hrK⟩
  exact ⟨K, r, hrK, hModule, rfl, rfl⟩

/-- End-to-end closure of the simple `(2,2)`-tight combinatorial reduction
stage without triangle sequences.  Every graph with at least two active
vertices is either the exact `K₄` base or has a strictly smaller legal
reduction, where the additional graph-extension case is an explicit
supported sparse-and-tight quotient. -/
theorem isK4Base_or_hasNixonOwenOrGraphExtensionReduction
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    IsK4Base F X ∨ HasNixonOwenOrGraphExtensionReduction F X := by
  rcases hasNixonOwenReduction_or_isK4Base_or_graphExtensionModule
      hG hXcard with hReduce | hBase | ⟨K, hModule, hKcard⟩
  · exact Or.inr (Or.inl hReduce)
  · exact Or.inl hBase
  · have hKtwo : 2 ≤ K.card := by omega
    obtain ⟨r, hrK, hCard, hLegal⟩ :=
      legalInverseGraphExtension_of_module hG hModule hKtwo
    exact Or.inr (Or.inr ⟨_, _, hCard, hLegal⟩)

/-! ## Agreement with the ordinary simple push-forward semantics -/

theorem Sym2.map_collapseSet_eq_self_of_toFinset_subset_outside
    (z : Sym2 V) {X K : Finset V} {r : V}
    (hz : z.toFinset ⊆ X \ K) :
    z.map (collapseSet K r) = z := by
  induction z using Sym2.inductionOn with
  | _ a b =>
      have ha : a ∈ X \ K := hz (by simp [Sym2.toFinset_mk_eq])
      have hb : b ∈ X \ K := hz (by simp [Sym2.toFinset_mk_eq])
      simp [Sym2.map_mk, collapseSet,
        (Finset.mem_sdiff.mp ha).2, (Finset.mem_sdiff.mp hb).2]

theorem Sym2.isDiag_map_collapseSet_of_toFinset_subset
    (z : Sym2 V) {K : Finset V} {r : V}
    (hz : z.toFinset ⊆ K) :
    (z.map (collapseSet K r)).IsDiag := by
  induction z using Sym2.inductionOn with
  | _ a b =>
      have ha : a ∈ K := hz (by simp [Sym2.toFinset_mk_eq])
      have hb : b ∈ K := hz (by simp [Sym2.toFinset_mk_eq])
      simp [Sym2.map_mk, collapseSet, ha, hb, Sym2.mk_isDiag_iff]

/-- A provenance edge entering `K` at the outside vertex `u` maps to the
single quotient boundary edge `ru`. -/
theorem exists_simpleEdge_eq_map_collapseSet_of_mem_newEdgesAt
    {F : SimpleEdgeSet V} {K : Finset V} {r u : V}
    (hrK : r ∈ K) (huK : u ∉ K) {e : SimpleEdge V}
    (heNew : e ∈ newEdgesAt F K u) :
    ∃ hru : r ≠ u,
      (simpleEdge r u hru).1 = e.1.map (collapseSet K r) := by
  have hNew := mem_newEdgesAt.mp heNew
  have hOutside : ∃ x ∈ e.vertices, x ∉ K := by
    by_contra hNot
    apply hNew.2.2
    intro x hx
    by_contra hxK
    exact hNot ⟨x, hx, hxK⟩
  obtain ⟨x, hxEdge, hxK⟩ := hOutside
  have hxu : x = u := by
    rcases Finset.mem_insert.mp (hNew.2.1 hxEdge) with hxu | hxK'
    · exact hxu
    · exact (hxK hxK').elim
  have huEdge : u ∈ e.vertices := hxu ▸ hxEdge
  obtain ⟨a, hua, heEq⟩ := exists_otherEndpoint e huEdge
  have haEdge : a ∈ e.vertices := by
    rw [heEq, vertices_simpleEdge]
    simp
  have haK : a ∈ K := by
    rcases Finset.mem_insert.mp (hNew.2.1 haEdge) with hau | haK
    · exact (hua hau.symm).elim
    · exact haK
  have hru : r ≠ u := by
    intro hru
    exact huK (hru ▸ hrK)
  refine ⟨hru, ?_⟩
  rw [heEq]
  simp [simpleEdge, Sym2.map_mk, collapseSet, huK, haK]

/-- The explicit quotient edge set is extensionally the ordinary simple
push-forward of the source edge set along `collapseSet`.  Thus the custom
provenance presentation above is not a surrogate notion of contraction. -/
theorem graphExtensionQuotientEdges_isSimpleEdgePushForward
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hSupported : SupportedOn F X) (hKX : K ⊆ X) (hrK : r ∈ K) :
    IsSimpleEdgePushForward (collapseSet K r) F
      (graphExtensionQuotientEdges F X K r hrK) := by
  intro e'
  constructor
  · intro he'
    rw [graphExtensionQuotientEdges, Finset.mem_union] at he'
    rcases he' with heExterior | heBoundary
    · refine ⟨e', (mem_edgesInside.mp heExterior).1, ?_⟩
      exact (Sym2.map_collapseSet_eq_self_of_toFinset_subset_outside
        e'.1 (mem_edgesInside.mp heExterior).2).symm
    · obtain ⟨u, huOutside, huNew, hru, heEq⟩ :=
        mem_collapsedBoundaryEdges.mp heBoundary
      obtain ⟨e, heNew⟩ := huNew
      have huK : u ∉ K := (Finset.mem_sdiff.mp huOutside).2
      obtain ⟨hru', hMap⟩ :=
        exists_simpleEdge_eq_map_collapseSet_of_mem_newEdgesAt
          hrK huK heNew
      refine ⟨e, (mem_newEdgesAt.mp heNew).1, ?_⟩
      calc
        e'.1 = (simpleEdge r u hru).1 := congrArg Subtype.val heEq
        _ = (simpleEdge r u hru').1 := by rfl
        _ = e.1.map (collapseSet K r) := hMap
  · rintro ⟨e, heF, heImage⟩
    have hClass : e ∈
        edgesInside F K ∪ edgesInside F (X \ K) ∪
          crossEdgesTo F K (X \ K) := by
      rw [module_exterior_cross_union_eq hSupported hKX]
      exact heF
    rw [Finset.mem_union] at hClass
    rcases hClass with hInternalOrExterior | hCross
    · rw [Finset.mem_union] at hInternalOrExterior
      rcases hInternalOrExterior with hInternal | hExterior
      · exfalso
        apply e'.2
        rw [heImage]
        exact Sym2.isDiag_map_collapseSet_of_toFinset_subset e.1
          (mem_edgesInside.mp hInternal).2
      · have hMap := Sym2.map_collapseSet_eq_self_of_toFinset_subset_outside
          (r := r) e.1 (mem_edgesInside.mp hExterior).2
        have heEq : e' = e := by
          apply Subtype.ext
          exact heImage.trans hMap
        subst e'
        exact Finset.mem_union_left _ hExterior
    · obtain ⟨u, huOutside, heNew⟩ := mem_crossEdgesTo.mp hCross
      have huK : u ∉ K := (Finset.mem_sdiff.mp huOutside).2
      obtain ⟨hru, hMap⟩ :=
        exists_simpleEdge_eq_map_collapseSet_of_mem_newEdgesAt hrK huK heNew
      apply Finset.mem_union_right
      apply mem_collapsedBoundaryEdges.mpr
      refine ⟨u, huOutside, ⟨e, heNew⟩, hru, ?_⟩
      apply Subtype.ext
      exact heImage.trans hMap.symm

end RB31E2E


end
end BundleSource0015

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0015/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0015.json"

section BundleSource0016
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagForest.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagForest.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# The terminal hyperforest forced by a sparse provenance completion

For one active flag, the restored terminal triangle together with its
private ghost star is a literal completed `K₄`.  This file derives, rather
than assumes, the two combinatorial consequences needed by the provenance
induction:

* distinct terminal triples meet in at most one live vertex;
* every nonempty family of `j` flags uses at least `2*j+1` live terminals.

The proof uses the actual finite edge and vertex unions.  In particular, the
six-edge count and pairwise edge-disjointness are proved as `Finset`
identities; no forest or counting conclusion is stored in `State`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

def liveVertexEmbedding : V ↪ V ⊕ Flag where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def ghostVertexEmbedding : Flag ↪ V ⊕ Flag where
  toFun := Sum.inr
  inj' := Sum.inr_injective

/-! ## One completed flag -/

/-- The three live terminals of `t`, together with its private ghost. -/
def State.flagVertices (S : State V Flag) (t : Flag) : Finset (V ⊕ Flag) :=
  insert (Sum.inr t) ((S.terminals t).map liveVertexEmbedding)

/-- The actual completion edges supported on one flag's four vertices. -/
def State.flagCompletedEdges (S : State V Flag) (t : Flag) :
    SimpleEdgeSet (V ⊕ Flag) :=
  edgesInside S.completionEdges (S.flagVertices t)

@[simp]
theorem State.mem_flagVertices_live (S : State V Flag) (t : Flag) (v : V) :
    Sum.inl v ∈ S.flagVertices t ↔ v ∈ S.terminals t := by
  simp [State.flagVertices, liveVertexEmbedding]

@[simp]
theorem State.mem_flagVertices_ghost (S : State V Flag) (t u : Flag) :
    Sum.inr u ∈ S.flagVertices t ↔ u = t := by
  simp [State.flagVertices, liveVertexEmbedding]

theorem State.flagVertices_nonempty (S : State V Flag) (t : Flag) :
    (S.flagVertices t).Nonempty :=
  ⟨Sum.inr t, by simp⟩

@[simp]
theorem State.card_flagVertices (S : State V Flag) (t : Flag) :
    (S.flagVertices t).card = 4 := by
  rw [State.flagVertices, Finset.card_insert_of_notMem]
  · rw [Finset.card_map, S.terminals_card t]
  · simp [liveVertexEmbedding]

/-- Every terminal pair of a flag is present after completion: it is either
the distinguished restored edge or one of the two live terminal edges. -/
theorem State.lifted_terminalEdge_mem_completionEdges
    (S : State V Flag) (t : Flag) {a b : V}
    (ha : a ∈ S.terminals t) (hb : b ∈ S.terminals t) (hab : a ≠ b) :
    liftLiveEdge (Flag := Flag) (simpleEdge a b hab) ∈ S.completionEdges := by
  let e : SimpleEdge V := simpleEdge a b hab
  have heSupported : e.vertices ⊆ S.terminals t := by
    rw [show e = simpleEdge a b hab from rfl, vertices_simpleEdge]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  by_cases heMissing : e = S.missing t
  · rw [show simpleEdge a b hab = e from rfl, heMissing]
    exact S.lifted_missing_mem_completionEdges t
  · apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact S.other_terminal_edges_live t e heSupported heMissing

/-- Every active flag gives named vertices for a genuine `K₄` in the
literal completion. -/
theorem State.exists_namedK4Witness_completion
    (S : State V Flag) (t : Flag) :
    ∃ a b c : V,
      S.terminals t = {a, b, c} ∧
      NamedK4Witness S.completionEdges
        (Sum.inr t) (Sum.inl a) (Sum.inl b) (Sum.inl c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hterm⟩ :=
    Finset.card_eq_three.mp (S.terminals_card t)
  have ha : a ∈ S.terminals t := by rw [hterm]; simp
  have hb : b ∈ S.terminals t := by rw [hterm]; simp
  have hc : c ∈ S.terminals t := by rw [hterm]; simp
  have hab' : Sum.inl a ≠ (Sum.inl b : V ⊕ Flag) := by
    exact fun h ↦ hab (Sum.inl.inj h)
  have hac' : Sum.inl a ≠ (Sum.inl c : V ⊕ Flag) := by
    exact fun h ↦ hac (Sum.inl.inj h)
  have hbc' : Sum.inl b ≠ (Sum.inl c : V ⊕ Flag) := by
    exact fun h ↦ hbc (Sum.inl.inj h)
  refine ⟨a, b, c, hterm, ?_⟩
  refine
    { hva := by simp
      hvb := by simp
      hvc := by simp
      hab := hab'
      hac := hac'
      hbc := hbc'
      va_mem := ?_
      vb_mem := ?_
      vc_mem := ?_
      ab_mem := ?_
      ac_mem := ?_
      bc_mem := ?_ }
  · simpa [ghostEdge, simpleEdge] using S.ghostEdge_mem_completionEdges t ha
  · simpa [ghostEdge, simpleEdge] using S.ghostEdge_mem_completionEdges t hb
  · simpa [ghostEdge, simpleEdge] using S.ghostEdge_mem_completionEdges t hc
  · simpa [liftLiveEdge, simpleEdge] using
      S.lifted_terminalEdge_mem_completionEdges t ha hb hab
  · simpa [liftLiveEdge, simpleEdge] using
      S.lifted_terminalEdge_mem_completionEdges t ha hc hac
  · simpa [liftLiveEdge, simpleEdge] using
      S.lifted_terminalEdge_mem_completionEdges t hb hc hbc

/-- The four vertices of an active flag are tight in every sparse
completion. -/
theorem State.flagVertices_tight
    (S : State V Flag) (hSparse : S.CompletionSparse) (t : Flag) :
    Tight22 S.completionEdges (S.flagVertices t) := by
  obtain ⟨a, b, c, hterm, hK⟩ := S.exists_namedK4Witness_completion t
  have hTight := tight22_namedK4Vertices hSparse hK
  simpa [State.flagVertices, namedK4Vertices, hterm, liveVertexEmbedding] using hTight

/-- A single flag contributes exactly the six edges of its completed
`K₄`. -/
@[simp]
theorem State.card_flagCompletedEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) (t : Flag) :
    (S.flagCompletedEdges t).card = 6 := by
  have hTight := S.flagVertices_tight hSparse t
  rw [State.flagCompletedEdges, hTight.2, S.card_flagVertices]

theorem State.flagCompletedEdges_subset_completionEdges
    (S : State V Flag) (t : Flag) :
    S.flagCompletedEdges t ⊆ S.completionEdges :=
  edgesInside_subset _ _

/-! ## A small simple-graph cardinal bound -/

def endpointIntoSubset
    {A : Type*} [DecidableEq A] (X : Finset A) (e : SimpleEdge A)
    (he : e.vertices ⊆ X) : e.vertices ↪ X where
  toFun x := ⟨x.1, he x.2⟩
  inj' := by
    intro x y hxy
    exact Subtype.ext (Subtype.mk.inj hxy)

def restrictedEdgeVertices
    {A : Type*} [DecidableEq A] (X : Finset A) (e : SimpleEdge A)
    (he : e.vertices ⊆ X) : Finset X :=
  e.vertices.attach.map (endpointIntoSubset X e he)

@[simp]
private theorem card_restrictedEdgeVertices
    {A : Type*} [DecidableEq A] (X : Finset A) (e : SimpleEdge A)
    (he : e.vertices ⊆ X) :
    (restrictedEdgeVertices X e he).card = 2 := by
  simp [restrictedEdgeVertices, e.card_vertices]

private theorem map_restrictedEdgeVertices
    {A : Type*} [DecidableEq A] (X : Finset A) (e : SimpleEdge A)
    (he : e.vertices ⊆ X) :
    (restrictedEdgeVertices X e he).map
        ⟨Subtype.val, Subtype.val_injective⟩ = e.vertices := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp hx
    obtain ⟨z, _hz, hza⟩ := Finset.mem_map.mp ha
    have hzval : z.1 = x :=
      (congrArg Subtype.val hza).trans hax
    exact hzval ▸ z.2
  · intro hx
    let z : e.vertices := ⟨x, hx⟩
    let a : X := ⟨x, he hx⟩
    apply Finset.mem_map.mpr
    refine ⟨a, ?_, rfl⟩
    apply Finset.mem_map.mpr
    exact ⟨z, by simp [z], rfl⟩

def edgesInsideToTwoSubsets
    {A : Type*} [DecidableEq A] (F : SimpleEdgeSet A) (X : Finset A) :
    (↑(edgesInside F X)) ↪
      (↑((Finset.univ : Finset X).powersetCard 2)) where
  toFun e :=
    ⟨restrictedEdgeVertices X e.1 (mem_edgesInside.mp e.2).2, by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, card_restrictedEdgeVertices _ _ _⟩⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    apply SimpleEdge.eq_of_vertices_eq
    have hmap := congrArg
      (fun Y : Finset X ↦ Y.map ⟨Subtype.val, Subtype.val_injective⟩)
      (Subtype.mk.inj hef)
    simpa [map_restrictedEdgeVertices] using hmap

/-- A simple graph induced on `X` has at most `X.card.choose 2` edges. -/
theorem card_edgesInside_le_choose_two
    {A : Type*} [DecidableEq A] (F : SimpleEdgeSet A) (X : Finset A) :
    (edgesInside F X).card ≤ X.card.choose 2 := by
  let emb := edgesInsideToTwoSubsets F X
  have hcard := Fintype.card_le_of_injective emb emb.injective
  calc
    (edgesInside F X).card ≤
        ((Finset.univ : Finset X).powersetCard 2).card := by
      simpa only [Fintype.card_coe] using hcard
    _ = (Finset.univ : Finset X).card.choose 2 :=
      Finset.card_powersetCard 2 (Finset.univ : Finset X)
    _ = X.card.choose 2 := by simp

/-- A `(2,2)`-tight vertex set with at least two vertices has at least four
vertices.  The exclusion of sizes two and three uses the actual simple-edge
bound above. -/
theorem four_le_card_of_tight22
    {A : Type*} [DecidableEq A] {F : SimpleEdgeSet A} {X : Finset A}
    (hTight : Tight22 F X) (hTwo : 2 ≤ X.card) :
    4 ≤ X.card := by
  have hBound := card_edgesInside_le_choose_two F X
  rw [hTight.2] at hBound
  by_contra hFour
  have hCases : X.card = 2 ∨ X.card = 3 := by omega
  rcases hCases with hTwoEq | hThreeEq
  · rw [hTwoEq] at hBound
    norm_num at hBound
  · rw [hThreeEq] at hBound
    norm_num at hBound

/-! ## Distinct flags meet in at most one terminal -/

theorem State.flagVertices_inter_eq
    (S : State V Flag) {t u : Flag} (htu : t ≠ u) :
    S.flagVertices t ∩ S.flagVertices u =
      (S.terminals t ∩ S.terminals u).map liveVertexEmbedding := by
  ext x
  cases x with
  | inl v =>
      simp only [Finset.mem_inter, State.mem_flagVertices_live,
        Finset.mem_map]
      constructor
      · rintro ⟨hvt, hvu⟩
        exact ⟨v, ⟨hvt, hvu⟩, rfl⟩
      · rintro ⟨a, ha, hav⟩
        have hav' : a = v := Sum.inl.inj hav
        subst a
        exact ha
  | inr w =>
      simp only [Finset.mem_inter, State.mem_flagVertices_ghost,
        Finset.mem_map]
      constructor
      · rintro ⟨hwt, hwu⟩
        exact (htu (hwt.symm.trans hwu)).elim
      · rintro ⟨a, _ha, haw⟩
        change (Sum.inl a : V ⊕ Flag) = Sum.inr w at haw
        exact (Sum.inl_ne_inr haw).elim

theorem State.card_flagVertices_inter
    (S : State V Flag) {t u : Flag} (htu : t ≠ u) :
    (S.flagVertices t ∩ S.flagVertices u).card =
      (S.terminals t ∩ S.terminals u).card := by
  rw [S.flagVertices_inter_eq htu, Finset.card_map]

/-- Completion sparsity forbids two distinct flags from sharing two live
terminals. -/
theorem State.card_terminal_inter_le_one
    (S : State V Flag) (hSparse : S.CompletionSparse)
    {t u : Flag} (htu : t ≠ u) :
    (S.terminals t ∩ S.terminals u).card ≤ 1 := by
  by_contra hOne
  have hTwo : 2 ≤ (S.terminals t ∩ S.terminals u).card := by omega
  have hInterNonempty : (S.flagVertices t ∩ S.flagVertices u).Nonempty := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (S.terminals t ∩ S.terminals u).card)
    refine ⟨Sum.inl v, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact S.mem_flagVertices_live t v |>.2 (Finset.mem_inter.mp hv).1
    · exact S.mem_flagVertices_live u v |>.2 (Finset.mem_inter.mp hv).2
  have hInterTight :=
    (tight22_union_inter hSparse
      (S.flagVertices_tight hSparse t)
      (S.flagVertices_tight hSparse u) hInterNonempty).2
  have hInterTwo : 2 ≤ (S.flagVertices t ∩ S.flagVertices u).card := by
    rw [S.card_flagVertices_inter htu]
    exact hTwo
  have hFour := four_le_card_of_tight22 hInterTight hInterTwo
  rw [S.card_flagVertices_inter htu] at hFour
  have hAtMostThree : (S.terminals t ∩ S.terminals u).card ≤ 3 := by
    calc
      (S.terminals t ∩ S.terminals u).card ≤ (S.terminals t).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = 3 := S.terminals_card t
  omega

/-- The six-edge packets of distinct flags are disjoint, now as a derived
fact about the literal edge sets. -/
theorem State.disjoint_flagCompletedEdges
    (S : State V Flag) (hSparse : S.CompletionSparse)
    {t u : Flag} (htu : t ≠ u) :
    Disjoint (S.flagCompletedEdges t) (S.flagCompletedEdges u) := by
  rw [Finset.disjoint_left]
  intro e het heu
  have heSubset : e.vertices ⊆ S.flagVertices t ∩ S.flagVertices u :=
    Finset.subset_inter (mem_edgesInside.mp het).2 (mem_edgesInside.mp heu).2
  have hCard := Finset.card_le_card heSubset
  rw [e.card_vertices, S.card_flagVertices_inter htu] at hCard
  have hOne := S.card_terminal_inter_le_one hSparse htu
  omega

/-! ## Exact unions and the terminal hyperforest inequality -/

/-- Live terminals used by a finite family of flags. -/
def State.terminalUnion (S : State V Flag) (A : Finset Flag) : Finset V :=
  A.biUnion S.terminals

/-- All live terminals and all private ghosts used by `A`. -/
def State.flagVertexUnion (S : State V Flag) (A : Finset Flag) :
    Finset (V ⊕ Flag) :=
  (S.terminalUnion A).map liveVertexEmbedding ∪
    A.map ghostVertexEmbedding

/-- Union of the actual six-edge packets belonging to `A`. -/
def State.flagEdgeUnion (S : State V Flag) (A : Finset Flag) :
    SimpleEdgeSet (V ⊕ Flag) :=
  A.biUnion S.flagCompletedEdges

theorem State.flagVertices_subset_flagVertexUnion
    (S : State V Flag) {A : Finset Flag} {t : Flag} (ht : t ∈ A) :
    S.flagVertices t ⊆ S.flagVertexUnion A := by
  intro x hx
  cases x with
  | inl v =>
      have hv : v ∈ S.terminals t := (S.mem_flagVertices_live t v).1 hx
      apply Finset.mem_union_left
      exact Finset.mem_map.mpr
        ⟨v, Finset.mem_biUnion.mpr ⟨t, ht, hv⟩, rfl⟩
  | inr u =>
      have hut : u = t := (S.mem_flagVertices_ghost t u).1 hx
      subst u
      apply Finset.mem_union_right
      exact Finset.mem_map.mpr ⟨t, ht, rfl⟩

theorem State.card_flagVertexUnion (S : State V Flag) (A : Finset Flag) :
    (S.flagVertexUnion A).card = (S.terminalUnion A).card + A.card := by
  have hDisjoint :
      Disjoint ((S.terminalUnion A).map liveVertexEmbedding)
        (A.map ghostVertexEmbedding) := by
    rw [Finset.disjoint_left]
    intro x hxLive hxGhost
    obtain ⟨v, _hv, hvx⟩ := Finset.mem_map.mp hxLive
    obtain ⟨t, _ht, htx⟩ := Finset.mem_map.mp hxGhost
    have hbad : (Sum.inl v : V ⊕ Flag) = Sum.inr t := hvx.trans htx.symm
    exact Sum.inl_ne_inr hbad
  rw [State.flagVertexUnion, Finset.card_union_of_disjoint hDisjoint,
    Finset.card_map, Finset.card_map]

theorem State.pairwiseDisjoint_flagCompletedEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) (A : Finset Flag) :
    (A : Set Flag).PairwiseDisjoint S.flagCompletedEdges := by
  intro t _ht u _hu htu
  exact S.disjoint_flagCompletedEdges hSparse htu

theorem State.card_flagEdgeUnion
    (S : State V Flag) (hSparse : S.CompletionSparse) (A : Finset Flag) :
    (S.flagEdgeUnion A).card = 6 * A.card := by
  rw [State.flagEdgeUnion,
    Finset.card_biUnion (S.pairwiseDisjoint_flagCompletedEdges hSparse A)]
  simp [S.card_flagCompletedEdges hSparse, Nat.mul_comm]

theorem State.flagEdgeUnion_subset_completionEdges
    (S : State V Flag) (A : Finset Flag) :
    S.flagEdgeUnion A ⊆ S.completionEdges := by
  intro e he
  obtain ⟨t, _ht, het⟩ := Finset.mem_biUnion.mp he
  exact S.flagCompletedEdges_subset_completionEdges t het

theorem State.flagEdgeUnion_supported
    (S : State V Flag) (A : Finset Flag) :
    SupportedOn (S.flagEdgeUnion A) (S.flagVertexUnion A) := by
  intro e he
  obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he
  exact (mem_edgesInside.mp het).2.trans
    (S.flagVertices_subset_flagVertexUnion ht)

theorem State.flagEdgeUnion_subset_edgesInside
    (S : State V Flag) (A : Finset Flag) :
    S.flagEdgeUnion A ⊆ edgesInside S.completionEdges (S.flagVertexUnion A) := by
  intro e he
  exact mem_edgesInside.mpr
    ⟨S.flagEdgeUnion_subset_completionEdges A he,
      S.flagEdgeUnion_supported A he⟩

/-- The incidence ledger has exactly three terminal occurrences per flag. -/
theorem State.sum_card_terminals
    (S : State V Flag) (A : Finset Flag) :
    (∑ t ∈ A, (S.terminals t).card) = 3 * A.card := by
  simp [S.terminals_card, Nat.mul_comm]

/-- Every nonempty family of `j` active flags uses at least `2*j+1`
distinct live terminals. -/
theorem State.two_mul_card_add_one_le_card_terminalUnion
    (S : State V Flag) (hSparse : S.CompletionSparse)
    {A : Finset Flag} (hA : A.Nonempty) :
    2 * A.card + 1 ≤ (S.terminalUnion A).card := by
  have hVertexNonempty : (S.flagVertexUnion A).Nonempty := by
    obtain ⟨t, ht⟩ := hA
    exact ⟨Sum.inr t,
      S.flagVertices_subset_flagVertexUnion ht (by simp)⟩
  have hSparseUpper := hSparse (S.flagVertexUnion A) hVertexNonempty
  have hEdgeLower := Finset.card_le_card
    (S.flagEdgeUnion_subset_edgesInside A)
  have hEdgeCard := S.card_flagEdgeUnion hSparse A
  have hVertexCard := S.card_flagVertexUnion A
  have hPositive : 1 ≤ (S.terminalUnion A).card + A.card := by
    rw [← hVertexCard]
    exact Finset.card_pos.mpr hVertexNonempty
  have hArithmetic :
      6 * A.card + 2 ≤
        2 * ((S.terminalUnion A).card + A.card) := by
    rw [hEdgeCard] at hEdgeLower
    rw [hVertexCard] at hSparseUpper
    omega
  exact terminal_count_ge_two_mul_add_one
    (Finset.card_pos.mpr hA) hArithmetic

/-- Derived hyperforest property of the terminal triples.  This definition
is only an abbreviation for the quantified Finset inequality; it is never a
field of `State` and the theorem below constructs it from completion
sparsity. -/
def State.TerminalHyperforest (S : State V Flag) : Prop :=
  ∀ A : Finset Flag, A.Nonempty → 2 * A.card + 1 ≤ (S.terminalUnion A).card

theorem State.terminalHyperforest
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    S.TerminalHyperforest := by
  intro A hA
  exact S.two_mul_card_add_one_le_card_terminalUnion hSparse hA

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0016

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0016/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0016.json"

section BundleSource0017
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagSelection.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagSelection.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# A derived low-degree selection lemma for provenance flags

This file partitions the exact live vertex type into vertices contained in
zero, one, or at least two active flags.  It then proves the three ledgers
used by the provenance induction from the literal `State` data:

* the completion has `|E| + 4 * |Flag|` edges;
* the terminal incidence sum is `3 * |Flag|`;
* the live degree sum is `2 * |E|`.

Together with completion sparsity and the terminal-hyperforest overlap
theorem, these identities force either an outside vertex of live degree at
most three or a private terminal of live degree at most two.  The selection
conclusion is a theorem, not a field of `State`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-! ## Flag multiplicity and the exact live-vertex partition -/

/-- Active flags containing a live vertex. -/
def State.activeFlagsAt (S : State V Flag) (v : V) : Finset Flag :=
  Finset.univ.filter fun t ↦ v ∈ S.terminals t

/-- Number of active flags containing a live vertex. -/
def State.flagMultiplicity (S : State V Flag) (v : V) : ℕ :=
  (S.activeFlagsAt v).card

/-- Live vertices outside every active flag. -/
def State.outsideVertices (S : State V Flag) : Finset V :=
  Finset.univ.filter fun v ↦ S.flagMultiplicity v = 0

/-- Live vertices belonging to exactly one active flag. -/
def State.privateVertices (S : State V Flag) : Finset V :=
  Finset.univ.filter fun v ↦ S.flagMultiplicity v = 1

/-- Live vertices belonging to at least two active flags. -/
def State.sharedVertices (S : State V Flag) : Finset V :=
  Finset.univ.filter fun v ↦ 2 ≤ S.flagMultiplicity v

/-- Total flag incidence carried by shared live vertices. -/
def State.sharedIncidence (S : State V Flag) : ℕ :=
  ∑ v ∈ S.sharedVertices, S.flagMultiplicity v

@[simp]
theorem State.mem_activeFlagsAt (S : State V Flag) (v : V) (t : Flag) :
    t ∈ S.activeFlagsAt v ↔ v ∈ S.terminals t := by
  simp [State.activeFlagsAt]

@[simp]
theorem State.mem_outsideVertices (S : State V Flag) (v : V) :
    v ∈ S.outsideVertices ↔ S.flagMultiplicity v = 0 := by
  simp [State.outsideVertices]

@[simp]
theorem State.mem_privateVertices (S : State V Flag) (v : V) :
    v ∈ S.privateVertices ↔ S.flagMultiplicity v = 1 := by
  simp [State.privateVertices]

@[simp]
theorem State.mem_sharedVertices (S : State V Flag) (v : V) :
    v ∈ S.sharedVertices ↔ 2 ≤ S.flagMultiplicity v := by
  simp [State.sharedVertices]

theorem State.outside_private_disjoint (S : State V Flag) :
    Disjoint S.outsideVertices S.privateVertices := by
  rw [Finset.disjoint_left]
  intro v hvO hvP
  rw [S.mem_outsideVertices] at hvO
  rw [S.mem_privateVertices] at hvP
  omega

theorem State.outside_union_private_disjoint_shared (S : State V Flag) :
    Disjoint (S.outsideVertices ∪ S.privateVertices) S.sharedVertices := by
  rw [Finset.disjoint_left]
  intro v hvOP hvS
  rw [Finset.mem_union] at hvOP
  rw [S.mem_sharedVertices] at hvS
  rcases hvOP with hvO | hvP
  · rw [S.mem_outsideVertices] at hvO
    omega
  · rw [S.mem_privateVertices] at hvP
    omega

theorem State.outside_union_private_union_shared (S : State V Flag) :
    S.outsideVertices ∪ S.privateVertices ∪ S.sharedVertices = Finset.univ := by
  ext v
  simp only [Finset.mem_union, S.mem_outsideVertices,
    S.mem_privateVertices, S.mem_sharedVertices, Finset.mem_univ, iff_true]
  omega

/-- Exact cardinal partition of the live vertex type. -/
theorem State.card_live_partition (S : State V Flag) :
    Fintype.card V =
      S.outsideVertices.card + S.privateVertices.card + S.sharedVertices.card := by
  calc
    Fintype.card V = (Finset.univ : Finset V).card := by simp
    _ = (S.outsideVertices ∪ S.privateVertices ∪ S.sharedVertices).card := by
      rw [S.outside_union_private_union_shared]
    _ = S.outsideVertices.card + S.privateVertices.card +
          S.sharedVertices.card := by
      rw [Finset.card_union_of_disjoint
        S.outside_union_private_disjoint_shared,
        Finset.card_union_of_disjoint S.outside_private_disjoint]

/-! ## Exact completion-edge bookkeeping -/

omit [Fintype V] [Fintype Flag] in
private theorem ghostEdge_eq_iff
    {t u : Flag} {v w : V} :
    ghostEdge t v = ghostEdge u w ↔ t = u ∧ v = w := by
  constructor
  · intro h
    have ht : Sum.inr t ∈ (ghostEdge u w).vertices := by
      rw [← h]
      simp
    have hv : Sum.inl v ∈ (ghostEdge u w).vertices := by
      rw [← h]
      simp
    constructor
    · simpa using ht
    · simpa using hv
  · rintro ⟨rfl, rfl⟩
    rfl

omit [Fintype V] [Fintype Flag] in
private theorem ghostEdge_fixed_injective (t : Flag) :
    Function.Injective (ghostEdge t : V → SimpleEdge (V ⊕ Flag)) := by
  intro v w h
  exact (ghostEdge_eq_iff.mp h).2

private theorem ghostEdge_flags_disjoint
    (S : State V Flag) {t u : Flag} (htu : t ≠ u) :
    Disjoint
      ((S.terminals t).image fun v ↦ ghostEdge t v)
      ((S.terminals u).image fun v ↦ ghostEdge u v) := by
  rw [Finset.disjoint_left]
  intro e het heu
  obtain ⟨v, _hv, hve⟩ := Finset.mem_image.mp het
  obtain ⟨w, _hw, hwe⟩ := Finset.mem_image.mp heu
  have heq : ghostEdge t v = ghostEdge u w := hve.trans hwe.symm
  exact htu (ghostEdge_eq_iff.mp heq).1

private theorem pairwiseDisjoint_ghostStars (S : State V Flag) :
    ((Finset.univ : Finset Flag) : Set Flag).PairwiseDisjoint
      (fun t ↦ (S.terminals t).image fun v ↦ ghostEdge t v) := by
  intro t _ht u _hu htu
  exact ghostEdge_flags_disjoint S htu

@[simp]
theorem State.card_ghostStarEdges (S : State V Flag) :
    S.ghostStarEdges.card = 3 * Fintype.card Flag := by
  rw [State.ghostStarEdges,
    Finset.card_biUnion (pairwiseDisjoint_ghostStars S)]
  calc
    (∑ t ∈ (Finset.univ : Finset Flag),
        ((S.terminals t).image fun v ↦ ghostEdge t v).card) =
        ∑ _t ∈ (Finset.univ : Finset Flag), 3 := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.card_image_of_injective _ (ghostEdge_fixed_injective t),
        S.terminals_card t]
    _ = 3 * Fintype.card Flag := by simp [Nat.mul_comm]

omit [Fintype V] [Fintype Flag] in
private theorem no_ghost_mem_liftLiveEdge_vertices
    (e : SimpleEdge V) (t : Flag) :
    Sum.inr t ∉ (liftLiveEdge (Flag := Flag) e).vertices := by
  intro ht
  obtain ⟨a, ha⟩ : e.vertices.Nonempty :=
    Finset.card_pos.mp (by simp)
  obtain ⟨b, hab, he⟩ := exists_otherEndpoint e ha
  rw [he] at ht
  simp [liftLiveEdge, simpleEdge, SimpleEdge.vertices,
    Sym2.toFinset_mk_eq] at ht

private theorem State.liftedLiveEdges_disjoint_ghostStarEdges
    (S : State V Flag) :
    Disjoint S.liftedLiveEdges S.ghostStarEdges := by
  rw [Finset.disjoint_left]
  intro e heLive heGhost
  obtain ⟨t, _ht, heStar⟩ := Finset.mem_biUnion.mp heGhost
  obtain ⟨v, _hv, hve⟩ := Finset.mem_image.mp heStar
  obtain ⟨f, _hf, hfe⟩ := Finset.mem_map.mp heLive
  have hghost : Sum.inr t ∈ e.vertices := by
    rw [← hve]
    simp
  rw [← hfe] at hghost
  exact no_ghost_mem_liftLiveEdge_vertices f t hghost

private theorem State.restoredMissingEdges_disjoint_ghostStarEdges
    (S : State V Flag) :
    Disjoint S.restoredMissingEdges S.ghostStarEdges := by
  rw [Finset.disjoint_left]
  intro e heMissing heGhost
  obtain ⟨t, _ht, hte⟩ := Finset.mem_image.mp heMissing
  obtain ⟨u, _hu, heStar⟩ := Finset.mem_biUnion.mp heGhost
  obtain ⟨v, _hv, hve⟩ := Finset.mem_image.mp heStar
  have hghost : Sum.inr u ∈ e.vertices := by
    rw [← hve]
    simp
  rw [← hte] at hghost
  exact no_ghost_mem_liftLiveEdge_vertices (S.missing t) u hghost

private theorem State.liftedLiveEdges_disjoint_restoredMissingEdges
    (S : State V Flag) :
    Disjoint S.liftedLiveEdges S.restoredMissingEdges := by
  rw [Finset.disjoint_left]
  intro e heLive heMissing
  obtain ⟨t, _ht, hte⟩ := Finset.mem_image.mp heMissing
  rw [← hte] at heLive
  exact S.missing_not_live t ((S.mem_liftedLiveEdges (S.missing t)).1 heLive)

private theorem State.missing_injective_of_completionSparse
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    Function.Injective S.missing := by
  intro t u htuEdge
  by_contra htu
  have hSupported : (S.missing t).vertices ⊆
      S.terminals t ∩ S.terminals u := by
    exact Finset.subset_inter (S.missing_supported t)
      (htuEdge ▸ S.missing_supported u)
  have hCard := Finset.card_le_card hSupported
  rw [(S.missing t).card_vertices] at hCard
  have hOne := S.card_terminal_inter_le_one hSparse htu
  omega

@[simp]
theorem State.card_restoredMissingEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    S.restoredMissingEdges.card = Fintype.card Flag := by
  rw [State.restoredMissingEdges,
    Finset.card_image_of_injective Finset.univ]
  · simp
  · intro t u htu
    apply S.missing_injective_of_completionSparse hSparse
    exact liftLiveEdge_injective htu

/-- Completion edges not already present in the live graph. -/
def State.extraCompletionEdges (S : State V Flag) :
    SimpleEdgeSet (V ⊕ Flag) :=
  S.restoredMissingEdges ∪ S.ghostStarEdges

@[simp]
theorem State.card_extraCompletionEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    S.extraCompletionEdges.card = 4 * Fintype.card Flag := by
  rw [State.extraCompletionEdges,
    Finset.card_union_of_disjoint
      S.restoredMissingEdges_disjoint_ghostStarEdges,
    S.card_restoredMissingEdges hSparse, S.card_ghostStarEdges]
  omega

theorem State.liftedLiveEdges_disjoint_extraCompletionEdges
    (S : State V Flag) :
    Disjoint S.liftedLiveEdges S.extraCompletionEdges := by
  rw [State.extraCompletionEdges, Finset.disjoint_union_right]
  exact ⟨S.liftedLiveEdges_disjoint_restoredMissingEdges,
    S.liftedLiveEdges_disjoint_ghostStarEdges⟩

theorem State.completionEdges_eq_live_union_extra (S : State V Flag) :
    S.completionEdges = S.liftedLiveEdges ∪ S.extraCompletionEdges := by
  ext e
  simp [State.completionEdges, State.extraCompletionEdges]

/-- Exact completion ledger: each flag adds one restored terminal edge and
three private ghost edges. -/
@[simp]
theorem State.card_completionEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    S.completionEdges.card = S.edges.card + 4 * Fintype.card Flag := by
  rw [S.completionEdges_eq_live_union_extra,
    Finset.card_union_of_disjoint
      S.liftedLiveEdges_disjoint_extraCompletionEdges,
    State.liftedLiveEdges, Finset.card_map,
    S.card_extraCompletionEdges hSparse]

/-- Full-universe consequence of completion sparsity, written without a
truncated subtraction. -/
theorem State.live_edge_budget
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (hV : (Finset.univ : Finset V).Nonempty) :
    S.edges.card + 2 * Fintype.card Flag + 2 ≤ 2 * Fintype.card V := by
  have hVCard : 1 ≤ Fintype.card V := by
    exact Nat.succ_le_iff.mpr (by simpa using Finset.card_pos.mpr hV)
  obtain ⟨v, _hv⟩ := hV
  have hUniverse : (Finset.univ : Finset (V ⊕ Flag)).Nonempty :=
    ⟨Sum.inl v, Finset.mem_univ _⟩
  have hBound := hSparse (Finset.univ : Finset (V ⊕ Flag)) hUniverse
  have hInside :
      edgesInside S.completionEdges (Finset.univ : Finset (V ⊕ Flag)) =
        S.completionEdges := by
    ext e
    simp
  rw [hInside, S.card_completionEdges hSparse] at hBound
  simp only [Finset.card_univ, Fintype.card_sum] at hBound
  omega

/-! ## Incidence and degree ledgers -/

/-- Live terminal edges of flag `t` incident with `v`. -/
def State.flagLiveEdgesAt (S : State V Flag) (t : Flag) (v : V) :
    SimpleEdgeSet V :=
  S.edges.filter fun e ↦ v ∈ e.vertices ∧ e.vertices ⊆ S.terminals t

@[simp]
theorem State.mem_flagLiveEdgesAt
    (S : State V Flag) (t : Flag) (v : V) (e : SimpleEdge V) :
    e ∈ S.flagLiveEdgesAt t v ↔
      e ∈ S.edges ∧ v ∈ e.vertices ∧ e.vertices ⊆ S.terminals t := by
  simp [State.flagLiveEdgesAt]

private theorem State.exists_flagLiveEdgeAt
    (S : State V Flag) (t : Flag) {v : V} (hv : v ∈ S.terminals t) :
    (S.flagLiveEdgesAt t v).Nonempty := by
  have hEraseCard : ((S.terminals t).erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hv, S.terminals_card t]
  obtain ⟨a, b, hab, hErase⟩ := Finset.card_eq_two.mp hEraseCard
  have haErase : a ∈ (S.terminals t).erase v := by rw [hErase]; simp
  have hbErase : b ∈ (S.terminals t).erase v := by rw [hErase]; simp
  have hva : v ≠ a := (Finset.mem_erase.mp haErase).1.symm
  have hvb : v ≠ b := (Finset.mem_erase.mp hbErase).1.symm
  have ha : a ∈ S.terminals t := (Finset.mem_erase.mp haErase).2
  have hb : b ∈ S.terminals t := (Finset.mem_erase.mp hbErase).2
  let ea : SimpleEdge V := simpleEdge v a hva
  let eb : SimpleEdge V := simpleEdge v b hvb
  have heaSupported : ea.vertices ⊆ S.terminals t := by
    rw [show ea = simpleEdge v a hva from rfl, vertices_simpleEdge]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact ha
  have hebSupported : eb.vertices ⊆ S.terminals t := by
    rw [show eb = simpleEdge v b hvb from rfl, vertices_simpleEdge]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact hb
  have heab : ea ≠ eb := by
    intro heq
    rcases (simpleEdge_eq_simpleEdge_iff v a v b hva hvb).mp heq with
        ⟨_hvv, hab'⟩ | ⟨hvb', _hav⟩
    · exact hab hab'
    · exact hvb hvb'
  by_cases heaMissing : ea = S.missing t
  · have hebMissing : eb ≠ S.missing t := by
      intro heb
      exact heab (heaMissing.trans heb.symm)
    refine ⟨eb, S.mem_flagLiveEdgesAt t v eb |>.2 ⟨?_, ?_, hebSupported⟩⟩
    · exact S.other_terminal_edges_live t eb hebSupported hebMissing
    · rw [show eb = simpleEdge v b hvb from rfl, vertices_simpleEdge]
      simp
  · refine ⟨ea, S.mem_flagLiveEdgesAt t v ea |>.2 ⟨?_, ?_, heaSupported⟩⟩
    · exact S.other_terminal_edges_live t ea heaSupported heaMissing
    · rw [show ea = simpleEdge v a hva from rfl, vertices_simpleEdge]
      simp

private theorem State.disjoint_flagLiveEdgesAt
    (S : State V Flag) (hSparse : S.CompletionSparse) (v : V)
    {t u : Flag} (htu : t ≠ u) :
    Disjoint (S.flagLiveEdgesAt t v) (S.flagLiveEdgesAt u v) := by
  rw [Finset.disjoint_left]
  intro e het heu
  have hSubset : e.vertices ⊆ S.terminals t ∩ S.terminals u :=
    Finset.subset_inter (S.mem_flagLiveEdgesAt t v e |>.1 het).2.2
      (S.mem_flagLiveEdgesAt u v e |>.1 heu).2.2
  have hCard := Finset.card_le_card hSubset
  rw [e.card_vertices] at hCard
  have hOne := S.card_terminal_inter_le_one hSparse htu
  omega

private theorem State.pairwiseDisjoint_flagLiveEdgesAt
    (S : State V Flag) (hSparse : S.CompletionSparse) (v : V) :
    ((S.activeFlagsAt v : Finset Flag) : Set Flag).PairwiseDisjoint
      (fun t ↦ S.flagLiveEdgesAt t v) := by
  intro t _ht u _hu htu
  exact S.disjoint_flagLiveEdgesAt hSparse v htu

/-- Each flag incidence at `v` supplies a distinct incident live edge. -/
theorem State.flagMultiplicity_le_liveDegree
    (S : State V Flag) (hSparse : S.CompletionSparse) (v : V) :
    S.flagMultiplicity v ≤ edgeSetDegree S.edges v := by
  let U : SimpleEdgeSet V :=
    (S.activeFlagsAt v).biUnion fun t ↦ S.flagLiveEdgesAt t v
  have hEach :
      (∑ _t ∈ S.activeFlagsAt v, 1) ≤
        ∑ t ∈ S.activeFlagsAt v, (S.flagLiveEdgesAt t v).card := by
    exact Finset.sum_le_sum fun t ht ↦
      Finset.card_pos.mpr
        (S.exists_flagLiveEdgeAt t ((S.mem_activeFlagsAt v t).1 ht))
  have hUnionCard :
      U.card = ∑ t ∈ S.activeFlagsAt v, (S.flagLiveEdgesAt t v).card := by
    exact Finset.card_biUnion (S.pairwiseDisjoint_flagLiveEdgesAt hSparse v)
  have hUnionSubset : U ⊆ incidentEdges S.edges v := by
    intro e he
    obtain ⟨t, _ht, het⟩ := Finset.mem_biUnion.mp he
    have het' := (S.mem_flagLiveEdgesAt t v e).1 het
    exact mem_incidentEdges.mpr ⟨het'.1, het'.2.1⟩
  calc
    S.flagMultiplicity v = ∑ _t ∈ S.activeFlagsAt v, 1 := by
      simp [State.flagMultiplicity]
    _ ≤ ∑ t ∈ S.activeFlagsAt v, (S.flagLiveEdgesAt t v).card := hEach
    _ = U.card := hUnionCard.symm
    _ ≤ (incidentEdges S.edges v).card := Finset.card_le_card hUnionSubset
    _ = edgeSetDegree S.edges v := rfl

private theorem State.sum_flagMultiplicity_eq_sum_terminalCards
    (S : State V Flag) :
    (∑ v ∈ (Finset.univ : Finset V), S.flagMultiplicity v) =
      ∑ t ∈ (Finset.univ : Finset Flag), (S.terminals t).card := by
  have hMultiplicity (v : V) :
      S.flagMultiplicity v =
        ∑ t ∈ (Finset.univ : Finset Flag),
          if v ∈ S.terminals t then 1 else 0 := by
    rw [State.flagMultiplicity, State.activeFlagsAt,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ v ∈ (Finset.univ : Finset V), S.flagMultiplicity v) =
        ∑ v ∈ (Finset.univ : Finset V),
          ∑ t ∈ (Finset.univ : Finset Flag),
            if v ∈ S.terminals t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact hMultiplicity v
    _ = ∑ t ∈ (Finset.univ : Finset Flag),
          ∑ v ∈ (Finset.univ : Finset V),
            if v ∈ S.terminals t then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ (Finset.univ : Finset Flag), (S.terminals t).card := by
      apply Finset.sum_congr rfl
      intro t _ht
      calc
        (∑ v ∈ (Finset.univ : Finset V),
            if v ∈ S.terminals t then 1 else 0) =
            ((Finset.univ : Finset V).filter
              fun v ↦ v ∈ S.terminals t).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = (S.terminals t).card := by
          congr
          ext v
          simp

private theorem State.sum_over_live_partition
    (S : State V Flag) (f : V → ℕ) :
    (∑ v ∈ (Finset.univ : Finset V), f v) =
      (∑ v ∈ S.outsideVertices, f v) +
      (∑ v ∈ S.privateVertices, f v) +
      ∑ v ∈ S.sharedVertices, f v := by
  rw [← S.outside_union_private_union_shared,
    Finset.sum_union S.outside_union_private_disjoint_shared,
    Finset.sum_union S.outside_private_disjoint]

/-- Exact terminal-incidence ledger after splitting live vertices into the
private and shared classes. -/
theorem State.private_card_add_sharedIncidence
    (S : State V Flag) :
    S.privateVertices.card + S.sharedIncidence = 3 * Fintype.card Flag := by
  have hTotal := S.sum_flagMultiplicity_eq_sum_terminalCards
  have hTerminal := S.sum_card_terminals (Finset.univ : Finset Flag)
  have hSplit := S.sum_over_live_partition S.flagMultiplicity
  have hOutside :
      (∑ v ∈ S.outsideVertices, S.flagMultiplicity v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact (S.mem_outsideVertices v).1 hv
  have hPrivate :
      (∑ v ∈ S.privateVertices, S.flagMultiplicity v) =
        S.privateVertices.card := by
    calc
      (∑ v ∈ S.privateVertices, S.flagMultiplicity v) =
          ∑ _v ∈ S.privateVertices, 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (S.mem_privateVertices v).1 hv
      _ = S.privateVertices.card := by simp
  rw [hOutside, hPrivate] at hSplit
  change (∑ v ∈ (Finset.univ : Finset V), S.flagMultiplicity v) =
      0 + S.privateVertices.card + S.sharedIncidence at hSplit
  rw [hTerminal] at hTotal
  simp only [Finset.card_univ] at hTotal
  omega

theorem State.two_mul_shared_card_le_sharedIncidence
    (S : State V Flag) :
    2 * S.sharedVertices.card ≤ S.sharedIncidence := by
  have hSum :
      (∑ _v ∈ S.sharedVertices, 2) ≤
        ∑ v ∈ S.sharedVertices, S.flagMultiplicity v := by
    exact Finset.sum_le_sum fun v hv ↦ (S.mem_sharedVertices v).1 hv
  simpa [State.sharedIncidence, Nat.mul_comm] using hSum

/-- The exact live-edge handshake on the full live vertex type. -/
theorem State.sum_liveDegree_eq_twice_edges (S : State V Flag) :
    (∑ v ∈ (Finset.univ : Finset V), edgeSetDegree S.edges v) =
      2 * S.edges.card := by
  apply sum_edgeSetDegree_eq_twice_card
  intro e _he v _hv
  exact Finset.mem_univ v

/-! ## The selection theorem -/

/-- Sparse completion forces a reducible live vertex: either a vertex
outside every flag has degree at most three, or a vertex private to one flag
has degree at most two. -/
theorem State.exists_outside_degree_le_three_or_private_degree_le_two
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (hV : (Finset.univ : Finset V).Nonempty) :
    (∃ v : V, S.flagMultiplicity v = 0 ∧ edgeSetDegree S.edges v ≤ 3) ∨
      ∃ v : V, S.flagMultiplicity v = 1 ∧ edgeSetDegree S.edges v ≤ 2 := by
  by_contra hSelection
  have hNoOutside :
      ∀ v : V, S.flagMultiplicity v = 0 → ¬ edgeSetDegree S.edges v ≤ 3 := by
    intro v hv hDegree
    exact hSelection (Or.inl ⟨v, hv, hDegree⟩)
  have hNoPrivate :
      ∀ v : V, S.flagMultiplicity v = 1 → ¬ edgeSetDegree S.edges v ≤ 2 := by
    intro v hv hDegree
    exact hSelection (Or.inr ⟨v, hv, hDegree⟩)
  have hOutsideDegree :
      ∀ v ∈ S.outsideVertices, 4 ≤ edgeSetDegree S.edges v := by
    intro v hv
    have hvZero := (S.mem_outsideVertices v).1 hv
    have hNot := hNoOutside v hvZero
    omega
  have hPrivateDegree :
      ∀ v ∈ S.privateVertices, 3 ≤ edgeSetDegree S.edges v := by
    intro v hv
    have hvOne := (S.mem_privateVertices v).1 hv
    have hNot := hNoPrivate v hvOne
    omega
  have hDegreeSplit := S.sum_over_live_partition (edgeSetDegree S.edges)
  have hOutsideLower :
      4 * S.outsideVertices.card ≤
        ∑ v ∈ S.outsideVertices, edgeSetDegree S.edges v := by
    have := Finset.sum_le_sum hOutsideDegree
    simpa [Nat.mul_comm] using this
  have hPrivateLower :
      3 * S.privateVertices.card ≤
        ∑ v ∈ S.privateVertices, edgeSetDegree S.edges v := by
    have := Finset.sum_le_sum hPrivateDegree
    simpa [Nat.mul_comm] using this
  have hSharedLower :
      S.sharedIncidence ≤
        ∑ v ∈ S.sharedVertices, edgeSetDegree S.edges v := by
    exact Finset.sum_le_sum fun v _hv ↦
      S.flagMultiplicity_le_liveDegree hSparse v
  have hDegreeLedger :
      4 * S.outsideVertices.card + 3 * S.privateVertices.card +
          S.sharedIncidence ≤ 2 * S.edges.card := by
    rw [← S.sum_liveDegree_eq_twice_edges, hDegreeSplit]
    omega
  exact not_all_flag_degrees_large
    (S.card_live_partition)
    (S.live_edge_budget hSparse hV)
    hDegreeLedger
    (S.private_card_add_sharedIncidence)
    (S.two_mul_shared_card_le_sharedIncidence)

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0017

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0017/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0017.json"

section BundleSource0018
/- Source: Papers/RigidityZheng_Combinatorics_Sparse22_Transport.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/Sparse22/Transport.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Transport of `(2,2)`-sparsity along injective vertex maps

Deletion and flag registration change the literal live-vertex type.  This
file supplies the provenance-preserving transport lemma needed for those
steps: if every transported child edge is an edge of a sparse parent, then
the child edge set is sparse.  No graph-isomorphism or sparsity conclusion
is stored as data.
-/

namespace RB31E2E

namespace Sparse22Transport

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Map a simple edge along an injective map of vertices. -/
def mapSimpleEdge (f : V ↪ W) (e : SimpleEdge V) : SimpleEdge W :=
  ⟨e.1.map f, by
    rw [Sym2.isDiag_map f.injective]
    exact e.2⟩

omit [DecidableEq V] [DecidableEq W] in
@[simp]
theorem mapSimpleEdge_val (f : V ↪ W) (e : SimpleEdge V) :
    (mapSimpleEdge f e).1 = e.1.map f := rfl

omit [DecidableEq V] [DecidableEq W] in
theorem mapSimpleEdge_injective (f : V ↪ W) :
    Function.Injective (mapSimpleEdge f) := by
  intro e g heg
  apply Subtype.ext
  exact Sym2.map.injective f.injective (Subtype.mk.inj heg)

/-- The induced embedding on simple edges. -/
def mapSimpleEdgeEmbedding (f : V ↪ W) : SimpleEdge V ↪ SimpleEdge W where
  toFun := mapSimpleEdge f
  inj' := mapSimpleEdge_injective f

/-- Map a finite simple edge set along an injective vertex map. -/
def mapEdgeSet (f : V ↪ W) (F : SimpleEdgeSet V) : SimpleEdgeSet W :=
  F.map (mapSimpleEdgeEmbedding f)

omit [DecidableEq V] [DecidableEq W] in
@[simp]
theorem mem_mapEdgeSet (f : V ↪ W) (F : SimpleEdgeSet V)
    (e : SimpleEdge V) :
    mapSimpleEdge f e ∈ mapEdgeSet f F ↔ e ∈ F := by
  constructor
  · intro he
    obtain ⟨g, hg, hge⟩ := Finset.mem_map.mp he
    have : g = e := mapSimpleEdge_injective f hge
    simpa [this] using hg
  · intro he
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩

omit [DecidableEq V] [DecidableEq W] in
@[simp]
theorem card_mapEdgeSet (f : V ↪ W) (F : SimpleEdgeSet V) :
    (mapEdgeSet f F).card = F.card := by
  simp [mapEdgeSet]

/-- Mapping an edge along an embedding maps its two endpoints into the
mapped endpoint set. -/
theorem mapSimpleEdge_vertices_subset
    (f : V ↪ W) (e : SimpleEdge V) (X : Finset V)
    (heX : e.vertices ⊆ X) :
    (mapSimpleEdge f e).vertices ⊆ X.map f := by
  intro y hy
  have hymem : y ∈ e.1.map f := by
    simpa [SimpleEdge.vertices] using hy
  obtain ⟨x, hx, hxy⟩ := (Sym2.mem_map.mp hymem)
  have hxVertices : x ∈ e.vertices := by
    simpa [SimpleEdge.vertices] using hx
  exact Finset.mem_map.mpr ⟨x, heX hxVertices, hxy⟩

/-- The mapped induced child edges inject into the induced parent edges. -/
theorem map_edgesInside_subset_edgesInside
    (f : V ↪ W) (F : SimpleEdgeSet V) (H : SimpleEdgeSet W)
    (hFH : mapEdgeSet f F ⊆ H) (X : Finset V) :
    mapEdgeSet f (edgesInside F X) ⊆ edgesInside H (X.map f) := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  have hgData := mem_edgesInside.mp hg
  apply mem_edgesInside.mpr
  exact ⟨hFH ((mem_mapEdgeSet f F g).2 hgData.1),
    mapSimpleEdge_vertices_subset f g X hgData.2⟩

/-- If the transported child edges lie in a sparse parent edge set, then
the child itself is sparse. -/
theorem sparse22_of_mapEdgeSet_subset
    (f : V ↪ W) {F : SimpleEdgeSet V} {H : SimpleEdgeSet W}
    (hH : Sparse22 H) (hFH : mapEdgeSet f F ⊆ H) : Sparse22 F := by
  intro X hX
  have hMapCard :
      (edgesInside F X).card =
        (mapEdgeSet f (edgesInside F X)).card := by
    rw [card_mapEdgeSet]
  have hSubset := map_edgesInside_subset_edgesInside f F H hFH X
  have hCardLe := Finset.card_le_card hSubset
  have hMapX : (X.map f).Nonempty := Finset.Nonempty.map hX
  have hSparse := hH (X.map f) hMapX
  have hXCard : (X.map f).card = X.card := Finset.card_map _
  rw [← hMapCard] at hCardLe
  exact hCardLe.trans (by simpa [hXCard] using hSparse)

end

end Sparse22Transport

end RB31E2E


end
end BundleSource0018

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0018/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0018.json"

section BundleSource0019
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagDeletion.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagDeletion.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Deleting an outside live vertex from a provenance-flag state

The provenance induction changes its literal live-vertex type after a
deletion.  This file constructs that child state rather than postulating
it.  If `v` belongs to no active flag, every terminal, missing edge, live
edge, and ghost star restricts to the subtype of vertices different from
`v`.  The child's completed graph maps edge-for-edge into the parent's
completed graph, so completion sparsity descends by the already proved
transport theorem.

No stress, response, semismallness, or height statement is stored in the
child state.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open Sparse22Transport

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The exact live-vertex type after deleting `v`. -/
abbrev RemainingVertex (v : V) := {u : V // u ≠ v}

/-- Inclusion of the remaining live vertices into the parent type. -/
def remainingVertexEmbedding (v : V) : RemainingVertex v ↪ V :=
  Function.Embedding.subtype _

/-- Inclusion of a child completion into the parent completion. -/
def remainingCompletionEmbedding (v : V) :
    (RemainingVertex v ⊕ Flag) ↪ (V ⊕ Flag) where
  toFun
    | Sum.inl u => Sum.inl u.1
    | Sum.inr t => Sum.inr t
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            change Sum.inl (x.1 : V) = Sum.inl (y.1 : V) at h
            exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
        | inr y =>
            change Sum.inl (x.1 : V) = Sum.inr y at h
            exact False.elim (Sum.inl_ne_inr h)
    | inr x =>
        cases y with
        | inl y =>
            change Sum.inr x = Sum.inl (y.1 : V) at h
            exact False.elim (Sum.inr_ne_inl h)
        | inr y =>
            change Sum.inr x = Sum.inr y at h
            exact congrArg Sum.inr (Sum.inr.inj h)

omit [Fintype V] in
theorem source_mem_vertices (e : SimpleEdge V) :
    e.source ∈ e.vertices := by
  rw [SimpleEdge.vertices, ← e.source_target_mk]
  simp [Sym2.toFinset_mk_eq]

omit [Fintype V] in
theorem target_mem_vertices (e : SimpleEdge V) :
    e.target ∈ e.vertices := by
  rw [SimpleEdge.vertices, ← e.source_target_mk]
  simp [Sym2.toFinset_mk_eq]

/-- Restrict a parent edge which avoids `v` to the remaining subtype. -/
def restrictSimpleEdge (v : V) (e : SimpleEdge V)
    (hv : v ∉ e.vertices) : SimpleEdge (RemainingVertex v) :=
  simpleEdge
    ⟨e.source, fun h => hv (h ▸ source_mem_vertices e)⟩
    ⟨e.target, fun h => hv (h ▸ target_mem_vertices e)⟩
    (by
      intro h
      exact e.source_ne_target (congrArg Subtype.val h))

omit [Fintype V] in
@[simp]
theorem map_restrictSimpleEdge (v : V) (e : SimpleEdge V)
    (hv : v ∉ e.vertices) :
    mapSimpleEdge (remainingVertexEmbedding v) (restrictSimpleEdge v e hv) = e := by
  apply Subtype.ext
  rw [mapSimpleEdge_val]
  simp only [restrictSimpleEdge, simpleEdge, Sym2.map_mk]
  exact e.source_target_mk

/-- A deleted parent edge, reindexed on the remaining vertex type. -/
def restrictDeletedEdge (F : SimpleEdgeSet V) (v : V)
    (e : deleteVertexEdges F v) : SimpleEdge (RemainingVertex v) :=
  restrictSimpleEdge v e.1 (mem_deleteVertexEdges.mp e.2).2

omit [Fintype V] in
theorem restrictDeletedEdge_injective (F : SimpleEdgeSet V) (v : V) :
    Function.Injective (restrictDeletedEdge F v) := by
  intro e f h
  have := congrArg (mapSimpleEdge (remainingVertexEmbedding v)) h
  apply Subtype.ext
  simpa [restrictDeletedEdge] using this

/-- Embedding of the deleted parent edge subtype into child edges. -/
def restrictDeletedEdgeEmbedding (F : SimpleEdgeSet V) (v : V) :
    deleteVertexEdges F v ↪ SimpleEdge (RemainingVertex v) where
  toFun := restrictDeletedEdge F v
  inj' := restrictDeletedEdge_injective F v

/-- The literal child live edge set. -/
def restrictedLiveEdges (F : SimpleEdgeSet V) (v : V) :
    SimpleEdgeSet (RemainingVertex v) :=
  (deleteVertexEdges F v).attach.map (restrictDeletedEdgeEmbedding F v)

omit [Fintype V] in
@[simp]
theorem mem_restrictedLiveEdges_iff
    (F : SimpleEdgeSet V) (v : V) (e : SimpleEdge (RemainingVertex v)) :
    e ∈ restrictedLiveEdges F v ↔
      mapSimpleEdge (remainingVertexEmbedding v) e ∈ deleteVertexEdges F v := by
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    change mapSimpleEdge (remainingVertexEmbedding v)
        (restrictDeletedEdge F v f) ∈ deleteVertexEdges F v
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]
    exact f.2
  · intro he
    let f : deleteVertexEdges F v :=
      ⟨mapSimpleEdge (remainingVertexEmbedding v) e, he⟩
    have hMap : restrictDeletedEdge F v f = e := by
      apply mapSimpleEdge_injective (remainingVertexEmbedding v)
      unfold restrictDeletedEdge
      rw [map_restrictSimpleEdge]
    exact Finset.mem_map.mpr ⟨f, Finset.mem_attach _ f, hMap⟩

omit [Fintype V] in
theorem map_restrictedLiveEdges (F : SimpleEdgeSet V) (v : V) :
    mapEdgeSet (remainingVertexEmbedding v) (restrictedLiveEdges F v) =
      deleteVertexEdges F v := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    exact (mem_restrictedLiveEdges_iff F v f).1 hf
  · intro he
    let f : deleteVertexEdges F v := ⟨e, he⟩
    let g := restrictDeletedEdge F v f
    have hg : g ∈ restrictedLiveEdges F v := by
      exact Finset.mem_map.mpr ⟨f, Finset.mem_attach _ f, rfl⟩
    refine Finset.mem_map.mpr ⟨g, hg, ?_⟩
    change mapSimpleEdge (remainingVertexEmbedding v)
        (restrictDeletedEdge F v f) = e
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]

/-- Restrict a finite vertex set known not to contain `v`. -/
def restrictVertexSet (v : V) (X : Finset V) (hv : v ∉ X) :
    Finset (RemainingVertex v) :=
  X.attach.map
    { toFun := fun x => ⟨x.1, fun h => hv (h ▸ x.2)⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : RemainingVertex v => z.1) h }

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem mem_restrictVertexSet_iff (v : V) (X : Finset V) (hv : v ∉ X)
    (u : RemainingVertex v) :
    u ∈ restrictVertexSet v X hv ↔ u.1 ∈ X := by
  constructor
  · intro hu
    unfold restrictVertexSet at hu
    obtain ⟨x, hx, hxu⟩ := Finset.mem_map.mp hu
    have hval : x.1 = u.1 := congrArg Subtype.val hxu
    exact hval ▸ x.2
  · intro hu
    let x : X := ⟨u.1, hu⟩
    unfold restrictVertexSet
    exact Finset.mem_map.mpr ⟨x, Finset.mem_attach _ x, Subtype.ext rfl⟩

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem card_restrictVertexSet (v : V) (X : Finset V) (hv : v ∉ X) :
    (restrictVertexSet v X hv).card = X.card := by
  simp [restrictVertexSet]

omit [Fintype V] [DecidableEq V] in
theorem map_restrictVertexSet (v : V) (X : Finset V) (hv : v ∉ X) :
    (restrictVertexSet v X hv).map (remainingVertexEmbedding v) = X := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, hx, hxu⟩ := Finset.mem_map.mp hu
    exact hxu.symm ▸
      (mem_restrictVertexSet_iff v X hv x).1 hx
  · intro hu
    have huv : u ≠ v := fun h => hv (h ▸ hu)
    let x : RemainingVertex v := ⟨u, huv⟩
    exact Finset.mem_map.mpr
      ⟨x, (mem_restrictVertexSet_iff v X hv x).2 hu, rfl⟩

omit [Fintype V] in
/-- Endpoint membership is preserved by restriction to the avoiding
subtype. -/
@[simp]
theorem mem_restrictSimpleEdge_vertices_iff
    (v : V) (e : SimpleEdge V) (hv : v ∉ e.vertices)
    (u : RemainingVertex v) :
    u ∈ (restrictSimpleEdge v e hv).vertices ↔ u.1 ∈ e.vertices := by
  rw [restrictSimpleEdge, vertices_simpleEdge, SimpleEdge.vertices,
    ← e.source_target_mk, Sym2.toFinset_mk_eq]
  constructor
  · intro hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val hu))
    · have hu' : u =
          (⟨e.target, fun h => hv (h ▸ target_mem_vertices e)⟩ :
            RemainingVertex v) := by simpa using hu
      exact Finset.mem_insert.mpr
        (Or.inr (by simpa using congrArg Subtype.val hu'))
  · intro hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · exact Finset.mem_insert.mpr
        (Or.inl (Subtype.ext (by simpa using hu)))
    · exact Finset.mem_insert.mpr
        (Or.inr (by
          rw [Finset.mem_singleton]
          apply Subtype.ext
          simpa using hu))

/-- Every endpoint of an edge mapped from the avoiding subtype still
avoids the deleted vertex. -/
theorem deleted_not_mem_mapped_vertices
    (v : V) (e : SimpleEdge (RemainingVertex v)) :
    v ∉ (mapSimpleEdge (remainingVertexEmbedding v) e).vertices := by
  intro hvEdge
  have hsub := mapSimpleEdge_vertices_subset
    (remainingVertexEmbedding v) e (Finset.univ : Finset (RemainingVertex v))
    (by simp)
  have hvRange := hsub hvEdge
  obtain ⟨u, _hu, huv⟩ := Finset.mem_map.mp hvRange
  exact u.2 huv

/-- An outside vertex occurs in no active terminal triple. -/
theorem not_mem_terminals_of_flagMultiplicity_eq_zero
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0)
    (t : Flag) : v ∉ S.terminals t := by
  intro hvt
  have ht : t ∈ S.activeFlagsAt v := (S.mem_activeFlagsAt v t).2 hvt
  have : 0 < S.flagMultiplicity v := by
    rw [State.flagMultiplicity]
    exact Finset.card_pos.mpr ⟨t, ht⟩
  omega

/-- The missing edge of a flag avoids an outside vertex. -/
theorem outside_not_mem_missing_vertices
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0)
    (t : Flag) : v ∉ (S.missing t).vertices := by
  intro hve
  exact not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t
    (S.missing_supported t hve)

/-- Delete an outside vertex and reindex all surviving provenance data. -/
def State.deleteOutside (S : State V Flag) (v : V)
    (hv : S.flagMultiplicity v = 0) : State (RemainingVertex v) Flag where
  edges := restrictedLiveEdges S.edges v
  terminals t := restrictVertexSet v (S.terminals t)
    (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t)
  missing t := restrictSimpleEdge v (S.missing t)
    (outside_not_mem_missing_vertices S v hv t)
  terminals_card t := by
    rw [card_restrictVertexSet, S.terminals_card]
  missing_supported t := by
    intro u hu
    rw [mem_restrictVertexSet_iff]
    apply S.missing_supported t
    exact (mem_restrictSimpleEdge_vertices_iff _ _ _ u).1 hu
  missing_not_live t := by
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge]
    simp [S.missing_not_live t]
  other_terminal_edges_live t e heT heMissing := by
    rw [mem_restrictedLiveEdges_iff]
    refine mem_deleteVertexEdges.mpr ⟨?_, deleted_not_mem_mapped_vertices v e⟩
    apply S.other_terminal_edges_live t
    · have hsub := mapSimpleEdge_vertices_subset
          (remainingVertexEmbedding v) e
          (restrictVertexSet v (S.terminals t)
            (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t)) heT
      simpa [map_restrictVertexSet] using hsub
    · intro hEq
      apply heMissing
      apply mapSimpleEdge_injective (remainingVertexEmbedding v)
      rw [hEq, map_restrictSimpleEdge]

@[simp]
theorem deleteOutside_edges (S : State V Flag) (v : V)
    (hv : S.flagMultiplicity v = 0) :
    (S.deleteOutside v hv).edges = restrictedLiveEdges S.edges v := rfl

@[simp]
theorem deleteOutside_terminals (S : State V Flag) (v : V)
    (hv : S.flagMultiplicity v = 0) (t : Flag) :
    (S.deleteOutside v hv).terminals t =
      restrictVertexSet v (S.terminals t)
        (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t) := rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_liftLiveEdge_remaining
    (v : V) (e : SimpleEdge (RemainingVertex v)) :
    mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
        (liftLiveEdge (Flag := Flag) e) =
      liftLiveEdge (Flag := Flag)
        (mapSimpleEdge (remainingVertexEmbedding v) e) := by
  apply Subtype.ext
  simp only [mapSimpleEdge_val, liftLiveEdge_val, Sym2.map_map]
  induction e.1 using Sym2.inductionOn with
  | _ a b =>
      simp [remainingCompletionEmbedding, remainingVertexEmbedding]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_ghostEdge_remaining
    (v : V) (t : Flag) (u : RemainingVertex v) :
    mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
        (ghostEdge t u) = ghostEdge t u.1 := by
  apply Subtype.ext
  change s(Sum.inr t, Sum.inl u.1) = s(Sum.inr t, Sum.inl u.1)
  rfl

/-- The completed outside child embeds edge-for-edge in the completed
parent. -/
theorem map_deleteOutside_completionEdges_subset
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0) :
    mapEdgeSet (remainingCompletionEmbedding (Flag := Flag) v)
        (S.deleteOutside v hv).completionEdges ⊆ S.completionEdges := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
  rw [State.completionEdges] at hf
  rcases Finset.mem_union.mp hf with hfLiveOrMissing | hfGhost
  · rcases Finset.mem_union.mp hfLiveOrMissing with hfLive | hfMissing
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hfLive
      change mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
          (liftLiveEdge (Flag := Flag) g) ∈ S.completionEdges
      rw [map_liftLiveEdge_remaining]
      apply S.liftedLiveEdges_subset_completionEdges
      rw [S.mem_liftedLiveEdges]
      exact (mem_deleteVertexEdges.mp
        ((mem_restrictedLiveEdges_iff S.edges v g).1 hg)).1
    · obtain ⟨t, _ht, hft⟩ := Finset.mem_image.mp hfMissing
      subst f
      change mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
          (liftLiveEdge (Flag := Flag)
            ((S.deleteOutside v hv).missing t)) ∈ S.completionEdges
      have hmissing : (S.deleteOutside v hv).missing t =
          restrictSimpleEdge v (S.missing t)
            (outside_not_mem_missing_vertices S v hv t) := rfl
      rw [hmissing, map_liftLiveEdge_remaining, map_restrictSimpleEdge]
      exact S.lifted_missing_mem_completionEdges t
  · obtain ⟨t, _ht, hft⟩ := Finset.mem_biUnion.mp hfGhost
    obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hft
    subst f
    change mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
        (ghostEdge t u) ∈ S.completionEdges
    rw [map_ghostEdge_remaining]
    exact S.ghostEdge_mem_completionEdges t
      ((mem_restrictVertexSet_iff v (S.terminals t)
        (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t) u).1 hu)

/-- Completion sparsity descends under deletion of an outside vertex. -/
theorem State.deleteOutside_completionSparse
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0)
    (hSparse : S.CompletionSparse) :
    (S.deleteOutside v hv).CompletionSparse := by
  exact sparse22_of_mapEdgeSet_subset
    (remainingCompletionEmbedding (Flag := Flag) v)
    hSparse (map_deleteOutside_completionEdges_subset S v hv)

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0019

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0019/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0019.json"

section BundleSource0020
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagInsertion.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagInsertion.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Inserting a certified live response edge into a flag state

When a virtual response row is available, the flag induction inserts its
underlying live edge.  The only compatibility condition is that the edge is
not the distinguished missing edge of any retained flag.  This file builds
the resulting `State` literally and identifies its completion with insertion
of the lifted edge into the old completion.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- Insert one live edge while retaining all active flag data. -/
def State.insertLiveEdge (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) : State V Flag where
  edges := insert e S.edges
  terminals := S.terminals
  missing := S.missing
  terminals_card := S.terminals_card
  missing_supported := S.missing_supported
  missing_not_live t := by
    simp [S.missing_not_live t, Ne.symm (heMissing t)]
  other_terminal_edges_live t f hfT hfMissing := by
    exact Finset.mem_insert_of_mem
      (S.other_terminal_edges_live t f hfT hfMissing)

@[simp]
theorem State.insertLiveEdge_edges
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    (S.insertLiveEdge e heMissing).edges = insert e S.edges := rfl

@[simp]
theorem State.insertLiveEdge_terminals
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) (t : Flag) :
    (S.insertLiveEdge e heMissing).terminals t = S.terminals t := rfl

@[simp]
theorem State.insertLiveEdge_missing
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) (t : Flag) :
    (S.insertLiveEdge e heMissing).missing t = S.missing t := rfl

/-- The literal completion changes by exactly the lifted inserted edge. -/
theorem State.completionEdges_insertLiveEdge
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    (S.insertLiveEdge e heMissing).completionEdges =
      insert (liftLiveEdge (Flag := Flag) e) S.completionEdges := by
  rw [State.completionEdges, State.completionEdges]
  have hLift :
      (S.insertLiveEdge e heMissing).liftedLiveEdges =
        insert (liftLiveEdge (Flag := Flag) e) S.liftedLiveEdges := by
    ext f
    simp [State.liftedLiveEdges, liftLiveEdgeEmbedding]
  have hMissing :
      (S.insertLiveEdge e heMissing).restoredMissingEdges =
        S.restoredMissingEdges := by
    rfl
  have hGhost :
      (S.insertLiveEdge e heMissing).ghostStarEdges =
        S.ghostStarEdges := by
    rfl
  rw [hLift, hMissing, hGhost]
  ext f
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

/-- A sparse certified insertion into the completion produces a sparse
child flag state. -/
theorem State.insertLiveEdge_completionSparse
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t)
    (hSparse : Sparse22
      (insert (liftLiveEdge (Flag := Flag) e) S.completionEdges)) :
    (S.insertLiveEdge e heMissing).CompletionSparse := by
  rw [State.CompletionSparse, S.completionEdges_insertLiveEdge]
  exact hSparse

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0020

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0020/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0020.json"

section BundleSource0021
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagPrivateDeletion.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagPrivateDeletion.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Deleting a private terminal and its unique provenance flag

If `v` belongs to exactly one active flag `t`, the private induction step
removes both the live vertex `v` and the ghost labelled by `t`.  This file
constructs the resulting state on the literal subtype vertex and flag types.
It also transports a certified virtual response-edge insertion to that
child.  All completion and sparsity assertions are proved about the actual
edge sets; no transition conclusion is stored in `State`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open Sparse22Transport

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The exact active-flag type after consuming `t`. -/
abbrev RemainingFlag (t : Flag) := {u : Flag // u ≠ t}

/-- Inclusion of the remaining flags into the parent flag type. -/
def remainingFlagEmbedding (t : Flag) : RemainingFlag t ↪ Flag :=
  Function.Embedding.subtype _

/-- Inclusion of the private child completion into the parent completion. -/
def remainingPrivateCompletionEmbedding (v : V) (t : Flag) :
    (RemainingVertex v ⊕ RemainingFlag t) ↪ (V ⊕ Flag) where
  toFun
    | Sum.inl u => Sum.inl u.1
    | Sum.inr r => Sum.inr r.1
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            change Sum.inl (x.1 : V) = Sum.inl (y.1 : V) at h
            exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
        | inr y => exact False.elim (Sum.inl_ne_inr h)
    | inr x =>
        cases y with
        | inl y => exact False.elim (Sum.inr_ne_inl h)
        | inr y =>
            change Sum.inr (x.1 : Flag) = Sum.inr (y.1 : Flag) at h
            exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

/-- A multiplicity-one vertex has no occurrence in any flag other than its
named unique flag. -/
theorem not_mem_other_terminals_of_flagMultiplicity_eq_one
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (u : Flag) (hut : u ≠ t) : v ∉ S.terminals u := by
  have ht : t ∈ S.activeFlagsAt v := (S.mem_activeFlagsAt v t).2 hvt
  have hCard : (S.activeFlagsAt v).card = 1 := hOne
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hCard
  have hrt : r = t := by
    rw [hr] at ht
    have htr : t = r := by simpa using ht
    exact htr.symm
  intro hvu
  have hu : u ∈ S.activeFlagsAt v := (S.mem_activeFlagsAt v u).2 hvu
  rw [hr, hrt] at hu
  exact hut (by simpa using hu)

/-- Every retained missing edge avoids the consumed private terminal. -/
theorem private_not_mem_retained_missing_vertices
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (u : RemainingFlag t) : v ∉ (S.missing u.1).vertices := by
  intro hve
  exact not_mem_other_terminals_of_flagMultiplicity_eq_one
    S v t hOne hvt u.1 u.2 (S.missing_supported u.1 hve)

/-- Delete the private live vertex and consume its unique flag. -/
def State.deletePrivate (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    State (RemainingVertex v) (RemainingFlag t) where
  edges := restrictedLiveEdges S.edges v
  terminals u := restrictVertexSet v (S.terminals u.1)
    (not_mem_other_terminals_of_flagMultiplicity_eq_one
      S v t hOne hvt u.1 u.2)
  missing u := restrictSimpleEdge v (S.missing u.1)
    (private_not_mem_retained_missing_vertices S v t hOne hvt u)
  terminals_card u := by
    rw [card_restrictVertexSet, S.terminals_card]
  missing_supported u := by
    intro x hx
    rw [mem_restrictVertexSet_iff]
    apply S.missing_supported u.1
    exact (mem_restrictSimpleEdge_vertices_iff _ _ _ x).1 hx
  missing_not_live u := by
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge]
    simp [S.missing_not_live u.1]
  other_terminal_edges_live u e heT heMissing := by
    rw [mem_restrictedLiveEdges_iff]
    refine mem_deleteVertexEdges.mpr ⟨?_, deleted_not_mem_mapped_vertices v e⟩
    apply S.other_terminal_edges_live u.1
    · have hsub := mapSimpleEdge_vertices_subset
          (remainingVertexEmbedding v) e
          (restrictVertexSet v (S.terminals u.1)
            (not_mem_other_terminals_of_flagMultiplicity_eq_one
              S v t hOne hvt u.1 u.2)) heT
      simpa [map_restrictVertexSet] using hsub
    · intro hEq
      apply heMissing
      apply mapSimpleEdge_injective (remainingVertexEmbedding v)
      rw [hEq, map_restrictSimpleEdge]

@[simp]
theorem deletePrivate_edges
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    (S.deletePrivate v t hOne hvt).edges = restrictedLiveEdges S.edges v := rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_liftLiveEdge_private
    (v : V) (t : Flag) (e : SimpleEdge (RemainingVertex v)) :
    mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
        (liftLiveEdge (Flag := RemainingFlag t) e) =
      liftLiveEdge (Flag := Flag)
        (mapSimpleEdge (remainingVertexEmbedding v) e) := by
  apply Subtype.ext
  simp only [mapSimpleEdge_val, liftLiveEdge_val, Sym2.map_map]
  induction e.1 using Sym2.inductionOn with
  | _ a b =>
      simp [remainingPrivateCompletionEmbedding, remainingVertexEmbedding]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_ghostEdge_private
    (v : V) (t : Flag) (u : RemainingFlag t) (x : RemainingVertex v) :
    mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
        (ghostEdge u x) = ghostEdge u.1 x.1 := by
  apply Subtype.ext
  change s(Sum.inr u.1, Sum.inl x.1) = s(Sum.inr u.1, Sum.inl x.1)
  rfl

/-- The completion of the private-deletion child embeds edge-for-edge in
the parent completion. -/
theorem State.map_deletePrivate_completionEdges_subset
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    mapEdgeSet (remainingPrivateCompletionEmbedding v t)
        (S.deletePrivate v t hOne hvt).completionEdges ⊆
      S.completionEdges := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
  rw [State.completionEdges] at hf
  rcases Finset.mem_union.mp hf with hfLiveOrMissing | hfGhost
  · rcases Finset.mem_union.mp hfLiveOrMissing with hfLive | hfMissing
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hfLive
      change mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
        (liftLiveEdge (Flag := RemainingFlag t) g) ∈ S.completionEdges
      rw [map_liftLiveEdge_private]
      apply S.liftedLiveEdges_subset_completionEdges
      rw [S.mem_liftedLiveEdges]
      exact (mem_deleteVertexEdges.mp
        ((mem_restrictedLiveEdges_iff S.edges v g).1 hg)).1
    · obtain ⟨u, _hu, hfu⟩ := Finset.mem_image.mp hfMissing
      subst f
      change mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
          (liftLiveEdge (Flag := RemainingFlag t)
            ((S.deletePrivate v t hOne hvt).missing u)) ∈ S.completionEdges
      have hmissing : (S.deletePrivate v t hOne hvt).missing u =
          restrictSimpleEdge v (S.missing u.1)
            (private_not_mem_retained_missing_vertices
              S v t hOne hvt u) := rfl
      rw [hmissing, map_liftLiveEdge_private, map_restrictSimpleEdge]
      exact S.lifted_missing_mem_completionEdges u.1
  · obtain ⟨u, _hu, hfStar⟩ := Finset.mem_biUnion.mp hfGhost
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hfStar
    subst f
    change mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
      (ghostEdge u x) ∈ S.completionEdges
    rw [map_ghostEdge_private]
    exact S.ghostEdge_mem_completionEdges u.1
      ((mem_restrictVertexSet_iff v (S.terminals u.1)
        (not_mem_other_terminals_of_flagMultiplicity_eq_one
          S v t hOne hvt u.1 u.2) x).1 hx)

/-- Completion sparsity descends after consuming a private terminal and its
unique flag. -/
theorem State.deletePrivate_completionSparse
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hSparse : S.CompletionSparse) :
    (S.deletePrivate v t hOne hvt).CompletionSparse := by
  exact sparse22_of_mapEdgeSet_subset
    (remainingPrivateCompletionEmbedding v t)
    hSparse (S.map_deletePrivate_completionEdges_subset v t hOne hvt)

/-! ## Transporting a certified response-edge insertion -/

/-- A mapped private-child completion edge avoids both deleted parent
vertices: the live terminal `v` and the consumed ghost `t`. -/
theorem deletedPrivate_not_mem_mappedCompletionEdge
    (v : V) (t : Flag) (e : SimpleEdge (RemainingVertex v ⊕ RemainingFlag t)) :
    Sum.inl v ∉ (mapSimpleEdge
        (remainingPrivateCompletionEmbedding v t) e).vertices ∧
      Sum.inr t ∉ (mapSimpleEdge
        (remainingPrivateCompletionEmbedding v t) e).vertices := by
  constructor
  · intro hvEdge
    have hsub := mapSimpleEdge_vertices_subset
      (remainingPrivateCompletionEmbedding v t) e
      (Finset.univ : Finset (RemainingVertex v ⊕ RemainingFlag t)) (by simp)
    obtain ⟨x, _hx, hxv⟩ := Finset.mem_map.mp (hsub hvEdge)
    cases x with
    | inl u => exact u.2 (Sum.inl.inj hxv)
    | inr r => exact Sum.inr_ne_inl hxv
  · intro htEdge
    have hsub := mapSimpleEdge_vertices_subset
      (remainingPrivateCompletionEmbedding v t) e
      (Finset.univ : Finset (RemainingVertex v ⊕ RemainingFlag t)) (by simp)
    obtain ⟨x, _hx, hxt⟩ := Finset.mem_map.mp (hsub htEdge)
    cases x with
    | inl u => exact Sum.inl_ne_inr hxt
    | inr r => exact r.2 (Sum.inr.inj hxt)

/-- The mapped private-child completion lies in the parent completion after
deleting the consumed ghost and live terminal. -/
theorem State.map_deletePrivate_completionEdges_subset_doubleDelete
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    mapEdgeSet (remainingPrivateCompletionEmbedding v t)
        (S.deletePrivate v t hOne hvt).completionEdges ⊆
      deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v) := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  have hAvoid := deletedPrivate_not_mem_mappedCompletionEdge v t g
  exact mem_deleteVertexEdges.mpr
    ⟨mem_deleteVertexEdges.mpr
      ⟨S.map_deletePrivate_completionEdges_subset v t hOne hvt
        (Finset.mem_map.mpr ⟨g, hg, rfl⟩), hAvoid.2⟩,
      hAvoid.1⟩

omit [Fintype V] [Fintype Flag] [DecidableEq Flag] in
/-- A restricted live response edge maps to its original lifted parent
edge even when the flag type is restricted simultaneously. -/
theorem map_lift_restrictSimpleEdge_private
    (v : V) (t : Flag) (e : SimpleEdge V) (hve : v ∉ e.vertices) :
    mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
        (liftLiveEdge (Flag := RemainingFlag t)
          (restrictSimpleEdge v e hve)) =
      liftLiveEdge (Flag := Flag) e := by
  rw [map_liftLiveEdge_private, map_restrictSimpleEdge]

/-- Insert a response edge whose addability has been certified in the
double-deleted parent completion.  The returned object is the literal
smaller flag state with a sparse completion. -/
theorem State.exists_insertedPrivateChild_of_addable
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hfAbsent : liftLiveEdge (Flag := Flag) f ∉ S.completionEdges)
    (hSparse : Sparse22
      (insert (liftLiveEdge (Flag := Flag) f)
        (deleteVertexEdges
          (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v)))) :
    ∃ heMissing : ∀ u : RemainingFlag t,
        restrictSimpleEdge v f hvf ≠
          (S.deletePrivate v t hOne hvt).missing u,
      ((S.deletePrivate v t hOne hvt).insertLiveEdge
        (restrictSimpleEdge v f hvf) heMissing).CompletionSparse := by
  have hfMissingParent : ∀ u : RemainingFlag t, f ≠ S.missing u.1 := by
    intro u hfu
    subst f
    exact hfAbsent (S.lifted_missing_mem_completionEdges u.1)
  have heMissing : ∀ u : RemainingFlag t,
      restrictSimpleEdge v f hvf ≠
        (S.deletePrivate v t hOne hvt).missing u := by
    intro u hEq
    apply hfMissingParent u
    have hmap := congrArg
      (mapSimpleEdge (remainingVertexEmbedding v)) hEq
    change mapSimpleEdge (remainingVertexEmbedding v)
        (restrictSimpleEdge v f hvf) =
      mapSimpleEdge (remainingVertexEmbedding v)
        (restrictSimpleEdge v (S.missing u.1)
          (private_not_mem_retained_missing_vertices
            S v t hOne hvt u)) at hmap
    simpa only [map_restrictSimpleEdge] using hmap
  refine ⟨heMissing, ?_⟩
  apply sparse22_of_mapEdgeSet_subset
    (remainingPrivateCompletionEmbedding v t) hSparse
  intro e he
  rw [(S.deletePrivate v t hOne hvt).completionEdges_insertLiveEdge] at he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  rw [Finset.mem_insert] at hg
  rcases hg with rfl | hgOld
  · change mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
      (liftLiveEdge (Flag := RemainingFlag t)
        (restrictSimpleEdge v f hvf)) ∈ _
    rw [map_lift_restrictSimpleEdge_private]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (S.map_deletePrivate_completionEdges_subset_doubleDelete
        v t hOne hvt (Finset.mem_map.mpr ⟨g, hgOld, rfl⟩))

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0021

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0021/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0021.json"

section BundleSource0022
/- Source: Papers/RigidityZheng_Linear_BlockKernelExact.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/BlockKernelExact.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# The kernel exact sequence for a two-by-two block map

This file isolates the linear-algebra mechanism used when a live vertex is
deleted from a direction matrix.  For maps

`A : X → Y`, `B : Z → Y`, and `C : Z → W`,

the block map sends `(x,z)` to `(A x + B z, C z)`.  Its kernel maps to the
kernel of the connecting map

`ker C → Y / range A`, `z ↦ [B z]`.

The resulting short exact sequence is proved literally, including the
surjectivity lift and the identification of its kernel with `ker A`.  No
dimension identity is stored as a hypothesis.
-/

namespace RB31E2E

namespace BlockKernelExact

noncomputable section

variable {k X Z Y W : Type*} [Field k]
  [AddCommGroup X] [Module k X]
  [AddCommGroup Z] [Module k Z]
  [AddCommGroup Y] [Module k Y]
  [AddCommGroup W] [Module k W]

/-- The lower-triangular block map `(x,z) ↦ (A x + B z, C z)`. -/
def blockMap (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    (X × Z) →ₗ[k] (Y × W) where
  toFun p := (A p.1 + B p.2, C p.2)
  map_add' p q := by
    apply Prod.ext
    · simp only [map_add, Prod.fst_add, Prod.snd_add]
      abel
    · simp
  map_smul' c p := by
    ext <;> simp

@[simp]
theorem blockMap_apply
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W)
    (p : X × Z) :
    blockMap A B C p = (A p.1 + B p.2, C p.2) := rfl

/-- The connecting map from the local kernel to the old-row cokernel. -/
def connectingMap (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    LinearMap.ker C →ₗ[k] (Y ⧸ LinearMap.range A) where
  toFun z := (LinearMap.range A).mkQ (B z.1)
  map_add' z z' := by simp
  map_smul' c z := by simp

@[simp]
theorem connectingMap_apply
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W)
    (z : LinearMap.ker C) :
    connectingMap A B C z = (LinearMap.range A).mkQ (B z.1) := rfl

/-- Project a block-kernel element to its local coordinate.  The block
equation says that its connecting class vanishes. -/
def kernelToConnecting
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    LinearMap.ker (blockMap A B C) →ₗ[k] LinearMap.ker (connectingMap A B C) where
  toFun p := by
    refine ⟨⟨p.1.2, ?_⟩, ?_⟩
    · have hp := LinearMap.mem_ker.mp p.2
      exact congrArg Prod.snd hp
    · rw [LinearMap.mem_ker]
      have hp := LinearMap.mem_ker.mp p.2
      have hfirst : A p.1.1 + B p.1.2 = 0 := congrArg Prod.fst hp
      change (LinearMap.range A).mkQ (B p.1.2) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨-p.1.1, ?_⟩
      rw [map_neg]
      exact neg_eq_of_add_eq_zero_right hfirst
  map_add' p q := by
    ext
    rfl
  map_smul' c p := by
    ext
    rfl

@[simp]
theorem kernelToConnecting_coe
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W)
    (p : LinearMap.ker (blockMap A B C)) :
    ((kernelToConnecting A B C p : LinearMap.ker C) : Z) = p.1.2 := rfl

/-- Every vanishing connecting class lifts to a block-kernel element. -/
theorem kernelToConnecting_surjective
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    Function.Surjective (kernelToConnecting A B C) := by
  intro z
  have hzq : (LinearMap.range A).mkQ (B z.1) = 0 := by
    exact LinearMap.mem_ker.mp z.2
  have hzrange : B z.1 ∈ LinearMap.range A :=
    (by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzq
      exact hzq)
  obtain ⟨x, hx⟩ := hzrange
  let p : X × Z := (-x, z.1)
  have hp : p ∈ LinearMap.ker (blockMap A B C) := by
    rw [LinearMap.mem_ker]
    apply Prod.ext
    · change A (-x) + B z.1 = 0
      rw [map_neg]
      rw [hx]
      simp
    · dsimp [p]
      exact LinearMap.mem_ker.mp z.1.2
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Insert an old-kernel vector as a block-kernel vector with zero local
coordinate. -/
def oldKernelToBlockKernel
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    LinearMap.ker A →ₗ[k] LinearMap.ker (blockMap A B C) where
  toFun x := by
    refine ⟨(x.1, 0), ?_⟩
    rw [LinearMap.mem_ker]
    ext <;> simp [LinearMap.mem_ker.mp x.2]
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

/-- The old kernel is linearly equivalent to the kernel of the projection
from block stresses to local connecting stresses. -/
def oldKernelEquivProjectionKernel
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    LinearMap.ker A ≃ₗ[k] LinearMap.ker (kernelToConnecting A B C) where
  toFun x := by
    refine ⟨oldKernelToBlockKernel A B C x, ?_⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  invFun p := by
    refine ⟨p.1.1.1, ?_⟩
    have hproj := LinearMap.mem_ker.mp p.2
    have hz : p.1.1.2 = 0 := by
      have hproj' : kernelToConnecting A B C p.1 = 0 := hproj
      exact congrArg
        (fun z : LinearMap.ker (connectingMap A B C) ↦
          ((z.1 : LinearMap.ker C).1 : Z)) hproj'
    have hblock := LinearMap.mem_ker.mp p.1.2
    have hfirst : A p.1.1.1 + B p.1.1.2 = 0 := congrArg Prod.fst hblock
    rw [hz] at hfirst
    simpa using hfirst
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hproj := LinearMap.mem_ker.mp p.2
      have hz : p.1.1.2 = 0 := by
        have hproj' : kernelToConnecting A B C p.1 = 0 := hproj
        exact congrArg
          (fun z : LinearMap.ker (connectingMap A B C) ↦
            ((z.1 : LinearMap.ker C).1 : Z)) hproj'
      exact hz.symm
  map_add' x y := by
    ext <;> simp [oldKernelToBlockKernel]
  map_smul' c x := by
    ext <;> simp [oldKernelToBlockKernel]

/-- Exact kernel dimension formula for the block map. -/
theorem finrank_blockKernel
    [FiniteDimensional k X] [FiniteDimensional k Z]
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    Module.finrank k (LinearMap.ker (blockMap A B C)) =
      Module.finrank k (LinearMap.ker A) +
        Module.finrank k (LinearMap.ker (connectingMap A B C)) := by
  have hRN := (kernelToConnecting A B C).finrank_range_add_finrank_ker
  have hsurj : LinearMap.range (kernelToConnecting A B C) = ⊤ :=
    LinearMap.range_eq_top.mpr (kernelToConnecting_surjective A B C)
  have hker : Module.finrank k (LinearMap.ker (kernelToConnecting A B C)) =
      Module.finrank k (LinearMap.ker A) :=
    (oldKernelEquivProjectionKernel A B C).finrank_eq.symm
  rw [hsurj, finrank_top, hker] at hRN
  omega

end

end BlockKernelExact

end RB31E2E


end
end BundleSource0022

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0022/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0022.json"

section BundleSource0023
/- Source: Papers/RigidityZheng_Linear_DirectionStressDeletion.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/DirectionStressDeletion.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Exact direction-stress decomposition under deletion of one vertex

For a live edge set `F` and a vertex `v`, the edge weights split into old
weights on `deleteVertexEdges F v` and local weights on `incidentEdges F v`.
Vertex loads split into the rows away from `v` and the three-coordinate row
at `v`.  After these two literal linear equivalences, the parent direction
equilibrium map is the lower-triangular block map of `BlockKernelExact`.

Consequently the parent stress dimension is the deleted stress dimension
plus the dimension of the genuine connecting kernel.  No rank identity or
exactness assertion is supplied as a hypothesis.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

/-- The exact type of live vertices different from the deleted vertex. -/
abbrev AwayFrom (v : V) := {u : V // u ≠ v}

/-! ## Splitting edge weights -/

/-- The parent edge type is the disjoint sum of deleted and incident edge
types. -/
def edgeDeletionEquiv (F : SimpleEdgeSet V) (v : V) :
    F ≃ (↑(deleteVertexEdges F v) ⊕ ↑(incidentEdges F v)) where
  toFun e :=
    if hev : v ∈ e.1.vertices then
      Sum.inr ⟨e.1, mem_incidentEdges.mpr ⟨e.2, hev⟩⟩
    else
      Sum.inl ⟨e.1, mem_deleteVertexEdges.mpr ⟨e.2, hev⟩⟩
  invFun e := match e with
    | Sum.inl f => ⟨f.1, (mem_deleteVertexEdges.mp f.2).1⟩
    | Sum.inr f => ⟨f.1, (mem_incidentEdges.mp f.2).1⟩
  left_inv e := by
    by_cases hev : v ∈ e.1.vertices
    · simp [hev]
    · simp [hev]
  right_inv e := by
    cases e with
    | inl f =>
        have hev : v ∉ f.1.vertices := (mem_deleteVertexEdges.mp f.2).2
        simp [hev]
    | inr f =>
        have hev : v ∈ f.1.vertices := (mem_incidentEdges.mp f.2).2
        simp [hev]

/-- Restrict a parent weight to the deleted and incident edge packets, with
the inverse extending the two packets over their literal partition of `F`. -/
def splitEdgeWeights (F : SimpleEdgeSet V) (v : V) :
    (F → k) ≃ₗ[k]
      ((deleteVertexEdges F v → k) × (incidentEdges F v → k)) where
  toFun weight :=
    (fun e ↦ weight ⟨e.1, (mem_deleteVertexEdges.mp e.2).1⟩,
      fun e ↦ weight ⟨e.1, (mem_incidentEdges.mp e.2).1⟩)
  invFun weight e :=
    if hev : v ∈ e.1.vertices then
      weight.2 ⟨e.1, mem_incidentEdges.mpr ⟨e.2, hev⟩⟩
    else
      weight.1 ⟨e.1, mem_deleteVertexEdges.mpr ⟨e.2, hev⟩⟩
  left_inv weight := by
    funext e
    by_cases hev : v ∈ e.1.vertices
    · simp [hev]
    · simp [hev]
  right_inv weight := by
    apply Prod.ext
    · funext e
      have hev : v ∉ e.1.vertices := (mem_deleteVertexEdges.mp e.2).2
      simp [hev]
    · funext e
      have hev : v ∈ e.1.vertices := (mem_incidentEdges.mp e.2).2
      simp [hev]
  map_add' _x _y := by
    apply Prod.ext <;> funext e <;> rfl
  map_smul' _c _x := by
    apply Prod.ext <;> funext e <;> rfl

/-! ## Splitting vertex loads -/

/-- Restrict a vertex load to the vertices away from `v`. -/
def restrictAway (v : V) :
    (V → Fin 3 → k) →ₗ[k] (AwayFrom v → Fin 3 → k) where
  toFun load u := load u.1
  map_add' _x _y := rfl
  map_smul' _c _x := rfl

/-- Evaluate a vertex load at the deleted vertex. -/
def loadAt (v : V) : (V → Fin 3 → k) →ₗ[k] (Fin 3 → k) where
  toFun load := load v
  map_add' _x _y := rfl
  map_smul' _c _x := rfl

/-- A load on all vertices is equivalent to its away-from-`v` rows and its
row at `v`. -/
def splitVertexLoads (v : V) :
    (V → Fin 3 → k) ≃ₗ[k]
      ((AwayFrom v → Fin 3 → k) × (Fin 3 → k)) where
  toFun load := (fun u ↦ load u.1, load v)
  invFun load u := if huv : u = v then load.2 else load.1 ⟨u, huv⟩
  left_inv load := by
    funext u
    by_cases huv : u = v
    · subst u
      simp
    · simp [huv]
  right_inv load := by
    apply Prod.ext
    · funext u
      simp [u.2]
    · simp
  map_add' _x _y := by
    apply Prod.ext <;> rfl
  map_smul' _c _x := by
    apply Prod.ext <;> rfl

/-! ## The three deletion blocks -/

/-- Equilibrium of the deleted edge packet, restricted to old vertex rows. -/
def oldEquilibrium
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    (deleteVertexEdges F v → k) →ₗ[k] (AwayFrom v → Fin 3 → k) :=
  (restrictAway v).comp (directionEquilibrium (deleteVertexEdges F v) a)

/-- Contribution of incident edge weights to old vertex rows. -/
def localToOldEquilibrium
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    (incidentEdges F v → k) →ₗ[k] (AwayFrom v → Fin 3 → k) :=
  (restrictAway v).comp (directionEquilibrium (incidentEdges F v) a)

/-- Equilibrium at the deleted vertex contributed by incident edge weights. -/
def localEquilibriumAt
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    (incidentEdges F v → k) →ₗ[k] (Fin 3 → k) :=
  (loadAt v).comp (directionEquilibrium (incidentEdges F v) a)

/-- The parent equilibrium after the literal domain and codomain splits. -/
def splitDirectionEquilibrium
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    ((deleteVertexEdges F v → k) × (incidentEdges F v → k)) →ₗ[k]
      ((AwayFrom v → Fin 3 → k) × (Fin 3 → k)) :=
  (splitVertexLoads v).toLinearMap.comp
    ((directionEquilibrium F a).comp (splitEdgeWeights F v).symm.toLinearMap)

omit [Fintype V] in
private theorem directionRow_deleted_vertex_eq_zero
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (e : deleteVertexEdges F v) :
    directionRow a e.1 v = 0 := by
  have hev : v ∉ e.1.vertices := (mem_deleteVertexEdges.mp e.2).2
  have hsourceMem : e.1.source ∈ e.1.vertices := by
    simp [SimpleEdge.vertices, ← e.1.source_target_mk, Sym2.toFinset_mk_eq]
  have htargetMem : e.1.target ∈ e.1.vertices := by
    simp [SimpleEdge.vertices, ← e.1.source_target_mk, Sym2.toFinset_mk_eq]
  apply directionRow_eq_zero_of_ne
  · intro h
    rw [h] at hsourceMem
    exact hev hsourceMem
  · intro h
    rw [h] at htargetMem
    exact hev htargetMem

omit [Fintype V] in
/-- Deleted edges contribute zero load at the deleted vertex. -/
@[simp]
theorem old_packet_equilibrium_at_deleted
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (weight : deleteVertexEdges F v → k) :
    directionEquilibrium (deleteVertexEdges F v) a weight v = 0 := by
  funext j
  simp only [directionEquilibrium_apply, directionEquilibriumCoordinate]
  apply Finset.sum_eq_zero
  intro e _he
  rw [directionRow_deleted_vertex_eq_zero F a v e]
  simp

omit [Fintype V] in
private theorem directionEquilibriumCoordinate_split
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v u : V) (j : Fin 3)
    (weight :
      (deleteVertexEdges F v → k) × (incidentEdges F v → k)) :
    directionEquilibriumCoordinate F a
        ((splitEdgeWeights F v).symm weight) u j =
      directionEquilibriumCoordinate (deleteVertexEdges F v) a weight.1 u j +
        directionEquilibriumCoordinate (incidentEdges F v) a weight.2 u j := by
  let g : (deleteVertexEdges F v → k) × (incidentEdges F v → k) := weight
  let summand : F → k := fun e ↦
    ((splitEdgeWeights F v).symm weight) e * directionRow a e.1 u j
  let splitSummand :
      (deleteVertexEdges F v ⊕ incidentEdges F v) → k
    | Sum.inl e => weight.1 e * directionRow a e.1 u j
    | Sum.inr e => weight.2 e * directionRow a e.1 u j
  have hReindex : (∑ e : F, summand e) =
      ∑ e : (deleteVertexEdges F v ⊕ incidentEdges F v), splitSummand e := by
    exact Fintype.sum_equiv (edgeDeletionEquiv F v)
      summand splitSummand (fun e ↦ by
        by_cases hev : v ∈ e.1.vertices
        · simp [summand, splitSummand, edgeDeletionEquiv, splitEdgeWeights, hev]
        · simp [summand, splitSummand, edgeDeletionEquiv, splitEdgeWeights, hev])
  change (∑ e : F, summand e) =
    (∑ e : deleteVertexEdges F v,
      weight.1 e * directionRow a e.1 u j) +
    ∑ e : incidentEdges F v,
      weight.2 e * directionRow a e.1 u j
  rw [hReindex]
  exact Fintype.sum_sum_type splitSummand

omit [Fintype V] in
/-- The transformed parent map is exactly the `A/B/C` block map. -/
theorem splitDirectionEquilibrium_eq_blockMap
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    splitDirectionEquilibrium F a v =
      BlockKernelExact.blockMap
        (oldEquilibrium F a v)
        (localToOldEquilibrium F a v)
        (localEquilibriumAt F a v) := by
  apply LinearMap.ext
  intro weight
  apply Prod.ext
  · funext u j
    exact directionEquilibriumCoordinate_split F a v u.1 j weight
  · funext j
    have hsplit := directionEquilibriumCoordinate_split F a v v j weight
    have hOldZero := congrFun
      (old_packet_equilibrium_at_deleted F a v weight.1) j
    change directionEquilibriumCoordinate (deleteVertexEdges F v) a
      weight.1 v j = 0 at hOldZero
    rw [hOldZero, zero_add] at hsplit
    exact hsplit

/-! ## Kernel identifications and the dimension formula -/

/-- Splitting edge weights identifies the parent stress kernel with the
kernel of the literal block map. -/
def parentStressEquivBlockKernel
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    DirectionStressSpace F a ≃ₗ[k]
      LinearMap.ker
        (BlockKernelExact.blockMap
          (oldEquilibrium F a v)
          (localToOldEquilibrium F a v)
          (localEquilibriumAt F a v)) where
  toFun weight := by
    refine ⟨splitEdgeWeights F v weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    have hParent := LinearMap.mem_ker.mp weight.2
    have hSplit :
        splitDirectionEquilibrium F a v (splitEdgeWeights F v weight.1) = 0 := by
      change splitVertexLoads v
        (directionEquilibrium F a
          ((splitEdgeWeights F v).symm (splitEdgeWeights F v weight.1))) = 0
      rw [(splitEdgeWeights F v).symm_apply_apply, hParent]
      simp
    calc
      BlockKernelExact.blockMap
          (oldEquilibrium F a v)
          (localToOldEquilibrium F a v)
          (localEquilibriumAt F a v)
          (splitEdgeWeights F v weight.1) =
          splitDirectionEquilibrium F a v (splitEdgeWeights F v weight.1) := by
        exact (congrArg
          (fun L ↦ L (splitEdgeWeights F v weight.1))
          (splitDirectionEquilibrium_eq_blockMap F a v)).symm
      _ = 0 := hSplit
  invFun weight := by
    refine ⟨(splitEdgeWeights F v).symm weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    have hblock := LinearMap.mem_ker.mp weight.2
    have hSplit : splitDirectionEquilibrium F a v weight.1 = 0 := by
      calc
        splitDirectionEquilibrium F a v weight.1 =
            BlockKernelExact.blockMap
              (oldEquilibrium F a v)
              (localToOldEquilibrium F a v)
              (localEquilibriumAt F a v) weight.1 := by
          exact congrArg (fun L ↦ L weight.1)
            (splitDirectionEquilibrium_eq_blockMap F a v)
        _ = 0 := hblock
    change splitVertexLoads v
      (directionEquilibrium F a ((splitEdgeWeights F v).symm weight.1)) = 0 at hSplit
    apply (splitVertexLoads v).injective
    simpa using hSplit
  left_inv weight := by
    apply Subtype.ext
    exact (splitEdgeWeights F v).symm_apply_apply weight.1
  right_inv weight := by
    apply Subtype.ext
    exact (splitEdgeWeights F v).apply_symm_apply weight.1
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- Restricting deleted-edge equilibrium to away-from-`v` rows loses no
kernel information, because its row at `v` is identically zero. -/
def oldKernelEquivDeletedStress
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    LinearMap.ker (oldEquilibrium F a v) ≃ₗ[k]
      DirectionStressSpace (deleteVertexEdges F v) a where
  toFun weight := by
    refine ⟨weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    funext u
    by_cases huv : u = v
    · subst u
      exact old_packet_equilibrium_at_deleted F a v weight.1
    · have hold := LinearMap.mem_ker.mp weight.2
      have hu := congrFun hold ⟨u, huv⟩
      change directionEquilibrium (deleteVertexEdges F v) a weight.1 u = 0 at hu
      exact hu
  invFun weight := by
    refine ⟨weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    funext u
    have h := LinearMap.mem_ker.mp weight.2
    exact congrFun h u.1
  left_inv weight := by
    apply Subtype.ext
    rfl
  right_inv weight := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' c x := by
    apply Subtype.ext
    rfl

/-- Exact deletion formula for direction stresses.  The second summand is
the kernel of the explicit local response in the old-row cokernel. -/
theorem directionStressDim_delete_add_connectingKernel
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    directionStressDim F a =
      directionStressDim (deleteVertexEdges F v) a +
        Module.finrank k
          (LinearMap.ker
            (BlockKernelExact.connectingMap
              (oldEquilibrium F a v)
              (localToOldEquilibrium F a v)
              (localEquilibriumAt F a v))) := by
  calc
    directionStressDim F a =
        Module.finrank k
          (LinearMap.ker
            (BlockKernelExact.blockMap
              (oldEquilibrium F a v)
              (localToOldEquilibrium F a v)
              (localEquilibriumAt F a v))) := by
      exact (parentStressEquivBlockKernel F a v).finrank_eq
    _ = Module.finrank k (LinearMap.ker (oldEquilibrium F a v)) +
          Module.finrank k
            (LinearMap.ker
              (BlockKernelExact.connectingMap
                (oldEquilibrium F a v)
                (localToOldEquilibrium F a v)
                (localEquilibriumAt F a v))) := by
      exact BlockKernelExact.finrank_blockKernel
        (oldEquilibrium F a v)
        (localToOldEquilibrium F a v)
        (localEquilibriumAt F a v)
    _ = directionStressDim (deleteVertexEdges F v) a +
          Module.finrank k
            (LinearMap.ker
              (BlockKernelExact.connectingMap
                (oldEquilibrium F a v)
                (localToOldEquilibrium F a v)
                (localEquilibriumAt F a v))) := by
      rw [(oldKernelEquivDeletedStress F a v).finrank_eq]
      rfl

end

end DirectionStress

end RB31E2E


end
end BundleSource0023

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0023/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0023.json"

section BundleSource0024
/- Source: Papers/RigidityZheng_Linear_DirectionResponse.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/DirectionResponse.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Direction-row spaces and the minimal local response calculus

The response of a deleted vertex is not stored in a record.  It is the
literal class of the local away-load in the cokernel of the old equilibrium
map.  This file identifies vanishing of that class with membership in the
span of the child direction rows.

It also proves the common augmentation fact used by both outside and
private-flag reductions: adjoining an absent edge whose direction row is
already in the old row space leaves row rank unchanged and increases stress
dimension by exactly one.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

/-! ## Literal row spaces -/

/-- The span of the actual labelled direction rows of `F`. -/
def directionRowSpace (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    Submodule k (V → Fin 3 → k) :=
  Submodule.span k (Set.range (fun e : F ↦ directionRow a e.1))

omit [Fintype V] in
/-- The literal row space is the range of equilibrium synthesis. -/
theorem directionRowSpace_eq_range
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionRowSpace F a = LinearMap.range (directionEquilibrium F a) := by
  exact (range_directionEquilibrium_eq_span_directionRows F a).symm

omit [Fintype V] in
/-- Row rank is the finite dimension of the literal row space. -/
theorem directionEquilibriumRank_eq_finrank_rowSpace
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionEquilibriumRank F a = Module.finrank k (directionRowSpace F a) := by
  rw [directionEquilibriumRank, ← directionRowSpace_eq_range]

/-- The child row space transported to the vertex rows away from `v`. -/
def deletedAwayRowSpace
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    Submodule k (AwayFrom v → Fin 3 → k) :=
  (directionRowSpace (deleteVertexEdges F v) a).map (restrictAway v)

omit [Fintype V] in
/-- The old block map has exactly the transported child row space as its
range. -/
theorem range_oldEquilibrium_eq_deletedAwayRowSpace
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    LinearMap.range (oldEquilibrium F a v) = deletedAwayRowSpace F a v := by
  ext load
  constructor
  · rintro ⟨weight, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨directionEquilibrium (deleteVertexEdges F v) a weight, ?_, rfl⟩
    rw [directionRowSpace_eq_range]
    exact ⟨weight, rfl⟩
  · intro hload
    obtain ⟨childLoad, hChildLoad, rfl⟩ := Submodule.mem_map.mp hload
    rw [directionRowSpace_eq_range] at hChildLoad
    obtain ⟨weight, rfl⟩ := hChildLoad
    exact ⟨weight, rfl⟩

/-! ## The local response class -/

/-- The actual child-load class of a locally equilibrated incident weight.
Its codomain is the old-row cokernel; this is precisely the connecting map
from the deletion exact sequence. -/
def deletedConnectingClass
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    LinearMap.ker (localEquilibriumAt F a v) →ₗ[k]
      ((AwayFrom v → Fin 3 → k) ⧸
        LinearMap.range (oldEquilibrium F a v)) :=
  BlockKernelExact.connectingMap
    (oldEquilibrium F a v)
    (localToOldEquilibrium F a v)
    (localEquilibriumAt F a v)

omit [Fintype V] in
@[simp]
theorem deletedConnectingClass_apply
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (z : LinearMap.ker (localEquilibriumAt F a v)) :
    deletedConnectingClass F a v z =
      (LinearMap.range (oldEquilibrium F a v)).mkQ
        (localToOldEquilibrium F a v z.1) :=
  rfl

omit [Fintype V] in
/-- Vanishing of the response class is exactly provenance-preserving
descent of the local away-load into the transported child row space. -/
theorem deletedConnectingClass_eq_zero_iff
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (z : LinearMap.ker (localEquilibriumAt F a v)) :
    deletedConnectingClass F a v z = 0 ↔
      localToOldEquilibrium F a v z.1 ∈ deletedAwayRowSpace F a v := by
  rw [deletedConnectingClass_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero,
    ← range_oldEquilibrium_eq_deletedAwayRowSpace]

omit [Fintype V] in
/-- Kernel membership form of the same response criterion. -/
theorem mem_ker_deletedConnectingClass_iff
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (z : LinearMap.ker (localEquilibriumAt F a v)) :
    z ∈ LinearMap.ker (deletedConnectingClass F a v) ↔
      localToOldEquilibrium F a v z.1 ∈ deletedAwayRowSpace F a v := by
  rw [LinearMap.mem_ker, deletedConnectingClass_eq_zero_iff]

/-! ## Adjoining a virtual response edge -/

omit [Fintype V] in
/-- Old direction rows remain in the row space after adjoining any edge. -/
theorem directionRowSpace_le_insert
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V) :
    directionRowSpace F a ≤ directionRowSpace (insert f F) a := by
  rw [directionRowSpace, directionRowSpace, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨e.1, Finset.mem_insert_of_mem e.2⟩, rfl⟩

omit [Fintype V] in
/-- If the adjoined row already belongs to the old row space, no new row
direction is created. -/
theorem directionRowSpace_insert_le_of_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V)
    (hrow : directionRow a f ∈ directionRowSpace F a) :
    directionRowSpace (insert f F) a ≤ directionRowSpace F a := by
  rw [directionRowSpace, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  by_cases hef : e.1 = f
  · simpa [hef] using hrow
  · apply Submodule.subset_span
    refine ⟨⟨e.1, ?_⟩, rfl⟩
    exact (Finset.mem_insert.mp e.2).resolve_left hef

omit [Fintype V] in
/-- Exact row-space invariance under adjoining a virtual response row. -/
theorem directionRowSpace_insert_eq_of_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V)
    (hrow : directionRow a f ∈ directionRowSpace F a) :
    directionRowSpace (insert f F) a = directionRowSpace F a := by
  apply le_antisymm
  · exact directionRowSpace_insert_le_of_mem F a f hrow
  · exact directionRowSpace_le_insert F a f

/-- Reusable augmentation theorem: an absent edge whose direction row is a
child response increases stress dimension by exactly one. -/
theorem directionStressDim_insert_eq_add_one_of_row_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V)
    (hf : f ∉ F) (hrow : directionRow a f ∈ directionRowSpace F a) :
    directionStressDim (insert f F) a = directionStressDim F a + 1 := by
  have hRank : directionEquilibriumRank (insert f F) a =
      directionEquilibriumRank F a := by
    rw [directionEquilibriumRank_eq_finrank_rowSpace,
      directionEquilibriumRank_eq_finrank_rowSpace,
      directionRowSpace_insert_eq_of_mem F a f hrow]
  have hParent := directionStressDim_add_directionEquilibriumRank
    (insert f F) a
  have hChild := directionStressDim_add_directionEquilibriumRank F a
  rw [Finset.card_insert_of_notMem hf, hRank] at hParent
  omega

/-- The same theorem phrased directly as the common virtual-response
certificate used by deletion branches. -/
theorem stress_augmentation_of_virtual_response
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V)
    (hf : f ∉ F)
    (hVirtualResponse : directionRow a f ∈ directionRowSpace F a) :
    directionStressDim (insert f F) a = directionStressDim F a + 1 :=
  directionStressDim_insert_eq_add_one_of_row_mem F a f hf hVirtualResponse

end

end DirectionStress

end RB31E2E


end
end BundleSource0024

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0024/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0024.json"

section BundleSource0025
/- Source: Papers/RigidityZheng_Algebra_CoordinateFieldTower.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/CoordinateFieldTower.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Splitting a finite coordinate-generated function field

Deleting a live vertex separates the generic coordinate functions into an
old family and a finite new family.  This file constructs the intermediate
field generated by the old coordinates and proves both parts of the exact
transcendence-degree ledger:

* the total field is generated over the old-coordinate field by the new
  coordinate family;
* the tower transcendence degrees add, and the extension degree is bounded
  by the number of new coordinate labels.

No geometric fibre-dimension theorem is used or assumed.
-/

namespace RB31E2E

namespace CoordinateFieldTower

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin

universe u v w x

variable {k : Type u} {K : Type v} {Old : Type w} {New : Type x}
  [Field k] [Field K] [Algebra k K]

/-- The intermediate field generated by the old coordinate family. -/
abbrev oldCoordinateField (old : Old → K) : IntermediateField k K :=
  IntermediateField.adjoin k (Set.range old)

/-- If old and new coordinate families together generate `K`, then the new
family generates `K` over the intermediate field generated by the old
family. -/
theorem adjoin_new_over_old_eq_top
    (old : Old → K) (new : New → K)
    (hgen : IntermediateField.adjoin k
      (Set.range old ∪ Set.range new) = ⊤) :
    IntermediateField.adjoin
      (oldCoordinateField (k := k) (K := K) old) (Set.range new) = ⊤ := by
  apply (IntermediateField.restrictScalars_eq_top_iff (K := k)).mp
  rw [IntermediateField.adjoin_adjoin_left]
  exact hgen

/-- The extension from the old-coordinate field to the full field has
transcendence degree at most the cardinality of the new labels. -/
theorem extension_trdeg_le_card
    [Fintype New]
    (old : Old → K) (new : New → K)
    (hgen : IntermediateField.adjoin k
      (Set.range old ∪ Set.range new) = ⊤) :
    Algebra.trdeg (oldCoordinateField (k := k) (K := K) old) K ≤
      (Fintype.card New : Cardinal) := by
  exact FiniteCoordinateTrdeg.trdeg_le_card_of_adjoin_range_eq_top
    (k := oldCoordinateField (k := k) (K := K) old) (K := K)
    new (adjoin_new_over_old_eq_top (k := k) old new hgen)

/-- Exact transcendence-degree tower for the old-coordinate intermediate
field. -/
theorem trdeg_old_add_extension
    (old : Old → K) :
    Algebra.trdeg k (oldCoordinateField (k := k) (K := K) old) +
        Algebra.trdeg (oldCoordinateField (k := k) (K := K) old) K =
      Algebra.trdeg k K := by
  exact trdeg_add_eq k
    (oldCoordinateField (k := k) (K := K) old)

/-- Packaged deletion ledger: the tower equality and the finite extension
bound are both derived from the literal coordinate-generation equation. -/
theorem trdeg_deletion_ledger
    [Fintype New]
    (old : Old → K) (new : New → K)
    (hgen : IntermediateField.adjoin k
      (Set.range old ∪ Set.range new) = ⊤) :
    Algebra.trdeg k (oldCoordinateField (k := k) (K := K) old) +
          Algebra.trdeg (oldCoordinateField (k := k) (K := K) old) K =
        Algebra.trdeg k K ∧
      Algebra.trdeg (oldCoordinateField (k := k) (K := K) old) K ≤
        (Fintype.card New : Cardinal) := by
  exact ⟨trdeg_old_add_extension (k := k) old,
    extension_trdeg_le_card (k := k) old new hgen⟩

end

end CoordinateFieldTower

end RB31E2E


end
end BundleSource0025

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0025/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0025.json"

section BundleSource0026
/- Source: Papers/RigidityZheng_Linear_OutsideLocalPayment.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/OutsideLocalPayment.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# The three-coordinate payment ledger for an outside deletion

Deleting one outside live vertex creates two actual local quantities:

* `u`, the finite dimension of the kernel of the direction-response
  connecting map;
* `d`, the transcendence degree of the full function field over the field
  generated by the retained coordinates.

The new point has exactly three coordinate functions, hence `d ≤ 3`.  In
the nonexceptional branch the response kernel has dimension at most the
remaining coordinate budget `3-d`; this transparent linear/function-field
gate gives the required payment `u+d ≤3`.  The exceptional alternative is
kept as the literal negation of this gate and is not stored in any graph or
branch structure.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {V : Type w}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V]

/-- The retained coordinate labels after deleting `v`. -/
abbrev RetainedCoordinate (v : V) := AwayFrom v × Fin 3

/-- The three coordinate labels of the deleted point. -/
abbrev DeletedCoordinate := Fin 3

/-- Retained live-coordinate family inside the ambient function field. -/
def retainedCoordinates (a : V → Fin 3 → K) (v : V) :
    RetainedCoordinate v → K :=
  fun c ↦ a c.1.1 c.2

/-- The three coordinate functions of the deleted point. -/
def deletedCoordinates (a : V → Fin 3 → K) (v : V) :
    DeletedCoordinate → K :=
  fun j ↦ a v j

/-- The intermediate function field generated by retained coordinates. -/
abbrev retainedCoordinateField (a : V → Fin 3 → K) (v : V) :
    IntermediateField k K :=
  CoordinateFieldTower.oldCoordinateField
    (k := k) (K := K) (retainedCoordinates a v)

/-- The actual transcendence-degree cost of adjoining the deleted point. -/
def outsideExtensionTrdeg (a : V → Fin 3 → K) (v : V) : Cardinal :=
  Algebra.trdeg (retainedCoordinateField (k := k) a v) K

/-- The actual local stress increment furnished by the deletion exact
sequence. -/
def outsideResponseKernelDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) : ℕ :=
  Module.finrank K
    (LinearMap.ker
      (deletedConnectingClass F a v))

/-- The local response dimension is exactly the second summand in the
kernel-exact deletion formula. -/
theorem directionStressDim_eq_delete_add_outsideResponseKernelDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    directionStressDim F a =
      directionStressDim (deleteVertexEdges F v) a +
        outsideResponseKernelDim F a v := by
  exact directionStressDim_delete_add_connectingKernel F a v

/-- Reindex all live coordinates as retained coordinates or one of the
three coordinates at `v`. -/
def liveCoordinateDeletionEquiv (v : V) :
    V × Fin 3 ≃ RetainedCoordinate v ⊕ DeletedCoordinate where
  toFun c := if hcv : c.1 = v then Sum.inr c.2 else Sum.inl (⟨c.1, hcv⟩, c.2)
  invFun c := match c with
    | Sum.inl c => (c.1.1, c.2)
    | Sum.inr j => (v, j)
  left_inv c := by
    by_cases hcv : c.1 = v
    · apply Prod.ext
      · simp [hcv]
      · simp [hcv]
    · simp [hcv]
  right_inv c := by
    cases c with
    | inl c => simp [c.1.2]
    | inr j => simp

omit [Fintype V] in
/-- Generation by all live coordinates is equivalent to generation by the
union of retained and deleted coordinate ranges. -/
theorem adjoin_retained_union_deleted_eq_top
    (a : V → Fin 3 → K) (v : V)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤) :
    IntermediateField.adjoin k
      (Set.range (retainedCoordinates a v) ∪
        Set.range (deletedCoordinates a v)) = ⊤ := by
  have hRange :
      Set.range (fun c : V × Fin 3 ↦ a c.1 c.2) =
        Set.range (retainedCoordinates a v) ∪
          Set.range (deletedCoordinates a v) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      by_cases hcv : c.1 = v
      · exact Or.inr ⟨c.2, by simp [hcv, deletedCoordinates]⟩
      · exact Or.inl ⟨(⟨c.1, hcv⟩, c.2), rfl⟩
    · rintro (hOld | hNew)
      · obtain ⟨c, rfl⟩ := hOld
        exact ⟨(c.1.1, c.2), rfl⟩
      · obtain ⟨j, rfl⟩ := hNew
        exact ⟨(v, j), rfl⟩
  rw [← hRange]
  exact hgen

omit [Fintype V] in
/-- The extension created by one deleted point has transcendence degree at
most three. -/
theorem outsideExtensionTrdeg_le_three
    (a : V → Fin 3 → K) (v : V)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤) :
    outsideExtensionTrdeg (k := k) a v ≤ 3 := by
  have hUnion := adjoin_retained_union_deleted_eq_top
    (k := k) a v hgen
  simpa [outsideExtensionTrdeg, retainedCoordinateField] using
    (CoordinateFieldTower.extension_trdeg_le_card
      (k := k) (K := K)
      (retainedCoordinates a v) (deletedCoordinates a v) hUnion)

omit [Fintype V] in
/-- The extension transcendence degree is finite; this legitimizes its
`Cardinal.toNat` use in the local numerical ledger. -/
theorem outsideExtensionTrdeg_lt_aleph0
    (a : V → Fin 3 → K) (v : V)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤) :
    outsideExtensionTrdeg (k := k) a v < Cardinal.aleph0 := by
  exact (outsideExtensionTrdeg_le_three (k := k) a v hgen).trans_lt
    Cardinal.natCast_lt_aleph0

/-- Transparent nonexceptional gate: the response-kernel dimension fits
inside the three-coordinate budget left after the extension transcendence
degree is paid. -/
def OutsideNonexceptional
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) : Prop :=
  outsideResponseKernelDim F a v +
      (outsideExtensionTrdeg (k := k) a v).toNat ≤ 3

/-- The exceptional branch is literally the failure of the local payment
gate, not a stored tag. -/
def OutsideExceptional
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) : Prop :=
  ¬ OutsideNonexceptional (k := k) F a v

omit [Fintype V] in
/-- The outside local payment in natural-number form. -/
theorem outside_local_payment_toNat
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (hNonexceptional : OutsideNonexceptional (k := k) F a v) :
    outsideResponseKernelDim F a v +
        (outsideExtensionTrdeg (k := k) a v).toNat ≤ 3 :=
  hNonexceptional

omit [Fintype V] in
/-- The desired cardinal-valued payment: local stress growth plus function-
field growth costs at most the three coordinates of the deleted point. -/
theorem outside_local_payment
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤)
    (hNonexceptional : OutsideNonexceptional (k := k) F a v) :
    (outsideResponseKernelDim F a v : Cardinal) +
        outsideExtensionTrdeg (k := k) a v ≤ 3 := by
  have hfinite := outsideExtensionTrdeg_lt_aleph0 (k := k) a v hgen
  rw [← Cardinal.cast_toNat_of_lt_aleph0 hfinite]
  exact_mod_cast hNonexceptional

omit [Fintype V] in
/-- Every local outside configuration is transparently split into the paid
branch and its exceptional complement. -/
theorem outside_nonexceptional_or_exceptional
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    OutsideNonexceptional (k := k) F a v ∨
      OutsideExceptional (k := k) F a v := by
  exact em _

omit [Fintype V] [DecidableEq V] in
/-- Coefficient-comparison gate for the genuinely maximal extension case:
if the three new coordinates generate the extension and its trdeg is at
least three, then those coordinates are algebraically independent over the
retained field. -/
theorem deletedCoordinates_algebraicIndependent_of_three_le_trdeg
    (a : V → Fin 3 → K) (v : V)
    (hgen : IntermediateField.adjoin k
      (Set.range (retainedCoordinates a v) ∪
        Set.range (deletedCoordinates a v)) = ⊤)
    (hThree : (3 : Cardinal) ≤ outsideExtensionTrdeg (k := k) a v) :
    AlgebraicIndependent (retainedCoordinateField (k := k) a v)
      (deletedCoordinates a v) := by
  apply FiniteCoordinateTrdeg.algebraicIndependent_of_card_le_trdeg_of_adjoin_range_eq_top
    (deletedCoordinates a v)
  · exact CoordinateFieldTower.adjoin_new_over_old_eq_top
      (k := k) (retainedCoordinates a v) (deletedCoordinates a v) hgen
  · simpa [outsideExtensionTrdeg] using hThree

end

end DirectionStress

end RB31E2E


end
end BundleSource0026

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0026/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0026.json"

section BundleSource0027
/- Source: Papers/RigidityZheng_Linear_OutsideLocalClassification.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/OutsideLocalClassification.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# The linear core of the outside local classification

For a vertex `v`, let `C_v` be the literal local equilibrium map on the
incident-edge packet.  This file proves the part of the outside-local lemma
which is pure finite-dimensional linear algebra:

* the response kernel is a subspace of `ker C_v`;
* rank--nullity for `C_v` is exactly the degree ledger;
* an injective placement makes `C_v` have positive rank whenever `v` has an
  incident edge;
* under degree at most three, failure of the three-coordinate payment has
  only two numerical shapes;
* if `rank C_v >= 2`, the only shape is
  `degree = 3`, extension cost `= 3`, response dimension `= 1`, and
  `dim ker C_v = 1`.

The retained-neighbour geometry then rules out the rank-one numerical
branch.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {V : Type w}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V]

/-- Nullity of the literal local equilibrium map `C_v`. -/
def outsideLocalKernelDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) : ℕ :=
  Module.finrank K (LinearMap.ker (localEquilibriumAt F a v))

/-- Rank of the literal local equilibrium map `C_v`. -/
def outsideLocalRank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) : ℕ :=
  Module.finrank K (LinearMap.range (localEquilibriumAt F a v))

/-- The response kernel is literally a submodule of `ker C_v`. -/
theorem outsideResponseKernelDim_le_outsideLocalKernelDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    outsideResponseKernelDim F a v ≤ outsideLocalKernelDim F a v := by
  simpa [outsideResponseKernelDim, outsideLocalKernelDim] using
    (LinearMap.ker (deletedConnectingClass F a v)).finrank_le

/-- Rank--nullity for `C_v`, with its domain cardinality identified with
the graph-theoretic degree of `v`. -/
theorem outsideLocalRank_add_kernelDim_eq_degree
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    outsideLocalRank F a v + outsideLocalKernelDim F a v =
      edgeSetDegree F v := by
  have hRankNullity :=
    (localEquilibriumAt F a v).finrank_range_add_finrank_ker
  have hDomain :
      Module.finrank K (incidentEdges F v → K) = edgeSetDegree F v := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    rfl
  simpa [outsideLocalRank, outsideLocalKernelDim, hDomain] using
    hRankNullity

omit [Fintype V] in
/-- A single incident-edge coefficient synthesizes its local direction
column at the deleted vertex. -/
@[simp]
theorem localEquilibriumAt_piSingle
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (e : incidentEdges F v) (c : K) :
    localEquilibriumAt F a v (Pi.single e c) =
      c • directionRow a e.1 v := by
  let weight : incidentEdges F v → K := Pi.single e c
  funext j
  change
    (∑ x ∈ (incidentEdges F v).attach,
      weight x * directionRow a x.1 v j) =
        c * directionRow a e.1 v j
  rw [Finset.sum_eq_single e]
  · simp [weight]
  · intro b _ hbe
    simp [weight, hbe]
  · intro he
    exact (he (Finset.mem_attach (incidentEdges F v) e)).elim

omit [Fintype V] [DecidableEq V] in
/-- Distinct placed endpoints give a nonzero oriented edge direction. -/
theorem edgeDirection_ne_zero_of_injective
    (a : V → Fin 3 → K) (ha : Function.Injective a)
    (e : SimpleEdge V) :
    edgeDirection a e ≠ 0 := by
  intro hzero
  apply e.source_ne_target
  apply ha
  funext j
  have hj := congrFun hzero j
  simpa [edgeDirection, sub_eq_zero] using hj

omit [Fintype V] in
/-- At either endpoint of an edge, the local direction row is nonzero for
an injective placement. -/
theorem directionRow_ne_zero_at_incident_of_injective
    (a : V → Fin 3 → K) (ha : Function.Injective a)
    (e : SimpleEdge V) (v : V) (hv : v ∈ e.vertices) :
    directionRow a e v ≠ 0 := by
  have hvEnds : v = e.source ∨ v = e.target := by
    simpa [SimpleEdge.vertices, ← e.source_target_mk,
      Sym2.toFinset_mk_eq] using hv
  rcases hvEnds with hvSource | hvTarget
  · subst v
    simpa using edgeDirection_ne_zero_of_injective a ha e
  · subst v
    simpa using neg_ne_zero.mpr (edgeDirection_ne_zero_of_injective a ha e)

/-- If `v` has an incident edge, then the local equilibrium map has positive
rank at every injective placement. -/
theorem outsideLocalRank_pos_of_injective_of_degree_pos
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a) (hDegree : 0 < edgeSetDegree F v) :
    0 < outsideLocalRank F a v := by
  have hIncident : (incidentEdges F v).Nonempty := by
    apply Finset.card_pos.mp
    simpa [edgeSetDegree] using hDegree
  obtain ⟨edge, hedge⟩ := hIncident
  let e : incidentEdges F v := ⟨edge, hedge⟩
  have hrow : directionRow a e.1 v ≠ 0 := by
    apply directionRow_ne_zero_at_incident_of_injective a ha
    exact (mem_incidentEdges.mp e.2).2
  have hrowRange :
      directionRow a e.1 v ∈ LinearMap.range (localEquilibriumAt F a v) := by
    refine ⟨Pi.single e 1, ?_⟩
    simpa only [one_smul] using localEquilibriumAt_piSingle F a v e 1
  have hSpan :
      K ∙ directionRow a e.1 v ≤
        LinearMap.range (localEquilibriumAt F a v) :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hrowRange
  have hDim : 1 ≤
      Module.finrank K (LinearMap.range (localEquilibriumAt F a v)) := by
    calc
      1 = Module.finrank K (K ∙ directionRow a e.1 v) :=
        (finrank_span_singleton hrow).symm
      _ ≤ Module.finrank K
          (LinearMap.range (localEquilibriumAt F a v)) :=
        Submodule.finrank_mono hSpan
  simpa only [outsideLocalRank] using (Nat.succ_le_iff.mp hDim)

/-- Pure numerical classification of a failed outside payment.  The first
branch has maximal coordinate-extension cost.  The only alternative has
extension cost two and a rank-one local equilibrium map on exactly three
incident edges. -/
theorem outsidePaymentFailure_linear_dichotomy
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a)
    (hDegree : edgeSetDegree F v ≤ 3)
    (d : ℕ) (hd : d ≤ 3)
    (hFailure : 3 < outsideResponseKernelDim F a v + d) :
    (d = 3 ∧ 1 ≤ outsideResponseKernelDim F a v) ∨
      (d = 2 ∧
        outsideResponseKernelDim F a v = 2 ∧
        outsideLocalKernelDim F a v = 2 ∧
        outsideLocalRank F a v = 1 ∧
        edgeSetDegree F v = 3) := by
  have hResponseKernel :=
    outsideResponseKernelDim_le_outsideLocalKernelDim F a v
  have hRankNullity := outsideLocalRank_add_kernelDim_eq_degree F a v
  have hResponsePos : 0 < outsideResponseKernelDim F a v := by omega
  have hDegreePos : 0 < edgeSetDegree F v := by omega
  have hRankPos :=
    outsideLocalRank_pos_of_injective_of_degree_pos F a v ha hDegreePos
  by_cases hdThree : d = 3
  · exact Or.inl ⟨hdThree, by omega⟩
  · right
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega

/-- Once the local equilibrium rank is at least two, failed payment has the
unique numerical shape needed by the outside-local lemma. -/
theorem outsidePaymentFailure_of_two_le_localRank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (hDegree : edgeSetDegree F v ≤ 3)
    (d : ℕ) (hd : d ≤ 3)
    (hRank : 2 ≤ outsideLocalRank F a v)
    (hFailure : 3 < outsideResponseKernelDim F a v + d) :
    d = 3 ∧
      outsideResponseKernelDim F a v = 1 ∧
      outsideLocalKernelDim F a v = 1 ∧
      outsideLocalRank F a v = 2 ∧
      edgeSetDegree F v = 3 := by
  have hResponseKernel :=
    outsideResponseKernelDim_le_outsideLocalKernelDim F a v
  have hRankNullity := outsideLocalRank_add_kernelDim_eq_degree F a v
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- The preceding dichotomy instantiated with the actual coordinate-field
extension.  Thus an actual exceptional outside deletion is already reduced
to the maximal-cost branch or the one explicit rank-one branch. -/
theorem outsideExceptional_linear_dichotomy
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a)
    (hDegree : edgeSetDegree F v ≤ 3)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤)
    (hExceptional : OutsideExceptional (k := k) F a v) :
    ((outsideExtensionTrdeg (k := k) a v).toNat = 3 ∧
      1 ≤ outsideResponseKernelDim F a v) ∨
      ((outsideExtensionTrdeg (k := k) a v).toNat = 2 ∧
        outsideResponseKernelDim F a v = 2 ∧
        outsideLocalKernelDim F a v = 2 ∧
        outsideLocalRank F a v = 1 ∧
        edgeSetDegree F v = 3) := by
  have hTrdegCard := outsideExtensionTrdeg_le_three (k := k) a v hgen
  have hTrdegNat : (outsideExtensionTrdeg (k := k) a v).toNat ≤ 3 := by
    simpa using Cardinal.toNat_le_toNat hTrdegCard
  have hFailure :
      3 < outsideResponseKernelDim F a v +
        (outsideExtensionTrdeg (k := k) a v).toNat := by
    unfold OutsideExceptional OutsideNonexceptional at hExceptional
    omega
  exact outsidePaymentFailure_linear_dichotomy F a v ha hDegree
    (outsideExtensionTrdeg (k := k) a v).toNat hTrdegNat hFailure

end

end DirectionStress

end RB31E2E


end
end BundleSource0027

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0027/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0027.json"

section BundleSource0028
/- Source: Papers/RigidityZheng_Linear_OutsideLocalGeometry.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/OutsideLocalGeometry.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Geometry and function-field cost of a low-degree outside star

This file supplies the geometric half of the outside-local classification.
The argument is carried out on the literal direction columns and the actual
retained-coordinate intermediate field:

* rank one puts the apex on a line through two retained neighbours, hence
  the coordinate extension has transcendence degree at most one;
* rank two with three noncollinear retained neighbours puts the apex in
  their affine plane, hence the extension has transcendence degree at most
  two.

Together with `OutsideLocalClassification`, these two field-generation
statements eliminate every failed-payment branch except the genuine
degree-three/full-fibre/collinear-neighbour branch.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V]

/-! ## Finite generators for a constrained point -/

omit [Fintype V] [DecidableEq V] in
/-- If the three coordinates of a point generate an extension and all lie
in a field generated by `r` parameters, its transcendence degree is at most
`r`. -/
theorem trdeg_le_card_of_coordinates_mem_parameter_adjoin
    {L : IntermediateField k K} {I : Type x} [Fintype I]
    (point : Fin 3 → K) (parameter : I → K)
    (hPointGen : IntermediateField.adjoin L (Set.range point) = ⊤)
    (hmem : ∀ j, point j ∈
      IntermediateField.adjoin L (Set.range parameter)) :
    Algebra.trdeg L K ≤ (Fintype.card I : Cardinal) := by
  have hParameterGen :
      IntermediateField.adjoin L (Set.range parameter) = ⊤ := by
    apply top_unique
    rw [← hPointGen]
    exact IntermediateField.adjoin_le_iff.mpr (by
      rintro _ ⟨j, rfl⟩
      exact hmem j)
  exact FiniteCoordinateTrdeg.trdeg_le_card_of_adjoin_range_eq_top
    parameter hParameterGen

omit [Fintype V] [DecidableEq V] in
/-- Every retained coordinate is an element of the literal retained
coordinate field. -/
theorem retained_coordinate_mem
    (a : V → Fin 3 → K) (v p : V) (hp : p ≠ v) (j : Fin 3) :
    a p j ∈ retainedCoordinateField (k := k) a v := by
  apply IntermediateField.subset_adjoin
  exact ⟨(⟨p, hp⟩, j), rfl⟩

omit [Fintype V] in
/-- If the apex lies on a line through two retained points, one scalar
parameter generates all three apex coordinates. -/
theorem outsideExtensionTrdeg_le_one_of_line_parameter
    (a : V → Fin 3 → K) (v p q : V)
    (hp : p ≠ v) (hq : q ≠ v)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤)
    (hline : ∃ s : K, a v = a p + s • (a q - a p)) :
    outsideExtensionTrdeg (k := k) a v ≤ 1 := by
  obtain ⟨s, hs⟩ := hline
  let L : IntermediateField k K := retainedCoordinateField (k := k) a v
  let parameter : Fin 1 → K := fun _ ↦ s
  have hPointGen :
      IntermediateField.adjoin L (Set.range (deletedCoordinates a v)) = ⊤ := by
    exact CoordinateFieldTower.adjoin_new_over_old_eq_top
      (k := k) (retainedCoordinates a v) (deletedCoordinates a v)
      (adjoin_retained_union_deleted_eq_top (k := k) a v hgen)
  have hmem : ∀ j, deletedCoordinates a v j ∈
      IntermediateField.adjoin L (Set.range parameter) := by
    intro j
    let M : IntermediateField L K :=
      IntermediateField.adjoin L (Set.range parameter)
    have hpM : a p j ∈ M := by
      exact IntermediateField.algebraMap_mem M
        (⟨a p j, retained_coordinate_mem (k := k) a v p hp j⟩ : L)
    have hqM : a q j ∈ M := by
      exact IntermediateField.algebraMap_mem M
        (⟨a q j, retained_coordinate_mem (k := k) a v q hq j⟩ : L)
    have hsM : s ∈ M := by
      apply IntermediateField.subset_adjoin
      exact ⟨0, rfl⟩
    have hj := congrFun hs j
    change a v j ∈ M
    rw [hj]
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      M.add_mem hpM (M.mul_mem hsM (M.sub_mem hqM hpM))
  simpa [outsideExtensionTrdeg, L] using
    (trdeg_le_card_of_coordinates_mem_parameter_adjoin
      (k := k) (L := L) (deletedCoordinates a v) parameter hPointGen hmem)

omit [Fintype V] in
/-- If the apex lies in the affine plane of three retained points, two
scalar parameters generate all three apex coordinates. -/
theorem outsideExtensionTrdeg_le_two_of_plane_parameters
    (a : V → Fin 3 → K) (v p q r : V)
    (hp : p ≠ v) (hq : q ≠ v) (hr : r ≠ v)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤)
    (hplane : ∃ s t : K,
      a v = a p + s • (a q - a p) + t • (a r - a p)) :
    outsideExtensionTrdeg (k := k) a v ≤ 2 := by
  obtain ⟨s, t, hst⟩ := hplane
  let L : IntermediateField k K := retainedCoordinateField (k := k) a v
  let parameter : Fin 2 → K := ![s, t]
  have hPointGen :
      IntermediateField.adjoin L (Set.range (deletedCoordinates a v)) = ⊤ := by
    exact CoordinateFieldTower.adjoin_new_over_old_eq_top
      (k := k) (retainedCoordinates a v) (deletedCoordinates a v)
      (adjoin_retained_union_deleted_eq_top (k := k) a v hgen)
  have hmem : ∀ j, deletedCoordinates a v j ∈
      IntermediateField.adjoin L (Set.range parameter) := by
    intro j
    let M : IntermediateField L K :=
      IntermediateField.adjoin L (Set.range parameter)
    have hpM : a p j ∈ M := by
      exact IntermediateField.algebraMap_mem M
        (⟨a p j, retained_coordinate_mem (k := k) a v p hp j⟩ : L)
    have hqM : a q j ∈ M := by
      exact IntermediateField.algebraMap_mem M
        (⟨a q j, retained_coordinate_mem (k := k) a v q hq j⟩ : L)
    have hrM : a r j ∈ M := by
      exact IntermediateField.algebraMap_mem M
        (⟨a r j, retained_coordinate_mem (k := k) a v r hr j⟩ : L)
    have hsM : s ∈ M := by
      apply IntermediateField.subset_adjoin
      exact ⟨0, rfl⟩
    have htM : t ∈ M := by
      apply IntermediateField.subset_adjoin
      exact ⟨1, rfl⟩
    have hj := congrFun hst j
    change a v j ∈ M
    rw [hj]
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      M.add_mem
        (M.add_mem hpM (M.mul_mem hsM (M.sub_mem hqM hpM)))
        (M.mul_mem htM (M.sub_mem hrM hpM))
  simpa [outsideExtensionTrdeg, L] using
    (trdeg_le_card_of_coordinates_mem_parameter_adjoin
      (k := k) (L := L) (deletedCoordinates a v) parameter hPointGen hmem)

/-! ## Literal direction columns at named neighbours -/

omit [Fintype V] in
/-- The direction row of the unordered edge `{v,p}`, evaluated at `v`, is
the orientation-free difference `a v - a p`. -/
theorem directionRow_simpleEdge_at_left
    (a : V → Fin 3 → K) (v p : V) (hvp : v ≠ p) :
    directionRow a (simpleEdge v p hvp) v = a v - a p := by
  let e : SimpleEdge V := simpleEdge v p hvp
  have hEnds :
      (e.source = v ∧ e.target = p) ∨
        (e.source = p ∧ e.target = v) := by
    have hPair : s(e.source, e.target) = s(v, p) := by
      rw [e.source_target_mk]
      rfl
    exact Sym2.eq_iff.mp hPair
  rcases hEnds with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · calc
      directionRow a e v = directionRow a e e.source := by rw [hsource]
      _ = edgeDirection a e := directionRow_source a e
      _ = a v - a p := by
        funext j
        simp [edgeDirection, hsource, htarget]
  · calc
      directionRow a e v = directionRow a e e.target := by rw [htarget]
      _ = -(edgeDirection a e) := directionRow_target a e
      _ = a v - a p := by
        funext j
        simp [edgeDirection, hsource, htarget]

omit [Fintype V] in
/-- Every named neighbour difference is a literal vector in the range of
the local equilibrium map. -/
theorem namedNeighbourDifference_mem_localRange
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v p : V)
    (hvp : v ≠ p) (hEdge : simpleEdge v p hvp ∈ F) :
    a v - a p ∈ LinearMap.range (localEquilibriumAt F a v) := by
  let e : incidentEdges F v :=
    ⟨simpleEdge v p hvp,
      mem_incidentEdges.mpr ⟨hEdge, by rw [vertices_simpleEdge]; simp⟩⟩
  refine ⟨Pi.single e 1, ?_⟩
  rw [localEquilibriumAt_piSingle, one_smul]
  exact directionRow_simpleEdge_at_left a v p hvp

/-- Explicit, pairwise-distinct neighbours exhausting a degree-three
incidence packet. -/
structure DegreeThreeNeighbours (F : SimpleEdgeSet V) (v : V) where
  p : V
  q : V
  r : V
  hvp : v ≠ p
  hvq : v ≠ q
  hvr : v ≠ r
  hpq : p ≠ q
  hpr : p ≠ r
  hqr : q ≠ r
  vp_mem : simpleEdge v p hvp ∈ F
  vq_mem : simpleEdge v q hvq ∈ F
  vr_mem : simpleEdge v r hvr ∈ F

/-- Two named distinct neighbours of one vertex. -/
structure TwoNeighbours (F : SimpleEdgeSet V) (v : V) where
  p : V
  q : V
  hvp : v ≠ p
  hvq : v ≠ q
  hpq : p ≠ q
  vp_mem : simpleEdge v p hvp ∈ F
  vq_mem : simpleEdge v q hvq ∈ F

omit [Fintype V] in
/-- A degree-three simple incidence set produces three actual, distinct
neighbours; this is only an enumeration theorem, not a stored geometric
classification. -/
theorem exists_degreeThreeNeighbours
    (F : SimpleEdgeSet V) (v : V) (hDegree : edgeSetDegree F v = 3) :
    Nonempty (DegreeThreeNeighbours F v) := by
  have hIncidentCard : (incidentEdges F v).card = 3 := hDegree
  obtain ⟨e₁, e₂, e₃, he₁₂, he₁₃, he₂₃, hIncidentEq⟩ :=
    Finset.card_eq_three.mp hIncidentCard
  have he₁ : e₁ ∈ incidentEdges F v := by rw [hIncidentEq]; simp
  have he₂ : e₂ ∈ incidentEdges F v := by rw [hIncidentEq]; simp
  have he₃ : e₃ ∈ incidentEdges F v := by rw [hIncidentEq]; simp
  obtain ⟨p, hvp, hpEdge⟩ :=
    exists_otherEndpoint e₁ (mem_incidentEdges.mp he₁).2
  obtain ⟨q, hvq, hqEdge⟩ :=
    exists_otherEndpoint e₂ (mem_incidentEdges.mp he₂).2
  obtain ⟨r, hvr, hrEdge⟩ :=
    exists_otherEndpoint e₃ (mem_incidentEdges.mp he₃).2
  have hpq : p ≠ q := by
    intro hpq
    subst q
    apply he₁₂
    calc
      e₁ = simpleEdge v p hvp := hpEdge
      _ = simpleEdge v p hvq := by rfl
      _ = e₂ := hqEdge.symm
  have hpr : p ≠ r := by
    intro hpr
    subst r
    apply he₁₃
    calc
      e₁ = simpleEdge v p hvp := hpEdge
      _ = simpleEdge v p hvr := by rfl
      _ = e₃ := hrEdge.symm
  have hqr : q ≠ r := by
    intro hqr
    subst r
    apply he₂₃
    calc
      e₂ = simpleEdge v q hvq := hqEdge
      _ = simpleEdge v q hvr := by rfl
      _ = e₃ := hrEdge.symm
  refine ⟨{
    p := p, q := q, r := r,
    hvp := hvp, hvq := hvq, hvr := hvr,
    hpq := hpq, hpr := hpr, hqr := hqr,
    vp_mem := ?_, vq_mem := ?_, vr_mem := ?_ }⟩
  · rw [← hpEdge]
    exact (mem_incidentEdges.mp he₁).1
  · rw [← hqEdge]
    exact (mem_incidentEdges.mp he₂).1
  · rw [← hrEdge]
    exact (mem_incidentEdges.mp he₃).1

omit [Fintype V] in
/-- Exactly two incident edges similarly give two actual distinct
neighbours. -/
theorem exists_degreeTwoNeighbours
    (F : SimpleEdgeSet V) (v : V) (hDegree : edgeSetDegree F v = 2) :
    Nonempty (TwoNeighbours F v) := by
  have hIncidentCard : (incidentEdges F v).card = 2 := hDegree
  obtain ⟨e₁, e₂, he₁₂, hIncidentEq⟩ :=
    Finset.card_eq_two.mp hIncidentCard
  have he₁ : e₁ ∈ incidentEdges F v := by rw [hIncidentEq]; simp
  have he₂ : e₂ ∈ incidentEdges F v := by rw [hIncidentEq]; simp
  obtain ⟨p, hvp, hpEdge⟩ :=
    exists_otherEndpoint e₁ (mem_incidentEdges.mp he₁).2
  obtain ⟨q, hvq, hqEdge⟩ :=
    exists_otherEndpoint e₂ (mem_incidentEdges.mp he₂).2
  have hpq : p ≠ q := by
    intro hpq
    subst q
    apply he₁₂
    calc
      e₁ = simpleEdge v p hvp := hpEdge
      _ = simpleEdge v p hvq := by rfl
      _ = e₂ := hqEdge.symm
  refine ⟨{
    p := p, q := q, hvp := hvp, hvq := hvq, hpq := hpq,
    vp_mem := ?_, vq_mem := ?_ }⟩
  · rw [← hpEdge]
    exact (mem_incidentEdges.mp he₁).1
  · rw [← hqEdge]
    exact (mem_incidentEdges.mp he₂).1

omit [Fintype V] in
/-- Forgetting the third neighbour retains a genuine two-neighbour packet. -/
def DegreeThreeNeighbours.toTwo
    {F : SimpleEdgeSet V} {v : V} (N : DegreeThreeNeighbours F v) :
    TwoNeighbours F v where
  p := N.p
  q := N.q
  hvp := N.hvp
  hvq := N.hvq
  hpq := N.hpq
  vp_mem := N.vp_mem
  vq_mem := N.vq_mem

/-! ## Rank one and rank two force affine parameterizations -/

omit [Fintype V] [DecidableEq V] in
/-- With two distinct first points, the provenance collinearity predicate is
equivalent to the third displacement being a scalar multiple of the first
displacement. -/
theorem collinear_iff_exists_smul_difference
    (p q r : Fin 3 → K) (hpq : p ≠ q) :
    PinCollinearity.Collinear p q r ↔
      ∃ t : K, r - p = t • (q - p) := by
  constructor
  · rintro ⟨d, c₁, c₂, h₁, h₂⟩
    have hDiff : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
    have hc₁ : c₁ ≠ 0 := by
      intro hc₁
      apply hDiff
      simpa [hc₁] using h₁
    refine ⟨c₂ * c₁⁻¹, ?_⟩
    rw [h₂, h₁, smul_smul]
    rw [mul_assoc, inv_mul_cancel₀ hc₁, mul_one]
  · rintro ⟨t, ht⟩
    exact ⟨q - p, 1, t, by simp, ht⟩

omit [Fintype V] [DecidableEq V] in
/-- If two apex differences lie in a vector space of dimension at most one,
then the apex lies on the affine line through their two distinct retained
endpoints. -/
theorem exists_line_parameter_of_finrank_le_one
    (point p q : Fin 3 → K) (S : Submodule K (Fin 3 → K))
    (hPointP : point ≠ p) (hPQ : p ≠ q)
    (hPointPMem : point - p ∈ S) (hPointQMem : point - q ∈ S)
    (hRank : Module.finrank K S ≤ 1) :
    ∃ t : K, point = p + t • (q - p) := by
  have hPointPDiff : point - p ≠ 0 := sub_ne_zero.mpr hPointP
  have hSpanLe : K ∙ (point - p) ≤ S :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hPointPMem
  have hSpanRank : Module.finrank K (K ∙ (point - p)) = 1 :=
    finrank_span_singleton hPointPDiff
  have hSRank : Module.finrank K S = 1 := by
    have hMono := Submodule.finrank_mono hSpanLe
    rw [hSpanRank] at hMono
    omega
  have hSpanEq : K ∙ (point - p) = S := by
    exact Submodule.eq_of_le_of_finrank_eq hSpanLe (by
      rw [hSpanRank, hSRank])
  have hPointQSpan : point - q ∈ K ∙ (point - p) := by
    rw [hSpanEq]
    exact hPointQMem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hPointQSpan
  have hOneSub : 1 - c ≠ 0 := by
    intro hzero
    have hcOne : c = 1 := (sub_eq_zero.mp hzero).symm
    apply hPQ
    have hSame : point - p = point - q := by simpa [hcOne] using hc
    funext j
    have hj := congrFun hSame j
    simp only [Pi.sub_apply] at hj
    exact sub_right_inj.mp hj
  have hDifference : q - p = (1 - c) • (point - p) := by
    calc
      q - p = (point - p) - (point - q) := by module
      _ = (point - p) - c • (point - p) := by rw [← hc]
      _ = (1 - c) • (point - p) := by module
  refine ⟨(1 - c)⁻¹, ?_⟩
  have hRecover : (1 - c)⁻¹ • (q - p) = point - p := by
    rw [hDifference, smul_smul]
    simp [hOneSub]
  rw [hRecover]
  module

omit [Fintype V] [DecidableEq V] in
/-- Noncollinearity of three points is linear independence of the two
displacements from the first point. -/
theorem linearIndependent_pair_differences_of_not_collinear
    (p q r : Fin 3 → K)
    (hNotCollinear : ¬ PinCollinearity.Collinear p q r) :
    LinearIndependent K ![q - p, r - p] := by
  have hPQ : p ≠ q := by
    intro hpq
    subst q
    apply hNotCollinear
    exact ⟨r - p, 0, 1, by simp, by simp⟩
  rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr (Ne.symm hPQ))]
  intro c hc
  apply hNotCollinear
  apply (collinear_iff_exists_smul_difference p q r hPQ).2
  exact ⟨c, hc.symm⟩

omit [Fintype V] [DecidableEq V] in
/-- If three apex differences lie in a vector space of dimension at most
two and the retained endpoints are noncollinear, the apex lies in their
affine plane. -/
theorem exists_plane_parameters_of_finrank_le_two
    (point p q r : Fin 3 → K) (S : Submodule K (Fin 3 → K))
    (hPointPMem : point - p ∈ S)
    (hPointQMem : point - q ∈ S)
    (hPointRMem : point - r ∈ S)
    (hRank : Module.finrank K S ≤ 2)
    (hNotCollinear : ¬ PinCollinearity.Collinear p q r) :
    ∃ s t : K,
      point = p + s • (q - p) + t • (r - p) := by
  let pair : Fin 2 → (Fin 3 → K) := ![q - p, r - p]
  let T : Submodule K (Fin 3 → K) :=
    Submodule.span K (Set.range pair)
  have hLI : LinearIndependent K pair := by
    exact linearIndependent_pair_differences_of_not_collinear
      p q r hNotCollinear
  have hTRank : Module.finrank K T = 2 := by
    change Module.finrank K (Submodule.span K (Set.range pair)) = 2
    rw [finrank_span_eq_card hLI]
    simp
  have hQP : q - p ∈ S := by
    have := S.sub_mem hPointPMem hPointQMem
    convert this using 1
    module
  have hRP : r - p ∈ S := by
    have := S.sub_mem hPointPMem hPointRMem
    convert this using 1
    module
  have hTLe : T ≤ S := by
    change Submodule.span K (Set.range pair) ≤ S
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hQP
    · exact hRP
  have hSRank : Module.finrank K S = 2 := by
    have hMono := Submodule.finrank_mono hTLe
    rw [hTRank] at hMono
    omega
  have hTEq : T = S := by
    exact Submodule.eq_of_le_of_finrank_eq hTLe (by rw [hTRank, hSRank])
  have hPointPInT : point - p ∈ T := by
    rw [hTEq]
    exact hPointPMem
  obtain ⟨coefficient : Fin 2 → K, hCoefficient⟩ :=
    (Submodule.mem_span_range_iff_exists_fun K).mp hPointPInT
  refine ⟨coefficient 0, coefficient 1, ?_⟩
  have hExpanded : point - p =
      coefficient 0 • (q - p) + coefficient 1 • (r - p) := by
    simpa [pair, Fin.sum_univ_two] using hCoefficient.symm
  funext j
  have hj := congrFun hExpanded j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
  linear_combination hj

/-! ## Applying the affine parameterizations to the actual local map -/

omit [Fintype V] in
/-- Rank one for an actual degree-two-or-three outside star forces the
deleted point into a one-parameter retained affine line. -/
theorem outsideExtensionTrdeg_le_one_of_localRank_eq_one
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a)
    (hDegreeLower : 2 ≤ edgeSetDegree F v)
    (hDegreeUpper : edgeSetDegree F v ≤ 3)
    (hRank : outsideLocalRank F a v = 1)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤) :
    outsideExtensionTrdeg (k := k) a v ≤ 1 := by
  have hDegreeCases : edgeSetDegree F v = 2 ∨ edgeSetDegree F v = 3 := by
    omega
  have hTwoNeighbours : Nonempty (TwoNeighbours F v) := by
    rcases hDegreeCases with hTwo | hThree
    · exact exists_degreeTwoNeighbours F v hTwo
    · exact ⟨(Classical.choice
        (exists_degreeThreeNeighbours F v hThree)).toTwo⟩
  let N : TwoNeighbours F v := Classical.choice hTwoNeighbours
  have hPointP : a v ≠ a N.p := by
    intro h
    exact N.hvp (ha h)
  have hPQ : a N.p ≠ a N.q := by
    intro h
    exact N.hpq (ha h)
  have hPointPMem :
      a v - a N.p ∈ LinearMap.range (localEquilibriumAt F a v) :=
    namedNeighbourDifference_mem_localRange F a v N.p N.hvp N.vp_mem
  have hPointQMem :
      a v - a N.q ∈ LinearMap.range (localEquilibriumAt F a v) :=
    namedNeighbourDifference_mem_localRange F a v N.q N.hvq N.vq_mem
  have hline : ∃ t : K,
      a v = a N.p + t • (a N.q - a N.p) := by
    apply exists_line_parameter_of_finrank_le_one
      (a v) (a N.p) (a N.q)
      (LinearMap.range (localEquilibriumAt F a v))
      hPointP hPQ hPointPMem hPointQMem
    change outsideLocalRank F a v ≤ 1
    omega
  exact outsideExtensionTrdeg_le_one_of_line_parameter
    (k := k) a v N.p N.q N.hvp.symm N.hvq.symm hgen hline

omit [Fintype V] in
/-- Rank at most two together with three noncollinear actual neighbours
forces the deleted point into their two-parameter retained affine plane. -/
theorem outsideExtensionTrdeg_le_two_of_localRank_of_not_collinear
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (N : DegreeThreeNeighbours F v)
    (hRank : outsideLocalRank F a v ≤ 2)
    (hNotCollinear :
      ¬ PinCollinearity.Collinear (a N.p) (a N.q) (a N.r))
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤) :
    outsideExtensionTrdeg (k := k) a v ≤ 2 := by
  have hPointPMem :
      a v - a N.p ∈ LinearMap.range (localEquilibriumAt F a v) :=
    namedNeighbourDifference_mem_localRange F a v N.p N.hvp N.vp_mem
  have hPointQMem :
      a v - a N.q ∈ LinearMap.range (localEquilibriumAt F a v) :=
    namedNeighbourDifference_mem_localRange F a v N.q N.hvq N.vq_mem
  have hPointRMem :
      a v - a N.r ∈ LinearMap.range (localEquilibriumAt F a v) :=
    namedNeighbourDifference_mem_localRange F a v N.r N.hvr N.vr_mem
  have hplane : ∃ s t : K,
      a v = a N.p + s • (a N.q - a N.p) +
        t • (a N.r - a N.p) := by
    apply exists_plane_parameters_of_finrank_le_two
      (a v) (a N.p) (a N.q) (a N.r)
      (LinearMap.range (localEquilibriumAt F a v))
      hPointPMem hPointQMem hPointRMem
    · simpa [outsideLocalRank] using hRank
    · exact hNotCollinear
  exact outsideExtensionTrdeg_le_two_of_plane_parameters
    (k := k) a v N.p N.q N.r
    N.hvp.symm N.hvq.symm N.hvr.symm hgen hplane

/-- **Outside-local classification.**  If a degree-at-most-three deletion
fails the three-coordinate payment at an injective, coordinate-generating
function-field point, then every part of the unique bad shape is forced by
the actual maps and fields:

* the degree is three;
* the three retained neighbours are pairwise distinct and collinear;
* the extension transcendence degree is exactly three;
* both `ker C_v` and the connecting kernel have dimension one;
* consequently the entire one-dimensional local relation space descends
  through the child row-space quotient.
-/
theorem outsideExceptional_classification
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a)
    (hDegree : edgeSetDegree F v ≤ 3)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤)
    (hExceptional : OutsideExceptional (k := k) F a v) :
    ∃ N : DegreeThreeNeighbours F v,
      PinCollinearity.Collinear (a N.p) (a N.q) (a N.r) ∧
      a N.p ≠ a N.q ∧ a N.p ≠ a N.r ∧ a N.q ≠ a N.r ∧
      outsideExtensionTrdeg (k := k) a v = 3 ∧
      outsideResponseKernelDim F a v = 1 ∧
      outsideLocalKernelDim F a v = 1 ∧
      outsideLocalRank F a v = 2 ∧
      deletedConnectingClass F a v = 0 := by
  let d : ℕ := (outsideExtensionTrdeg (k := k) a v).toNat
  have hTrdegCard := outsideExtensionTrdeg_le_three (k := k) a v hgen
  have hd : d ≤ 3 := by
    simpa [d] using Cardinal.toNat_le_toNat hTrdegCard
  have hFailure : 3 < outsideResponseKernelDim F a v + d := by
    unfold OutsideExceptional OutsideNonexceptional at hExceptional
    simpa [d] using (show
      3 < outsideResponseKernelDim F a v +
        (outsideExtensionTrdeg (k := k) a v).toNat by omega)
  have hResponseLe :=
    outsideResponseKernelDim_le_outsideLocalKernelDim F a v
  have hRankNullity := outsideLocalRank_add_kernelDim_eq_degree F a v
  have hResponsePos : 0 < outsideResponseKernelDim F a v := by omega
  have hDegreePos : 0 < edgeSetDegree F v := by omega
  have hRankPos :=
    outsideLocalRank_pos_of_injective_of_degree_pos F a v ha hDegreePos
  have hRankTwo : 2 ≤ outsideLocalRank F a v := by
    by_contra hNotTwo
    have hRankOne : outsideLocalRank F a v = 1 := by omega
    have hDegreeLower : 2 ≤ edgeSetDegree F v := by omega
    have hTrdegLeOne :=
      outsideExtensionTrdeg_le_one_of_localRank_eq_one
        (k := k) F a v ha hDegreeLower hDegree hRankOne hgen
    have hdOne : d ≤ 1 := by
      simpa [d] using Cardinal.toNat_le_toNat hTrdegLeOne
    omega
  obtain ⟨hdThree, hResponseOne, hKernelOne, hRankEqTwo,
      hDegreeThree⟩ :=
    outsidePaymentFailure_of_two_le_localRank F a v hDegree d hd
      hRankTwo hFailure
  let N : DegreeThreeNeighbours F v :=
    Classical.choice (exists_degreeThreeNeighbours F v hDegreeThree)
  have hCollinear :
      PinCollinearity.Collinear (a N.p) (a N.q) (a N.r) := by
    by_contra hNotCollinear
    have hTrdegLeTwo :=
      outsideExtensionTrdeg_le_two_of_localRank_of_not_collinear
        (k := k) F a v N (by omega) hNotCollinear hgen
    have hdTwo : d ≤ 2 := by
      simpa [d] using Cardinal.toNat_le_toNat hTrdegLeTwo
    omega
  have hTrdegFinite := outsideExtensionTrdeg_lt_aleph0 (k := k) a v hgen
  have hTrdegThree : outsideExtensionTrdeg (k := k) a v = 3 := by
    calc
      outsideExtensionTrdeg (k := k) a v =
          ((outsideExtensionTrdeg (k := k) a v).toNat : Cardinal) :=
        (Cardinal.cast_toNat_of_lt_aleph0 hTrdegFinite).symm
      _ = 3 := by
        change (d : Cardinal) = 3
        exact_mod_cast hdThree
  have hConnectingZero : deletedConnectingClass F a v = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_top]
    change outsideResponseKernelDim F a v = outsideLocalKernelDim F a v
    rw [hResponseOne, hKernelOne]
  refine ⟨N, hCollinear, ?_, ?_, ?_, hTrdegThree,
    hResponseOne, hKernelOne, hRankEqTwo, hConnectingZero⟩
  · exact fun h ↦ N.hpq (ha h)
  · exact fun h ↦ N.hpr (ha h)
  · exact fun h ↦ N.hqr (ha h)

end

end DirectionStress

end RB31E2E


end
end BundleSource0028

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0028/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0028.json"

section BundleSource0029
/- Source: Papers/RigidityZheng_Linear_PrivateLocalClassification.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/PrivateLocalClassification.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# The private-flag local classification

This file proves the one-dimensional analogue of the outside local
classification used at a terminal belonging to one provenance flag.  The
input is the literal pivoted shape: the flag line contains `v,p,q`, the
edge `vp` is live, the edge `vq` is missing, and the live degree of `v` is
at most two.

The exceptional alternative is not a tag stored in a graph or branch.  It
is exactly the failure of the transparent one-coordinate payment

`response-kernel dimension + coordinate-extension trdeg <= 1`.

From the actual local equilibrium map and the actual retained-coordinate
field we prove that failure has one shape only: degree two, a unique second
neighbour `z`, four distinct labels `v,p,q,z` on the same line, extension
trdeg one, local and response kernels both one-dimensional, and zero
connecting class.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {V : Type w}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V]

/-! ## The literal one-coordinate payment -/

/-- The response kernel fits in the coordinate budget left by the
one-dimensional flag-line fibre. -/
def PrivateNonexceptional
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v : V) : Prop :=
  outsideResponseKernelDim F pos v +
      (outsideExtensionTrdeg (k := k) pos v).toNat ≤ 1

/-- The private exceptional branch is exactly the negation of the local
payment, not an extra hypothesis carried by the state. -/
def PrivateExceptional
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v : V) : Prop :=
  ¬ PrivateNonexceptional (k := k) F pos v

omit [Fintype V] in
theorem private_nonexceptional_or_exceptional
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v : V) :
    PrivateNonexceptional (k := k) F pos v ∨
      PrivateExceptional (k := k) F pos v := by
  exact em _

omit [Fintype V] in
/-- Cardinal-valued form of the private one-coordinate payment. -/
theorem private_local_payment
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v : V)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤)
    (hNonexceptional : PrivateNonexceptional (k := k) F pos v) :
    (outsideResponseKernelDim F pos v : Cardinal) +
        outsideExtensionTrdeg (k := k) pos v ≤ 1 := by
  have hfinite := outsideExtensionTrdeg_lt_aleph0 (k := k) pos v hgen
  rw [← Cardinal.cast_toNat_of_lt_aleph0 hfinite]
  exact_mod_cast hNonexceptional

/-! ## Elementary collinearity conversions -/

omit [Fintype V] [DecidableEq V] in
/-- Cyclically permuting three affinely collinear points preserves the
literal witness predicate. -/
theorem collinear_cycle
    (x y z : Fin 3 → K)
    (h : PinCollinearity.Collinear x y z) :
    PinCollinearity.Collinear y z x := by
  obtain ⟨d, c₁, c₂, h₁, h₂⟩ := h
  refine ⟨d, c₂ - c₁, -c₁, ?_, ?_⟩
  · calc
      z - y = (z - x) - (y - x) := by module
      _ = c₂ • d - c₁ • d := by rw [h₁, h₂]
      _ = (c₂ - c₁) • d := by module
  · calc
      x - y = -(y - x) := by module
      _ = -(c₁ • d) := by rw [h₁]
      _ = (-c₁) • d := by module

omit [Fintype V] [DecidableEq V] in
/-- A point written on the affine line through two endpoints gives the
collinearity orientation needed by the private star. -/
theorem collinear_of_point_eq_line
    (point p q : Fin 3 → K) (s : K)
    (hpoint : point = p + s • (q - p)) :
    PinCollinearity.Collinear point p q := by
  refine ⟨q - p, -s, 1 - s, ?_, ?_⟩
  · rw [hpoint]
    module
  · rw [hpoint]
    module

omit [Fintype V] [DecidableEq V] in
/-- Collinearity supplied by the provenance branch on a finite terminal
set implies the three-point predicate used by the direction calculus. -/
theorem pinCollinear_of_affinelyCollinearOn
    (pos : V → Fin 3 → K) (X : Finset V) (x y z : V)
    (h : ProvenanceFlag.AffinelyCollinearOn pos X)
    (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X) :
    PinCollinearity.Collinear (pos x) (pos y) (pos z) := by
  obtain ⟨origin, direction, hall⟩ := h
  obtain ⟨cₓ, hxEq⟩ := hall x hx
  obtain ⟨cᵧ, hyEq⟩ := hall y hy
  obtain ⟨c_z, hzEq⟩ := hall z hz
  refine ⟨direction, cᵧ - cₓ, c_z - cₓ, ?_, ?_⟩
  · rw [hxEq, hyEq]
    module
  · rw [hxEq, hzEq]
    module

omit [Fintype V] in
/-- The pivoted private flag line makes the deleted point a one-parameter
extension of the retained coordinate field. -/
theorem privateExtensionTrdeg_le_one_of_collinear
    (pos : V → Fin 3 → K) (v p q : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos v) (pos p) (pos q))
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤) :
    outsideExtensionTrdeg (k := k) pos v ≤ 1 := by
  have hpqPos : pos p ≠ pos q := by
    intro h
    exact hpq (hpos h)
  have hpqv : PinCollinearity.Collinear (pos p) (pos q) (pos v) :=
    collinear_cycle (pos v) (pos p) (pos q) hcol
  obtain ⟨s, hs⟩ :=
    (collinear_iff_exists_smul_difference
      (pos p) (pos q) (pos v) hpqPos).1 hpqv
  have hline : ∃ s : K, pos v = pos p + s • (pos q - pos p) := by
    refine ⟨s, ?_⟩
    funext j
    have hj := congrFun hs j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linear_combination hj
  exact outsideExtensionTrdeg_le_one_of_line_parameter
    (k := k) pos v p q hvp.symm hvq.symm hgen hline

/-! ## A fixed first neighbour and the actual second neighbour -/

/-- The genuine second neighbour of a degree-two private vertex, with the
first neighbour fixed by the pivoted flag edge. -/
structure PrivateSecondNeighbour
    (F : SimpleEdgeSet V) (v p : V) where
  z : V
  hvz : v ≠ z
  hpz : p ≠ z
  vz_mem : simpleEdge v z hvz ∈ F

omit [Fintype V] in
/-- A named live edge `vp` and degree exactly two produce a unique other
edge with an endpoint `z ≠ v,p`.  This is a derived enumeration fact. -/
theorem exists_privateSecondNeighbour
    (F : SimpleEdgeSet V) (v p : V) (hvp : v ≠ p)
    (hvpMem : simpleEdge v p hvp ∈ F)
    (hDegree : edgeSetDegree F v = 2) :
    Nonempty (PrivateSecondNeighbour F v p) := by
  have hIncidentCard : (incidentEdges F v).card = 2 := hDegree
  obtain ⟨e₁, e₂, he₁₂, hIncidentEq⟩ :=
    Finset.card_eq_two.mp hIncidentCard
  have hvpIncident : simpleEdge v p hvp ∈ incidentEdges F v := by
    exact mem_incidentEdges.mpr ⟨hvpMem, by rw [vertices_simpleEdge]; simp⟩
  have hvpCases : simpleEdge v p hvp = e₁ ∨ simpleEdge v p hvp = e₂ := by
    rw [hIncidentEq] at hvpIncident
    simpa using hvpIncident
  have he₁Incident : e₁ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  have he₂Incident : e₂ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  rcases hvpCases with hvpEq | hvpEq
  · obtain ⟨z, hvz, he₂Eq⟩ :=
      exists_otherEndpoint e₂ (mem_incidentEdges.mp he₂Incident).2
    have hpz : p ≠ z := by
      intro hpz
      subst z
      apply he₁₂
      calc
        e₁ = simpleEdge v p hvp := hvpEq.symm
        _ = simpleEdge v p hvz := by rfl
        _ = e₂ := he₂Eq.symm
    refine ⟨⟨z, hvz, hpz, ?_⟩⟩
    rw [← he₂Eq]
    exact (mem_incidentEdges.mp he₂Incident).1
  · obtain ⟨z, hvz, he₁Eq⟩ :=
      exists_otherEndpoint e₁ (mem_incidentEdges.mp he₁Incident).2
    have hpz : p ≠ z := by
      intro hpz
      subst z
      apply he₁₂
      calc
        e₁ = simpleEdge v p hvz := he₁Eq
        _ = simpleEdge v p hvp := by rfl
        _ = e₂ := hvpEq
    refine ⟨⟨z, hvz, hpz, ?_⟩⟩
    rw [← he₁Eq]
    exact (mem_incidentEdges.mp he₁Incident).1

/-! ## The literal virtual response row -/

omit [Fintype V] in
@[simp]
theorem directionRow_simpleEdge_at_right
    (pos : V → Fin 3 → K) (x y : V) (hxy : x ≠ y) :
    directionRow pos (simpleEdge x y hxy) y = pos y - pos x := by
  rw [simpleEdge_comm x y hxy]
  exact directionRow_simpleEdge_at_left pos y x hxy.symm

omit [Fintype V] in
theorem directionRow_simpleEdge_at_other
    (pos : V → Fin 3 → K) (x y u : V) (hxy : x ≠ y)
    (hux : u ≠ x) (huy : u ≠ y) :
    directionRow pos (simpleEdge x y hxy) u = 0 := by
  apply directionRow_eq_zero_of_ne
  · intro hsource
    have hmem : u ∈ (simpleEdge x y hxy).vertices := by
      rw [← hsource]
      rw [SimpleEdge.vertices,
        ← (simpleEdge x y hxy).source_target_mk]
      simp [Sym2.toFinset_mk_eq]
    rw [vertices_simpleEdge] at hmem
    simp [hux, huy] at hmem
  · intro htarget
    have hmem : u ∈ (simpleEdge x y hxy).vertices := by
      rw [← htarget]
      rw [SimpleEdge.vertices,
        ← (simpleEdge x y hxy).source_target_mk]
      simp [Sym2.toFinset_mk_eq]
    rw [vertices_simpleEdge] at hmem
    simp [hux, huy] at hmem

omit [Fintype V] in
/-- A singleton edge coefficient synthesizes exactly its scalar direction
row in the full vertex-load space. -/
theorem directionEquilibrium_piSingle
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K)
    (e : F) (c : K) :
    directionEquilibrium F pos (Pi.single e c) =
      c • directionRow pos e.1 := by
  rw [directionEquilibrium_eq_sum_smul_directionRow]
  change (∑ x ∈ F.attach,
    (Pi.single e c : F → K) x • directionRow pos x.1) =
      c • directionRow pos e.1
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hbe
    simp [hbe]
  · intro he
    exact (he (Finset.mem_attach F e)).elim

omit [Fintype V] in
/-- The explicit two-star relation on three collinear points has away-load
equal to a scalar multiple of the virtual endpoint row. -/
theorem privateTwoStarRows_eq_virtualRow
    (pos : V → Fin 3 → K) (v p z : V)
    (hvp : v ≠ p) (hvz : v ≠ z) (hpz : p ≠ z) (s : K)
    (hs : pos v - pos p = s • (pos z - pos p)) :
    (1 - s) • directionRow pos (simpleEdge v p hvp) +
        s • directionRow pos (simpleEdge v z hvz) =
      (s * (1 - s)) • directionRow pos (simpleEdge p z hpz) := by
  funext u j
  by_cases huv : u = v
  · subst u
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_left pos v p hvp) j,
      congrFun (directionRow_simpleEdge_at_left pos v z hvz) j,
      congrFun (directionRow_simpleEdge_at_other pos p z v hpz hvp hvz) j]
    have hj := congrFun hs j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hj ⊢
    linear_combination hj
  · by_cases hup : u = p
    · subst u
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_right pos v p hvp) j,
        congrFun (directionRow_simpleEdge_at_other pos v z p hvz hvp.symm hpz) j,
        congrFun (directionRow_simpleEdge_at_left pos p z hpz) j]
      have hj := congrFun hs j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at hj ⊢
      linear_combination -(1 - s) * hj
    · by_cases huz : u = z
      · subst u
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_other pos v p z hvp hvz.symm hpz.symm) j,
          congrFun (directionRow_simpleEdge_at_right pos v z hvz) j,
          congrFun (directionRow_simpleEdge_at_right pos p z hpz) j]
        have hj := congrFun hs j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at hj ⊢
        linear_combination -s * hj
      · simp only [Pi.add_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_other pos v p u hvp huv hup) j,
          congrFun (directionRow_simpleEdge_at_other pos v z u hvz huv huz) j,
          congrFun (directionRow_simpleEdge_at_other pos p z u hpz hup huz) j]
        simp

/-! ## Classification of failed private payment -/

/-- Under the pivoted flag shape, failure of the one-coordinate inequality
forces the stated local dimensions and a zero connecting class. -/
theorem privateExceptional_classification
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v p q : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hvpMem : simpleEdge v p hvp ∈ F)
    (hvqNotMem : simpleEdge v q hvq ∉ F)
    (hDegree : edgeSetDegree F v ≤ 2)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos v) (pos p) (pos q))
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤)
    (hExceptional : PrivateExceptional (k := k) F pos v) :
    ∃ N : PrivateSecondNeighbour F v p,
      q ≠ N.z ∧
      PinCollinearity.Collinear (pos v) (pos p) (pos N.z) ∧
      outsideExtensionTrdeg (k := k) pos v = 1 ∧
      outsideResponseKernelDim F pos v = 1 ∧
      outsideLocalKernelDim F pos v = 1 ∧
      outsideLocalRank F pos v = 1 ∧
      edgeSetDegree F v = 2 ∧
      deletedConnectingClass F pos v = 0 := by
  let d : ℕ := (outsideExtensionTrdeg (k := k) pos v).toNat
  have hTrdegLeOne := privateExtensionTrdeg_le_one_of_collinear
    (k := k) pos v p q hvp hvq hpq hpos hcol hgen
  have hd : d ≤ 1 := by
    simpa [d] using Cardinal.toNat_le_toNat hTrdegLeOne
  have hFailure : 1 < outsideResponseKernelDim F pos v + d := by
    unfold PrivateExceptional PrivateNonexceptional at hExceptional
    simpa [d] using (show
      1 < outsideResponseKernelDim F pos v +
        (outsideExtensionTrdeg (k := k) pos v).toNat by omega)
  have hResponseLe :=
    outsideResponseKernelDim_le_outsideLocalKernelDim F pos v
  have hRankNullity := outsideLocalRank_add_kernelDim_eq_degree F pos v
  have hDegreePos : 0 < edgeSetDegree F v := by
    apply Finset.card_pos.mpr
    exact ⟨simpleEdge v p hvp,
      mem_incidentEdges.mpr ⟨hvpMem, by rw [vertices_simpleEdge]; simp⟩⟩
  have hRankPos :=
    outsideLocalRank_pos_of_injective_of_degree_pos F pos v hpos hDegreePos
  have hDegreeTwo : edgeSetDegree F v = 2 := by omega
  have hResponseOne : outsideResponseKernelDim F pos v = 1 := by omega
  have hKernelOne : outsideLocalKernelDim F pos v = 1 := by omega
  have hRankOne : outsideLocalRank F pos v = 1 := by omega
  have hdOne : d = 1 := by omega
  let N : PrivateSecondNeighbour F v p :=
    Classical.choice
      (exists_privateSecondNeighbour F v p hvp hvpMem hDegreeTwo)
  have hqz : q ≠ N.z := by
    intro h
    subst q
    apply hvqNotMem
    simpa using N.vz_mem
  have hvpPos : pos v ≠ pos p := fun h ↦ hvp (hpos h)
  have hpzPos : pos p ≠ pos N.z := fun h ↦ N.hpz (hpos h)
  have hPointPMem :
      pos v - pos p ∈ LinearMap.range (localEquilibriumAt F pos v) :=
    namedNeighbourDifference_mem_localRange F pos v p hvp hvpMem
  have hPointZMem :
      pos v - pos N.z ∈ LinearMap.range (localEquilibriumAt F pos v) :=
    namedNeighbourDifference_mem_localRange F pos v N.z N.hvz N.vz_mem
  have hline : ∃ s : K,
      pos v = pos p + s • (pos N.z - pos p) := by
    apply exists_line_parameter_of_finrank_le_one
      (pos v) (pos p) (pos N.z)
      (LinearMap.range (localEquilibriumAt F pos v))
      hvpPos hpzPos hPointPMem hPointZMem
    change outsideLocalRank F pos v ≤ 1
    omega
  obtain ⟨s, hs⟩ := hline
  have hCollinearZ :
      PinCollinearity.Collinear (pos v) (pos p) (pos N.z) :=
    collinear_of_point_eq_line (pos v) (pos p) (pos N.z) s hs
  have hTrdegFinite := outsideExtensionTrdeg_lt_aleph0
    (k := k) pos v hgen
  have hTrdegOne : outsideExtensionTrdeg (k := k) pos v = 1 := by
    calc
      outsideExtensionTrdeg (k := k) pos v =
          ((outsideExtensionTrdeg (k := k) pos v).toNat : Cardinal) :=
        (Cardinal.cast_toNat_of_lt_aleph0 hTrdegFinite).symm
      _ = 1 := by
        change (d : Cardinal) = 1
        exact_mod_cast hdOne
  have hConnectingZero : deletedConnectingClass F pos v = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_top]
    change outsideResponseKernelDim F pos v = outsideLocalKernelDim F pos v
    rw [hResponseOne, hKernelOne]
  exact ⟨N, hqz, hCollinearZ, hTrdegOne, hResponseOne,
    hKernelOne, hRankOne, hDegreeTwo, hConnectingZero⟩

/-- In the forced private exceptional shape,
the virtual row from the retained flag endpoint `p` to the second neighbour
`z` already lies in the literal child row space after deleting `v`.

The proof constructs the two-star relation, sends it through the actual
connecting map, identifies its away-load with a nonzero multiple of the
virtual row, and cancels that scalar. -/
theorem privateExceptional_virtualRow_mem
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v p q : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hvpMem : simpleEdge v p hvp ∈ F)
    (hvqNotMem : simpleEdge v q hvq ∉ F)
    (hDegree : edgeSetDegree F v ≤ 2)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos v) (pos p) (pos q))
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤)
    (hExceptional : PrivateExceptional (k := k) F pos v) :
    ∃ N : PrivateSecondNeighbour F v p,
      q ≠ N.z ∧
      PinCollinearity.Collinear (pos v) (pos p) (pos N.z) ∧
      directionRow pos (simpleEdge p N.z N.hpz) ∈
        directionRowSpace (deleteVertexEdges F v) pos := by
  obtain ⟨N, hqz, hCollinearZ, _hTrdegOne, _hResponseOne,
      _hKernelOne, _hRankOne, _hDegreeTwo, hConnectingZero⟩ :=
    privateExceptional_classification (k := k) F pos v p q
      hvp hvq hpq hvpMem hvqNotMem hDegree hpos hcol hgen hExceptional
  have hpzPos : pos p ≠ pos N.z := fun h ↦ N.hpz (hpos h)
  have hColPZV :
      PinCollinearity.Collinear (pos p) (pos N.z) (pos v) :=
    collinear_cycle (pos v) (pos p) (pos N.z) hCollinearZ
  obtain ⟨s, hs⟩ :=
    (collinear_iff_exists_smul_difference
      (pos p) (pos N.z) (pos v) hpzPos).1 hColPZV
  have hsZero : s ≠ 0 := by
    intro hs0
    have hvpPos : pos v = pos p := by
      apply sub_eq_zero.mp
      simpa [hs0] using hs
    exact hvp (hpos hvpPos)
  have hsOne : s ≠ 1 := by
    intro hs1
    have hvzPos : pos v = pos N.z := by
      apply sub_eq_zero.mp
      have : pos v - pos N.z = 0 := by
        funext j
        have hj := congrFun hs j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at hj ⊢
        rw [hs1] at hj
        linear_combination hj
      exact this
    exact N.hvz (hpos hvzPos)
  have hScalar : s * (1 - s) ≠ 0 := by
    exact mul_ne_zero hsZero (sub_ne_zero.mpr (Ne.symm hsOne))
  let ep : incidentEdges F v :=
    ⟨simpleEdge v p hvp,
      mem_incidentEdges.mpr
        ⟨hvpMem, by rw [vertices_simpleEdge]; simp⟩⟩
  let ez : incidentEdges F v :=
    ⟨simpleEdge v N.z N.hvz,
      mem_incidentEdges.mpr
        ⟨N.vz_mem, by rw [vertices_simpleEdge]; simp⟩⟩
  let localWeight : incidentEdges F v → K :=
    Pi.single ep (1 - s) + Pi.single ez s
  have hLocalKernel : localEquilibriumAt F pos v localWeight = 0 := by
    change localEquilibriumAt F pos v
      (Pi.single ep (1 - s) + Pi.single ez s) = 0
    rw [map_add, localEquilibriumAt_piSingle,
      localEquilibriumAt_piSingle]
    change
      (1 - s) • directionRow pos (simpleEdge v p hvp) v +
          s • directionRow pos (simpleEdge v N.z N.hvz) v = 0
    rw [directionRow_simpleEdge_at_left,
      directionRow_simpleEdge_at_left]
    funext j
    have hj := congrFun hs j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hj ⊢
    linear_combination hj
  let localRelation : LinearMap.ker (localEquilibriumAt F pos v) :=
    ⟨localWeight, hLocalKernel⟩
  have hClassZero :
      deletedConnectingClass F pos v localRelation = 0 := by
    rw [hConnectingZero]
    rfl
  have hAwayMem :=
    (deletedConnectingClass_eq_zero_iff F pos v localRelation).1 hClassZero
  have hFullLoad :
      directionEquilibrium (incidentEdges F v) pos localWeight =
        (s * (1 - s)) •
          directionRow pos (simpleEdge p N.z N.hpz) := by
    change directionEquilibrium (incidentEdges F v) pos
      (Pi.single ep (1 - s) + Pi.single ez s) = _
    rw [map_add, directionEquilibrium_piSingle,
      directionEquilibrium_piSingle]
    exact privateTwoStarRows_eq_virtualRow
      pos v p N.z hvp N.hvz N.hpz s hs
  have hScaledAway :
      restrictAway v
          ((s * (1 - s)) •
            directionRow pos (simpleEdge p N.z N.hpz)) ∈
        deletedAwayRowSpace F pos v := by
    change localToOldEquilibrium F pos v localWeight ∈
      deletedAwayRowSpace F pos v at hAwayMem
    change restrictAway v
      (directionEquilibrium (incidentEdges F v) pos localWeight) ∈
        deletedAwayRowSpace F pos v at hAwayMem
    rw [hFullLoad] at hAwayMem
    exact hAwayMem
  change restrictAway v
      ((s * (1 - s)) •
        directionRow pos (simpleEdge p N.z N.hpz)) ∈
    (directionRowSpace (deleteVertexEdges F v) pos).map
      (restrictAway v) at hScaledAway
  obtain ⟨childLoad, hChildLoad, hChildRestrict⟩ :=
    Submodule.mem_map.mp hScaledAway
  have hChildAtV : childLoad v = 0 := by
    have hChildRange := hChildLoad
    rw [directionRowSpace_eq_range] at hChildRange
    obtain ⟨childWeight, hChildWeight⟩ := hChildRange
    rw [← hChildWeight]
    exact old_packet_equilibrium_at_deleted F pos v childWeight
  have hVirtualAtV :
      ((s * (1 - s)) •
        directionRow pos (simpleEdge p N.z N.hpz)) v = 0 := by
    funext j
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    rw [congrFun
      (directionRow_simpleEdge_at_other pos p N.z v N.hpz hvp N.hvz) j]
    simp
  have hChildEq : childLoad =
      (s * (1 - s)) •
        directionRow pos (simpleEdge p N.z N.hpz) := by
    funext u
    by_cases huv : u = v
    · subst u
      rw [hChildAtV, hVirtualAtV]
    · have hu := congrFun hChildRestrict ⟨u, huv⟩
      exact hu
  have hScaledMem :
      (s * (1 - s)) •
          directionRow pos (simpleEdge p N.z N.hpz) ∈
        directionRowSpace (deleteVertexEdges F v) pos := by
    rw [← hChildEq]
    exact hChildLoad
  have hVirtualMem :=
    (directionRowSpace (deleteVertexEdges F v) pos).smul_mem
      (s * (1 - s))⁻¹ hScaledMem
  have hCancel : (s * (1 - s))⁻¹ * (s * (1 - s)) = 1 :=
    inv_mul_cancel₀ hScalar
  refine ⟨N, hqz, hCollinearZ, ?_⟩
  simpa only [smul_smul, hCancel, one_smul] using hVirtualMem

omit [Fintype V] [DecidableEq V] in
/-- Two collinear triples sharing two distinct first points put the two
remaining points on one common line, with a nonzero affine parameter when
the new endpoint is distinct. -/
theorem exists_nonzero_line_parameter_of_common_collinear
    (x p q z : Fin 3 → K)
    (hxp : x ≠ p) (hpq : p ≠ q) (hpz : p ≠ z)
    (hxpq : PinCollinearity.Collinear x p q)
    (hxpz : PinCollinearity.Collinear x p z) :
    ∃ t : K, t ≠ 0 ∧ z - p = t • (q - p) := by
  obtain ⟨alpha, hq⟩ :=
    (collinear_iff_exists_smul_difference x p q hxp).1 hxpq
  obtain ⟨beta, hz⟩ :=
    (collinear_iff_exists_smul_difference x p z hxp).1 hxpz
  have hAlphaOne : alpha ≠ 1 := by
    intro h
    apply hpq
    have hqx : q - x = p - x := by
      simpa only [h, one_smul] using hq
    exact (sub_left_inj.mp hqx).symm
  have hAlphaSub : alpha - 1 ≠ 0 := sub_ne_zero.mpr hAlphaOne
  let t : K := (beta - 1) * (alpha - 1)⁻¹
  have hQP : q - p = (alpha - 1) • (p - x) := by
    funext j
    have hj := congrFun hq j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linear_combination hj
  have hZP : z - p = (beta - 1) • (p - x) := by
    funext j
    have hj := congrFun hz j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linear_combination hj
  have hline : z - p = t • (q - p) := by
    rw [hQP, hZP, smul_smul]
    have hScalar : t * (alpha - 1) = beta - 1 := by
      dsimp [t]
      rw [mul_assoc, inv_mul_cancel₀ hAlphaSub, mul_one]
    rw [hScalar]
  have ht : t ≠ 0 := by
    intro htZero
    apply hpz
    exact (sub_eq_zero.mp (by simpa [htZero] using hline)).symm
  exact ⟨t, ht, hline⟩

omit [Fintype V] in
/-- Scaled triangle-row identity for three collinear placed points.  The
identity is stated without division so cancellation is isolated in the
consumer. -/
theorem triangleRows_scaled_identity
    (pos : V → Fin 3 → K) (p q z : V)
    (hpq : p ≠ q) (hpz : p ≠ z) (hqz : q ≠ z) (t : K)
    (hline : pos z - pos p = t • (pos q - pos p)) :
    t • directionRow pos (simpleEdge q z hqz) =
      (t * (1 - t)) • directionRow pos (simpleEdge p q hpq) +
        (t - 1) • directionRow pos (simpleEdge p z hpz) := by
  funext u j
  by_cases hup : u = p
  · subst u
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_other pos q z p hqz hpq hpz) j,
      congrFun (directionRow_simpleEdge_at_left pos p q hpq) j,
      congrFun (directionRow_simpleEdge_at_left pos p z hpz) j]
    have hj := congrFun hline j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hj ⊢
    linear_combination (t - 1) * hj
  · by_cases huq : u = q
    · subst u
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_left pos q z hqz) j,
        congrFun (directionRow_simpleEdge_at_right pos p q hpq) j,
        congrFun (directionRow_simpleEdge_at_other pos p z q hpz hpq.symm hqz) j]
      have hj := congrFun hline j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at hj ⊢
      linear_combination -t * hj
    · by_cases huz : u = z
      · subst u
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_right pos q z hqz) j,
          congrFun (directionRow_simpleEdge_at_other pos p q z hpq hpz.symm hqz.symm) j,
          congrFun (directionRow_simpleEdge_at_right pos p z hpz) j]
        have hj := congrFun hline j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at hj ⊢
        linear_combination hj
      · simp only [Pi.add_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_other pos q z u hqz huq huz) j,
          congrFun (directionRow_simpleEdge_at_other pos p q u hpq hup huq) j,
          congrFun (directionRow_simpleEdge_at_other pos p z u hpz hup huz) j]
        simp

/-- If the other live terminal edge `pq` is
present, both possible response edges from the second neighbour lie in the
child row space. -/
theorem privateExceptional_bothVirtualRows_mem
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v p q : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hvpMem : simpleEdge v p hvp ∈ F)
    (hpqMem : simpleEdge p q hpq ∈ F)
    (hvqNotMem : simpleEdge v q hvq ∉ F)
    (hDegree : edgeSetDegree F v ≤ 2)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos v) (pos p) (pos q))
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤)
    (hExceptional : PrivateExceptional (k := k) F pos v) :
    ∃ (N : PrivateSecondNeighbour F v p) (hqz : q ≠ N.z),
      directionRow pos (simpleEdge p N.z N.hpz) ∈
          directionRowSpace (deleteVertexEdges F v) pos ∧
      directionRow pos (simpleEdge q N.z hqz) ∈
          directionRowSpace (deleteVertexEdges F v) pos := by
  obtain ⟨N, hqz, hCollinearZ, hpzRow⟩ :=
    privateExceptional_virtualRow_mem (k := k) F pos v p q
      hvp hvq hpq hvpMem hvqNotMem hDegree hpos hcol hgen hExceptional
  have hvpPos : pos v ≠ pos p := fun h ↦ hvp (hpos h)
  have hpqPos : pos p ≠ pos q := fun h ↦ hpq (hpos h)
  have hpzPos : pos p ≠ pos N.z := fun h ↦ N.hpz (hpos h)
  obtain ⟨t, ht, hline⟩ :=
    exists_nonzero_line_parameter_of_common_collinear
      (pos v) (pos p) (pos q) (pos N.z)
      hvpPos hpqPos hpzPos hcol hCollinearZ
  have hpqDelete : simpleEdge p q hpq ∈ deleteVertexEdges F v := by
    apply mem_deleteVertexEdges.mpr
    refine ⟨hpqMem, ?_⟩
    rw [vertices_simpleEdge]
    simp [hvp, hvq]
  have hpqRow : directionRow pos (simpleEdge p q hpq) ∈
      directionRowSpace (deleteVertexEdges F v) pos := by
    apply Submodule.subset_span
    exact ⟨⟨simpleEdge p q hpq, hpqDelete⟩, rfl⟩
  have hScaledRow :
      t • directionRow pos (simpleEdge q N.z hqz) ∈
        directionRowSpace (deleteVertexEdges F v) pos := by
    rw [triangleRows_scaled_identity pos p q N.z hpq N.hpz hqz t hline]
    exact (directionRowSpace (deleteVertexEdges F v) pos).add_mem
      ((directionRowSpace (deleteVertexEdges F v) pos).smul_mem _ hpqRow)
      ((directionRowSpace (deleteVertexEdges F v) pos).smul_mem _ hpzRow)
  have hRow :=
    (directionRowSpace (deleteVertexEdges F v) pos).smul_mem t⁻¹ hScaledRow
  have hCancel : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  have hqzRow : directionRow pos (simpleEdge q N.z hqz) ∈
      directionRowSpace (deleteVertexEdges F v) pos := by
    simpa only [smul_smul, hCancel, one_smul] using hRow
  exact ⟨N, hqz, hpzRow, hqzRow⟩

end

end DirectionStress

end RB31E2E


end
end BundleSource0029

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0029/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0029.json"

section BundleSource0030
/- Source: Papers/RigidityZheng_Linear_DirectionStressVertexDeletion.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/DirectionStressVertexDeletion.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Reindexing direction stresses after a literal vertex deletion

`restrictedLiveEdges F v` is a graph on the subtype of vertices different
from `v`, whereas `deleteVertexEdges F v` retains the parent vertex type.
This file proves that these are not merely equinumerous presentations: the
actual direction-stress kernels are linearly equivalent after restricting
the placement.  This is the cross-type bridge needed to apply induction to
the child `State` and the deletion exact sequence to the parent graph.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

open ProvenanceFlag Sparse22Transport

/-- Restriction of a placement to the literal remaining-vertex subtype. -/
def restrictPlacement (a : V → Fin 3 → k) (v : V) :
    RemainingVertex v → Fin 3 → k :=
  fun u ↦ a u.1

/-- The child-edge subtype and the deleted parent-edge subtype are
canonically equivalent. -/
def restrictedEdgeEquiv (F : SimpleEdgeSet V) (v : V) :
    ↑(restrictedLiveEdges F v) ≃ ↑(deleteVertexEdges F v) where
  toFun e :=
    ⟨mapSimpleEdge (remainingVertexEmbedding v) e.1,
      (mem_restrictedLiveEdges_iff F v e.1).1 e.2⟩
  invFun e :=
    ⟨restrictDeletedEdge F v e,
      Finset.mem_map.mpr ⟨e, Finset.mem_attach _ e, rfl⟩⟩
  left_inv e := by
    apply Subtype.ext
    apply mapSimpleEdge_injective (remainingVertexEmbedding v)
    change mapSimpleEdge (remainingVertexEmbedding v)
      (restrictDeletedEdge F v
        ⟨mapSimpleEdge (remainingVertexEmbedding v) e.1, _⟩) =
      mapSimpleEdge (remainingVertexEmbedding v) e.1
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]
  right_inv e := by
    apply Subtype.ext
    change mapSimpleEdge (remainingVertexEmbedding v)
      (restrictDeletedEdge F v e) = e.1
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]

/-- Reindex edge-weight functions along the canonical deleted-edge
equivalence. -/
def restrictedEdgeWeightEquiv (F : SimpleEdgeSet V) (v : V) :
    (restrictedLiveEdges F v → k) ≃ₗ[k]
      (deleteVertexEdges F v → k) where
  toFun weight e := weight ((restrictedEdgeEquiv F v).symm e)
  invFun weight e := weight (restrictedEdgeEquiv F v e)
  left_inv weight := by
    funext e
    simp
  right_inv weight := by
    funext e
    simp
  map_add' _x _y := rfl
  map_smul' _c _x := rfl

omit [Fintype V] in
/-- Restricting a parent edge which avoids `v` preserves its direction row
at every remaining vertex. -/
theorem directionRow_restrictSimpleEdge
    (a : V → Fin 3 → k) (v : V) (e : SimpleEdge V)
    (hve : v ∉ e.vertices) (u : RemainingVertex v) :
    directionRow (restrictPlacement a v) (restrictSimpleEdge v e hve) u =
      directionRow a e u.1 := by
  let source : RemainingVertex v :=
    ⟨e.source, fun h ↦ hve (h ▸ by
      rw [SimpleEdge.vertices, ← e.source_target_mk]
      simp [Sym2.toFinset_mk_eq])⟩
  let target : RemainingVertex v :=
    ⟨e.target, fun h ↦ hve (h ▸ by
      rw [SimpleEdge.vertices, ← e.source_target_mk]
      simp [Sym2.toFinset_mk_eq])⟩
  have hParent : e = simpleEdge e.source e.target e.source_ne_target := by
    apply Subtype.ext
    exact e.source_target_mk.symm
  have hChild : restrictSimpleEdge v e hve =
      simpleEdge source target (by
        intro h
        exact e.source_ne_target (congrArg Subtype.val h)) := by
    rfl
  rw [hChild]
  conv_rhs => rw [hParent]
  by_cases huSource : u = source
  · subst u
    rw [directionRow_simpleEdge_at_left,
      directionRow_simpleEdge_at_left]
    rfl
  · by_cases huTarget : u = target
    · subst u
      rw [directionRow_simpleEdge_at_right,
        directionRow_simpleEdge_at_right]
      rfl
    · rw [directionRow_simpleEdge_at_other]
      · rw [directionRow_simpleEdge_at_other]
        · exact fun h ↦ huSource (Subtype.ext h)
        · exact fun h ↦ huTarget (Subtype.ext h)
      · exact huSource
      · exact huTarget

omit [Fintype V] in
/-- Mapping a child edge to the deleted parent presentation preserves its
direction row on remaining vertices. -/
theorem directionRow_restrictedEdgeEquiv
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (e : restrictedLiveEdges F v) (u : RemainingVertex v) :
    directionRow (restrictPlacement a v) e.1 u =
      directionRow a (restrictedEdgeEquiv F v e).1 u.1 := by
  let E : deleteVertexEdges F v := restrictedEdgeEquiv F v e
  have hAvoid : v ∉ E.1.vertices := (mem_deleteVertexEdges.mp E.2).2
  have hRestrict : restrictDeletedEdge F v E = e.1 := by
    apply mapSimpleEdge_injective (remainingVertexEmbedding v)
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]
    rfl
  rw [← hRestrict]
  exact directionRow_restrictSimpleEdge a v E.1 hAvoid u

omit [Fintype V] in
/-- Equilibrium synthesis commutes with the cross-type deletion reindexing. -/
theorem directionEquilibrium_restricted
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (weight : restrictedLiveEdges F v → k) (u : RemainingVertex v) :
    directionEquilibrium (restrictedLiveEdges F v)
        (restrictPlacement a v) weight u =
      directionEquilibrium (deleteVertexEdges F v) a
        (restrictedEdgeWeightEquiv F v weight) u.1 := by
  funext j
  change (∑ e : restrictedLiveEdges F v,
      weight e * directionRow (restrictPlacement a v) e.1 u j) =
    ∑ e : deleteVertexEdges F v,
      (restrictedEdgeWeightEquiv F v weight) e *
        directionRow a e.1 u.1 j
  exact Fintype.sum_equiv (restrictedEdgeEquiv F v)
    (fun e : restrictedLiveEdges F v ↦
      weight e * directionRow (restrictPlacement a v) e.1 u j)
    (fun e : deleteVertexEdges F v ↦
      (restrictedEdgeWeightEquiv F v weight) e *
        directionRow a e.1 u.1 j)
    (fun e ↦ by
      change weight e * directionRow (restrictPlacement a v) e.1 u j =
        (restrictedEdgeWeightEquiv F v weight) (restrictedEdgeEquiv F v e) *
          directionRow a (restrictedEdgeEquiv F v e).1 u.1 j
      rw [directionRow_restrictedEdgeEquiv F a v e u]
      simp [restrictedEdgeWeightEquiv])

/-- The literal stress spaces in the subtype child and deleted parent
presentations are linearly equivalent. -/
def restrictedStressEquiv
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    DirectionStressSpace (restrictedLiveEdges F v) (restrictPlacement a v) ≃ₗ[k]
      DirectionStressSpace (deleteVertexEdges F v) a where
  toFun weight := by
    refine ⟨restrictedEdgeWeightEquiv F v weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    funext u
    by_cases huv : u = v
    · subst u
      exact old_packet_equilibrium_at_deleted F a v
        (restrictedEdgeWeightEquiv F v weight.1)
    · let ur : RemainingVertex v := ⟨u, huv⟩
      have hChild := LinearMap.mem_ker.mp weight.2
      have hChildAt := congrFun hChild ur
      rw [directionEquilibrium_restricted F a v weight.1 ur] at hChildAt
      exact hChildAt
  invFun weight := by
    refine ⟨(restrictedEdgeWeightEquiv F v).symm weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    funext u
    rw [directionEquilibrium_restricted]
    rw [(restrictedEdgeWeightEquiv F v).apply_symm_apply]
    have hParent := LinearMap.mem_ker.mp weight.2
    have hAt := congrFun hParent u.1
    exact hAt
  left_inv weight := by
    apply Subtype.ext
    exact (restrictedEdgeWeightEquiv F v).symm_apply_apply weight.1
  right_inv weight := by
    apply Subtype.ext
    exact (restrictedEdgeWeightEquiv F v).apply_symm_apply weight.1
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' c x := by
    apply Subtype.ext
    rfl

omit [Fintype V] in
/-- Stress nullity is exactly invariant under the literal child reindexing. -/
theorem directionStressDim_restrictedLiveEdges
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    directionStressDim (restrictedLiveEdges F v) (restrictPlacement a v) =
      directionStressDim (deleteVertexEdges F v) a := by
  exact (restrictedStressEquiv F a v).finrank_eq

end

end DirectionStress

end RB31E2E


end
end BundleSource0030

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0030/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0030.json"

section BundleSource0031
/- Source: Papers/RigidityZheng_Linear_DirectionStressBaseChange.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/DirectionStressBaseChange.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Direction-stress dimension under field extension

The provenance induction projects a generic configuration to the field
generated by the retained coordinates.  Its child direction rows are
therefore first defined over that smaller field and then viewed over the
parent function field.  This file proves, from the literal row formulas,
that row rank and hence stress dimension are unchanged by this scalar
extension.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {L K V : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype V] [DecidableEq V]

/-- Coordinatewise scalar extension of a placement. -/
def mapPlacement (a : V → Fin 3 → L) : V → Fin 3 → K :=
  fun v j ↦ algebraMap L K (a v j)

/-- Flatten vertex and spatial coordinates into a single finite function
space.  This is the representation consumed by the finite-family
base-change theorem. -/
def flattenVector (x : V → Fin 3 → L) : V × Fin 3 → L :=
  fun p ↦ x p.1 p.2

omit [Fintype V] [DecidableEq V] in
/-- Currying is a linear equivalence, so flattening a finite row family does
not change the dimension of its span. -/
theorem finrank_span_flatten
    {I : Type*} [Finite I] (row : I → V → Fin 3 → L) :
    Module.finrank L (Submodule.span L (Set.range row)) =
      Module.finrank L
        (Submodule.span L (Set.range (fun i ↦ flattenVector (row i)))) := by
  let flat : (V → Fin 3 → L) ≃ₗ[L] (V × Fin 3 → L) :=
    (LinearEquiv.curry L L V (Fin 3)).symm
  have hset :
      flat '' Set.range row =
        Set.range (fun i ↦ flattenVector (row i)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨row i, ⟨i, rfl⟩, rfl⟩
  have hspan :
      (Submodule.span L (Set.range row)).map
          (flat : (V → Fin 3 → L) →ₗ[L] (V × Fin 3 → L)) =
        Submodule.span L
          (Set.range (fun i ↦ flattenVector (row i))) := by
    rw [Submodule.map_span]
    change Submodule.span L (flat '' Set.range row) = _
    rw [hset]
  calc
    Module.finrank L (Submodule.span L (Set.range row)) =
        Module.finrank L
          ((Submodule.span L (Set.range row)).map
            (flat : (V → Fin 3 → L) →ₗ[L] (V × Fin 3 → L))) := by
      symm
      exact LinearEquiv.finrank_map_eq flat _
    _ = Module.finrank L
        (Submodule.span L
          (Set.range (fun i ↦ flattenVector (row i)))) := by
      rw [hspan]

omit [Fintype V] in
/-- A direction row is transported coordinatewise by scalar extension. -/
theorem directionRow_mapPlacement
    (a : V → Fin 3 → L) (e : SimpleEdge V) :
    flattenVector (directionRow (mapPlacement (K := K) a) e) =
      FiniteFamilyBaseChange.mapVector (K := K)
        (flattenVector (directionRow a e)) := by
  funext p
  rcases p with ⟨v, j⟩
  simp only [directionRow, edgeDirection, mapPlacement,
    flattenVector, FiniteFamilyBaseChange.mapVector, Function.comp_apply]
  split_ifs <;> simp

/-- Direction-row rank is invariant under a field extension. -/
theorem directionEquilibriumRank_mapPlacement
    (F : SimpleEdgeSet V) (a : V → Fin 3 → L) :
    directionEquilibriumRank F (mapPlacement (K := K) a) =
      directionEquilibriumRank F a := by
  rw [directionEquilibriumRank_eq_finrank_span_rows,
    directionEquilibriumRank_eq_finrank_span_rows]
  rw [finrank_span_flatten, finrank_span_flatten]
  have hbase := FiniteFamilyBaseChange.finrank_span_range_mapVector_finite
    (K := K) (fun e : F ↦ flattenVector (directionRow a e.1))
  rw [hbase]
  have hset :
      Set.range (fun e : F ↦
        FiniteFamilyBaseChange.mapVector (K := K)
          (flattenVector (directionRow a e.1))) =
        Set.range (fun e : F ↦
          flattenVector (directionRow (mapPlacement (K := K) a) e.1)) := by
    ext x
    constructor <;> rintro ⟨e, rfl⟩
    · exact ⟨e, directionRow_mapPlacement (K := K) a e.1⟩
    · exact ⟨e, directionRow_mapPlacement (K := K) a e.1 |>.symm⟩
  rw [hset]

/-- Direction-stress nullity is invariant under a field extension. -/
theorem directionStressDim_mapPlacement
    (F : SimpleEdgeSet V) (a : V → Fin 3 → L) :
    directionStressDim F (mapPlacement (K := K) a) =
      directionStressDim F a := by
  have hK := directionStressDim_add_directionEquilibriumRank
    F (mapPlacement (K := K) a)
  have hL := directionStressDim_add_directionEquilibriumRank F a
  rw [directionEquilibriumRank_mapPlacement] at hK
  omega

end

end DirectionStress

end RB31E2E


end
end BundleSource0031

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0031/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0031.json"

section BundleSource0032
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagDeletionLedger.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagDeletionLedger.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Exact budget transport across provenance-flag deletion

This file is the numerical interface consumed by the strong induction.
It constructs the actual outside and private child placements on their
literal subtype states, identifies their stress dimensions with the parent
deleted graph, and proves the two local budget lifts:

* outside deletion consumes at most three coordinates;
* private deletion consumes one coordinate but also removes one flag, so
  the local allowance is exactly one.

All branch dimensions are the transcendence degrees of actual coordinate
fields, and the tower equality is `CoordinateFieldTower.trdeg_add_eq`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-! ## Literal child placements -/

/-- Restrict an ambient-field placement branch to an outside-deletion
child. -/
def PlacementBranch.deleteOutsidePlacement
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0) :
    PlacementBranch (K := K) (S.deleteOutside v hv) where
  position := restrictPlacement Y.position v
  distinct := by
    intro a b hab
    apply Subtype.ext
    exact Y.distinct hab
  collinear t := by
    obtain ⟨origin, direction, hall⟩ := Y.collinear t
    refine ⟨origin, direction, ?_⟩
    intro a ha
    exact hall a.1
      ((mem_restrictVertexSet_iff v (S.terminals t)
        (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t) a).1 ha)

/-- Restrict an ambient-field placement branch to a private-deletion child,
simultaneously consuming its unique flag. -/
def PlacementBranch.deletePrivatePlacement
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    PlacementBranch (K := K) (S.deletePrivate v t hOne hvt) where
  position := restrictPlacement Y.position v
  distinct := by
    intro a b hab
    apply Subtype.ext
    exact Y.distinct hab
  collinear r := by
    obtain ⟨origin, direction, hall⟩ := Y.collinear r.1
    refine ⟨origin, direction, ?_⟩
    intro a ha
    exact hall a.1
      ((mem_restrictVertexSet_iff v (S.terminals r.1)
        (not_mem_other_terminals_of_flagMultiplicity_eq_one
          S v t hOne hvt r.1 r.2) a).1 ha)

@[simp]
theorem deleteOutsidePlacement_position
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0) :
    (Y.deleteOutsidePlacement S v hv).position =
      restrictPlacement Y.position v := rfl

@[simp]
theorem deletePrivatePlacement_position
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    (Y.deletePrivatePlacement S v t hOne hvt).position =
      restrictPlacement Y.position v := rfl

/-! ## Cross-type stress and coordinate-field identities -/

/-- The outside child stress is exactly the stress of the parent's
vertex-deleted edge set. -/
theorem PlacementBranch.deleteOutsidePlacement_stressDim
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0) :
    (Y.deleteOutsidePlacement S v hv).stressDim (S.deleteOutside v hv) =
      directionStressDim (deleteVertexEdges S.edges v) Y.position := by
  exact directionStressDim_restrictedLiveEdges S.edges Y.position v

/-- The same exact stress identity for the private child. -/
theorem PlacementBranch.deletePrivatePlacement_stressDim
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    (Y.deletePrivatePlacement S v t hOne hvt).stressDim
        (S.deletePrivate v t hOne hvt) =
      directionStressDim (deleteVertexEdges S.edges v) Y.position := by
  exact directionStressDim_restrictedLiveEdges S.edges Y.position v

omit [Fintype V] [DecidableEq V] in
/-- The child's intrinsic coordinate field is definitionally the retained
coordinate field used by the deletion ledger. -/
theorem liveCoordinateField_restrictPlacement
    (a : V → Fin 3 → K) (v : V) :
    liveCoordinateField (k := k) (restrictPlacement a v) =
      retainedCoordinateField (k := k) a v := by
  rfl

omit [Fintype V] [DecidableEq V] in
/-- Exact transcendence-degree tower from the child coordinate field to a
coordinate-generated parent function field. -/
theorem trdeg_child_add_outsideExtension
    (a : V → Fin 3 → K) (v : V)
    (_hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤) :
    Algebra.trdeg k
        (liveCoordinateField (k := k) (restrictPlacement a v)) +
      outsideExtensionTrdeg (k := k) a v =
        Algebra.trdeg k K := by
  rw [liveCoordinateField_restrictPlacement]
  exact CoordinateFieldTower.trdeg_old_add_extension
    (k := k) (retainedCoordinates a v)

/-! ## Finite cardinal ledgers -/

theorem card_remainingVertex_add_one (v : V) :
    Fintype.card (RemainingVertex v) + 1 = Fintype.card V := by
  have hcard : Fintype.card (RemainingVertex v) = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun u : V ↦ u = v)]
    simp
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

theorem card_remainingFlag_add_one (t : Flag) :
    Fintype.card (RemainingFlag t) + 1 = Fintype.card Flag := by
  have hcard : Fintype.card (RemainingFlag t) = Fintype.card Flag - 1 := by
    rw [Fintype.card_subtype_compl (fun u : Flag ↦ u = t)]
    simp
  have hpos : 0 < Fintype.card Flag := Fintype.card_pos_iff.mpr ⟨t⟩
  omega

/-! ## The intrinsic child coordinate field -/

/-- The exact field generated by all coordinates retained after deleting
`v`. -/
abbrev retainedLiveCoordinateField
    (a : V → Fin 3 → K) (v : V) : IntermediateField k K :=
  liveCoordinateField (k := k) (restrictPlacement a v)

/-- The retained placement, now genuinely valued in its own intrinsic
coordinate field. -/
def intrinsicRestrictedPlacement
    (a : V → Fin 3 → K) (v : V) :
    RemainingVertex v → Fin 3 → retainedLiveCoordinateField (k := k) a v :=
  fun u j ↦
    ⟨a u.1 j, IntermediateField.subset_adjoin k
      (Set.range (liveCoordinateFamily (restrictPlacement a v)))
      ⟨(u, j), rfl⟩⟩

omit [Fintype V] [DecidableEq V] in
/-- Scalar-extending the intrinsic child placement recovers the ambient
restricted placement coordinatewise. -/
theorem map_intrinsicRestrictedPlacement
    (a : V → Fin 3 → K) (v : V) :
    mapPlacement (K := K) (intrinsicRestrictedPlacement (k := k) a v) =
      restrictPlacement a v := by
  funext u j
  rfl

omit [Fintype V] [DecidableEq V] in
/-- The intrinsic retained coordinates generate their field by
construction. -/
theorem intrinsicRestrictedPlacement_generated
    (a : V → Fin 3 → K) (v : V) :
    IntermediateField.adjoin k
      (Set.range (liveCoordinateFamily
        (intrinsicRestrictedPlacement (k := k) a v))) = ⊤ := by
  let L := retainedLiveCoordinateField (k := k) a v
  let x : RemainingVertex v × Fin 3 → L := fun c ↦
    intrinsicRestrictedPlacement (k := k) a v c.1 c.2
  apply top_unique
  intro y _hy
  exact IntermediateField.adjoin_induction k
    (motive := fun z hz ↦
      (⟨z, hz⟩ : L) ∈ IntermediateField.adjoin k (Set.range x))
    (fun z hz ↦ by
      obtain ⟨c, rfl⟩ := hz
      exact IntermediateField.subset_adjoin k (Set.range x) ⟨c, rfl⟩)
    (fun z ↦ (IntermediateField.adjoin k (Set.range x)).algebraMap_mem z)
    (fun _ _ _ _ hz hw ↦
      (IntermediateField.adjoin k (Set.range x)).add_mem hz hw)
    (fun _ _ hz ↦
      (IntermediateField.adjoin k (Set.range x)).inv_mem hz)
    (fun _ _ _ _ hz hw ↦
      (IntermediateField.adjoin k (Set.range x)).mul_mem hz hw)
    y.property

/-- Base change plus literal vertex reindexing identifies the child stress
computed over its intrinsic field with the parent deleted stress. -/
theorem directionStressDim_intrinsicRestrictedPlacement
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    directionStressDim (restrictedLiveEdges F v)
        (intrinsicRestrictedPlacement (k := k) a v) =
      directionStressDim (deleteVertexEdges F v) a := by
  calc
    directionStressDim (restrictedLiveEdges F v)
        (intrinsicRestrictedPlacement (k := k) a v) =
      directionStressDim (restrictedLiveEdges F v)
        (mapPlacement (K := K)
          (intrinsicRestrictedPlacement (k := k) a v)) :=
        (directionStressDim_mapPlacement
          (K := K) (restrictedLiveEdges F v)
          (intrinsicRestrictedPlacement (k := k) a v)).symm
    _ = directionStressDim (restrictedLiveEdges F v)
        (restrictPlacement a v) := by
      rw [map_intrinsicRestrictedPlacement]
    _ = directionStressDim (deleteVertexEdges F v) a :=
      directionStressDim_restrictedLiveEdges F a v

/-- Outside-child semismallness is equivalently computed using the stress
matrix over the child's intrinsic coordinate field. -/
theorem PlacementBranch.deleteOutside_semismallBudget_iff_intrinsic
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0) :
    PlacementBranch.SemismallBudget (k := k)
        (S.deleteOutside v hv) (Y.deleteOutsidePlacement S v hv) ↔
      (directionStressDim (restrictedLiveEdges S.edges v)
          (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k
            (retainedLiveCoordinateField (k := k) Y.position v) +
          2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) := by
  unfold PlacementBranch.SemismallBudget PlacementBranch.stressDim
  change
    (directionStressDim (restrictedLiveEdges S.edges v)
          (restrictPlacement Y.position v) : Cardinal) +
          Algebra.trdeg k
            (retainedLiveCoordinateField (k := k) Y.position v) +
          2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) ↔ _
  rw [← directionStressDim_mapPlacement
    (K := K) (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v),
    map_intrinsicRestrictedPlacement]

/-- Private-child semismallness has the same intrinsic-field
interpretation, with the consumed flag removed from the cardinal term. -/
theorem PlacementBranch.deletePrivate_semismallBudget_iff_intrinsic
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    PlacementBranch.SemismallBudget (k := k)
        (S.deletePrivate v t hOne hvt)
        (Y.deletePrivatePlacement S v t hOne hvt) ↔
      (directionStressDim (restrictedLiveEdges S.edges v)
          (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k
            (retainedLiveCoordinateField (k := k) Y.position v) +
          2 * (Fintype.card (RemainingFlag t) : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) := by
  unfold PlacementBranch.SemismallBudget PlacementBranch.stressDim
  change
    (directionStressDim (restrictedLiveEdges S.edges v)
          (restrictPlacement Y.position v) : Cardinal) +
          Algebra.trdeg k
            (retainedLiveCoordinateField (k := k) Y.position v) +
          2 * (Fintype.card (RemainingFlag t) : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) ↔ _
  rw [← directionStressDim_mapPlacement
    (K := K) (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v),
    map_intrinsicRestrictedPlacement]

/-! ## The two direct induction interfaces -/

/-- **Outside nonexceptional budget lift.**  A semismall outside child and
the literal local payment `u + d ≤ 3` imply the parent flag budget. -/
theorem FunctionFieldBranch.semismallBudget_of_deleteOutside
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (hChild : PlacementBranch.SemismallBudget (k := k)
      (S.deleteOutside v hv)
      ((Y.toPlacement S).deleteOutsidePlacement S v hv))
    (hLocal :
      (outsideResponseKernelDim S.edges Y.position v : Cardinal) +
        outsideExtensionTrdeg (k := k) Y.position v ≤ 3) :
    Y.SemismallBudget S := by
  let child := (Y.toPlacement S).deleteOutsidePlacement S v hv
  have hStress := directionStressDim_eq_delete_add_outsideResponseKernelDim
    S.edges Y.position v
  have hStressC :
      (directionStressDim S.edges Y.position : Cardinal) =
        (directionStressDim (deleteVertexEdges S.edges v) Y.position : Cardinal) +
          (outsideResponseKernelDim S.edges Y.position v : Cardinal) := by
    exact_mod_cast hStress
  have hChildStress :=
    (Y.toPlacement S).deleteOutsidePlacement_stressDim S v hv
  have hChildStress' :
      child.stressDim (S.deleteOutside v hv) =
        directionStressDim (deleteVertexEdges S.edges v) Y.position := by
    simpa [child] using hChildStress
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  have hTower' :
      Algebra.trdeg k (liveCoordinateField (k := k) child.position) +
          outsideExtensionTrdeg (k := k) Y.position v =
        Algebra.trdeg k K := by
    exact hTower
  have hVCard := card_remainingVertex_add_one v
  unfold PlacementBranch.SemismallBudget at hChild
  unfold FunctionFieldBranch.SemismallBudget
  change
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  calc
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) =
        ((child.stressDim (S.deleteOutside v hv) : Cardinal) +
            Algebra.trdeg k
              (liveCoordinateField (k := k) child.position) +
            2 * (Fintype.card Flag : Cardinal)) +
          ((outsideResponseKernelDim S.edges Y.position v : Cardinal) +
            outsideExtensionTrdeg (k := k) Y.position v) := by
      rw [hStressC, ← hChildStress', ← hTower']
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 3 :=
      add_le_add hChild hLocal
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 3 = 3 * Fintype.card V)

/-- **Private nonexceptional budget lift.**  Removing one live vertex and
one flag changes the ambient ledger by `3 - 2 = 1`; hence the transparent
local payment `u + d ≤ 1` is exactly sufficient. -/
theorem FunctionFieldBranch.semismallBudget_of_deletePrivate
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hChild : PlacementBranch.SemismallBudget (k := k)
      (S.deletePrivate v t hOne hvt)
      ((Y.toPlacement S).deletePrivatePlacement S v t hOne hvt))
    (hLocal :
      (outsideResponseKernelDim S.edges Y.position v : Cardinal) +
        outsideExtensionTrdeg (k := k) Y.position v ≤ 1) :
    Y.SemismallBudget S := by
  let child :=
    (Y.toPlacement S).deletePrivatePlacement S v t hOne hvt
  have hStress := directionStressDim_eq_delete_add_outsideResponseKernelDim
    S.edges Y.position v
  have hStressC :
      (directionStressDim S.edges Y.position : Cardinal) =
        (directionStressDim (deleteVertexEdges S.edges v) Y.position : Cardinal) +
          (outsideResponseKernelDim S.edges Y.position v : Cardinal) := by
    exact_mod_cast hStress
  have hChildStress :=
    (Y.toPlacement S).deletePrivatePlacement_stressDim
      S v t hOne hvt
  have hChildStress' :
      child.stressDim (S.deletePrivate v t hOne hvt) =
        directionStressDim (deleteVertexEdges S.edges v) Y.position := by
    simpa [child] using hChildStress
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  have hTower' :
      Algebra.trdeg k (liveCoordinateField (k := k) child.position) +
          outsideExtensionTrdeg (k := k) Y.position v =
        Algebra.trdeg k K := by
    exact hTower
  have hVCard := card_remainingVertex_add_one v
  have hFCard := card_remainingFlag_add_one t
  have hFCardC :
      (Fintype.card (RemainingFlag t) : Cardinal) + 1 =
        (Fintype.card Flag : Cardinal) := by
    exact_mod_cast hFCard
  unfold PlacementBranch.SemismallBudget at hChild
  unfold FunctionFieldBranch.SemismallBudget
  change
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  calc
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) =
        ((child.stressDim (S.deletePrivate v t hOne hvt) : Cardinal) +
            Algebra.trdeg k
              (liveCoordinateField (k := k) child.position) +
            2 * (Fintype.card (RemainingFlag t) : Cardinal)) +
          ((outsideResponseKernelDim S.edges Y.position v : Cardinal) +
            outsideExtensionTrdeg (k := k) Y.position v) + 2 := by
      rw [hStressC, ← hChildStress', ← hTower', ← hFCardC]
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 1 + 2 :=
      add_le_add (add_le_add hChild hLocal) (le_refl 2)
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 1 + 2 =
          3 * Fintype.card V)

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0032

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0032/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0032.json"

section BundleSource0033
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagSemismallness.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagSemismallness.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Strong induction for provenance-flag semismallness

This file proves the common strong-induction step: descent of collinearity to
the intrinsic child coordinate field, construction of coordinate-generated
child branches, the empty-live-vertex base case, low-degree selection, and
the two nonexceptional recursive branches.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-! ## Collinearity descends to a coordinate field -/

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
/-- Three points valued in an intermediate field are already collinear over
that field if their scalar extensions are collinear and the first two are
distinct.  The scalar is the ratio of two retained coordinates, so no
closure or algebraic-geometry descent theorem is assumed. -/
theorem collinear_restrictScalars
    (L : IntermediateField k K)
    (p q r : Fin 3 → L) (hpq : p ≠ q)
    (hcol : PinCollinearity.Collinear
      (fun j ↦ (p j : K)) (fun j ↦ (q j : K)) (fun j ↦ (r j : K))) :
    PinCollinearity.Collinear p q r := by
  have hpqK : (fun j ↦ (p j : K)) ≠ (fun j ↦ (q j : K)) := by
    intro h
    apply hpq
    funext j
    exact Subtype.ext (congrFun h j)
  obtain ⟨s, hs⟩ :=
    (collinear_iff_exists_smul_difference
      (fun j ↦ (p j : K)) (fun j ↦ (q j : K))
      (fun j ↦ (r j : K)) hpqK).1 hcol
  have hCoordinate : ∃ j : Fin 3, q j - p j ≠ 0 := by
    by_contra h
    push Not at h
    apply hpq
    funext j
    exact sub_eq_zero.mp (h j) |>.symm
  obtain ⟨j, hj⟩ := hCoordinate
  let t : L := (r j - p j) / (q j - p j)
  have hsEq : s = (t : K) := by
    have hsj := congrFun hs j
    change (r j : K) - p j = s * ((q j : K) - p j) at hsj
    have hjK : (q j : K) - p j ≠ 0 := by
      intro hzero
      apply hj
      apply Subtype.ext
      exact hzero
    apply (eq_div_iff hjK).2
    exact hsj.symm
  apply (collinear_iff_exists_smul_difference p q r hpq).2
  refine ⟨t, ?_⟩
  funext i
  apply Subtype.ext
  have hi := congrFun hs i
  change (r i : K) - p i = s * ((q i : K) - p i) at hi
  change (r i : K) - p i = (t : K) * ((q i : K) - p i)
  rw [← hsEq]
  exact hi

omit [Fintype V] [Fintype Flag] [DecidableEq Flag] in
/-- A three-element collinear terminal set remains affinely collinear after
restricting all its coordinates to an intermediate field. -/
theorem affinelyCollinearOn_intrinsic
    (L : IntermediateField k K)
    (a : V → Fin 3 → L) (X : Finset V)
    (hCard : X.card = 3)
    (hDistinct : Function.Injective a)
    (hAmbient : AffinelyCollinearOn
      (fun v j ↦ ((a v j : L) : K)) X) :
    AffinelyCollinearOn a X := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hX⟩ := Finset.card_eq_three.mp hCard
  have hp : p ∈ X := by rw [hX]; simp
  have hq : q ∈ X := by rw [hX]; simp
  have hr : r ∈ X := by rw [hX]; simp
  have hpqA : a p ≠ a q := fun h ↦ hpq (hDistinct h)
  have hcolK := pinCollinear_of_affinelyCollinearOn
    (fun v j ↦ ((a v j : L) : K)) X p q r hAmbient hp hq hr
  have hcolL : PinCollinearity.Collinear (a p) (a q) (a r) :=
    collinear_restrictScalars L (a p) (a q) (a r) hpqA hcolK
  obtain ⟨t, ht⟩ :=
    (collinear_iff_exists_smul_difference (a p) (a q) (a r) hpqA).1 hcolL
  refine ⟨a p, a q - a p, ?_⟩
  intro z hz
  rw [hX] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by module⟩
  · refine ⟨t, ?_⟩
    funext i
    have hi := congrFun ht i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination hi

/-! ## Genuine intrinsic child function-field branches -/

/-- The outside-deletion child over the field generated by its own
retained coordinates. -/
def FunctionFieldBranch.deleteOutsideIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0) :
    FunctionFieldBranch
      (k := k) (K := retainedLiveCoordinateField (k := k) Y.position v)
      (S.deleteOutside v hv) where
  position := intrinsicRestrictedPlacement (k := k) Y.position v
  generated := intrinsicRestrictedPlacement_generated (k := k) Y.position v
  distinct := by
    intro a b hab
    apply Subtype.ext
    apply Y.distinct
    funext j
    exact congrArg Subtype.val (congrFun hab j)
  collinear t := by
    let L := retainedLiveCoordinateField (k := k) Y.position v
    let childPosition := intrinsicRestrictedPlacement (k := k) Y.position v
    apply affinelyCollinearOn_intrinsic
      (k := k) (K := K) L childPosition
      ((S.deleteOutside v hv).terminals t)
      ((S.deleteOutside v hv).terminals_card t)
    · intro a b hab
      apply Subtype.ext
      apply Y.distinct
      funext j
      exact congrArg Subtype.val (congrFun hab j)
    · exact (Y.toPlacement S).deleteOutsidePlacement S v hv |>.collinear t

/-- The private-deletion child over its own intrinsic coordinate field. -/
def FunctionFieldBranch.deletePrivateIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    FunctionFieldBranch
      (k := k) (K := retainedLiveCoordinateField (k := k) Y.position v)
      (S.deletePrivate v t hOne hvt) where
  position := intrinsicRestrictedPlacement (k := k) Y.position v
  generated := intrinsicRestrictedPlacement_generated (k := k) Y.position v
  distinct := by
    intro a b hab
    apply Subtype.ext
    apply Y.distinct
    funext j
    exact congrArg Subtype.val (congrFun hab j)
  collinear r := by
    let L := retainedLiveCoordinateField (k := k) Y.position v
    let childPosition := intrinsicRestrictedPlacement (k := k) Y.position v
    apply affinelyCollinearOn_intrinsic
      (k := k) (K := K) L childPosition
      ((S.deletePrivate v t hOne hvt).terminals r)
      ((S.deletePrivate v t hOne hvt).terminals_card r)
    · intro a b hab
      apply Subtype.ext
      apply Y.distinct
      funext j
      exact congrArg Subtype.val (congrFun hab j)
    · exact (Y.toPlacement S).deletePrivatePlacement
        S v t hOne hvt |>.collinear r

/-! ## Intrinsic recursive budgets feed the deletion ledger -/

/-- A recursive budget for the genuine intrinsic outside child is exactly
the intrinsic form of the ambient child placement budget expected by the
outside deletion ledger. -/
theorem FunctionFieldBranch.deleteOutsidePlacement_semismallBudget_of_intrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (hChild :
      (Y.deleteOutsideIntrinsic S v hv).SemismallBudget
        (S.deleteOutside v hv)) :
    PlacementBranch.SemismallBudget (k := k)
      (S.deleteOutside v hv)
      ((Y.toPlacement S).deleteOutsidePlacement S v hv) := by
  apply (PlacementBranch.deleteOutside_semismallBudget_iff_intrinsic
    (k := k) S (Y.toPlacement S) v hv).2
  exact hChild

/-- The corresponding bridge for a private child, whose intrinsic flag
type has already forgotten the consumed flag. -/
theorem FunctionFieldBranch.deletePrivatePlacement_semismallBudget_of_intrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hChild :
      (Y.deletePrivateIntrinsic S v t hOne hvt).SemismallBudget
        (S.deletePrivate v t hOne hvt)) :
    PlacementBranch.SemismallBudget (k := k)
      (S.deletePrivate v t hOne hvt)
      ((Y.toPlacement S).deletePrivatePlacement S v t hOne hvt) := by
  apply (PlacementBranch.deletePrivate_semismallBudget_iff_intrinsic
    (k := k) S (Y.toPlacement S) v t hOne hvt).2
  exact hChild

/-- **Outside nonexceptional induction step.**  This is the complete
recursive branch: intrinsic child semismallness plus the transparent local
nonexceptional condition implies the parent budget. -/
theorem FunctionFieldBranch.semismallBudget_of_deleteOutsideIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (hChild :
      (Y.deleteOutsideIntrinsic S v hv).SemismallBudget
        (S.deleteOutside v hv))
    (hNonexceptional :
      OutsideNonexceptional (k := k) S.edges Y.position v) :
    Y.SemismallBudget S := by
  apply Y.semismallBudget_of_deleteOutside S v hv
    (Y.deleteOutsidePlacement_semismallBudget_of_intrinsic
      S v hv hChild)
  exact outside_local_payment S.edges Y.position v Y.generated hNonexceptional

/-- **Private nonexceptional induction step.**  The removed flag pays two
of the three deleted vertex coordinates, leaving precisely the local
allowance certified by `PrivateNonexceptional`. -/
theorem FunctionFieldBranch.semismallBudget_of_deletePrivateIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hChild :
      (Y.deletePrivateIntrinsic S v t hOne hvt).SemismallBudget
        (S.deletePrivate v t hOne hvt))
    (hNonexceptional :
      PrivateNonexceptional (k := k) S.edges Y.position v) :
    Y.SemismallBudget S := by
  apply Y.semismallBudget_of_deletePrivate S v t hOne hvt
    (Y.deletePrivatePlacement_semismallBudget_of_intrinsic
      S v t hOne hvt hChild)
  exact private_local_payment S.edges Y.position v Y.generated hNonexceptional

/-! ## Empty live-vertex base case -/

/-- If the exact live-vertex type is empty, then the defining properties of the state force the
active flag type to be empty as well.  There are no live edges, and
coordinate generation bounds the function-field transcendence degree by
zero, so the semismall budget follows without sparsity. -/
theorem FunctionFieldBranch.semismallBudget_of_card_live_eq_zero
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (hV : Fintype.card V = 0) :
    Y.SemismallBudget S := by
  have hFlagCard : Fintype.card Flag = 0 := by
    by_contra hFlag
    have hFlagPos : 0 < Fintype.card Flag := Nat.pos_of_ne_zero hFlag
    obtain ⟨t⟩ := Fintype.card_pos_iff.mp hFlagPos
    have hTerminalBound :
        (S.terminals t).card ≤ Fintype.card V := by
      simpa using
        Finset.card_le_card (Finset.subset_univ (S.terminals t))
    rw [S.terminals_card t, hV] at hTerminalBound
    omega
  have hEdgeCard : S.edges.card = 0 := by
    by_contra hEdges
    have hEdgePos : 0 < S.edges.card := Nat.pos_of_ne_zero hEdges
    obtain ⟨e, _he⟩ := Finset.card_pos.mp hEdgePos
    have hVPos : 0 < Fintype.card V :=
      Fintype.card_pos_iff.mpr ⟨e.source⟩
    omega
  have hStress : Y.stressDim S = 0 := by
    have hStressBound :=
      directionStressDim_le_card S.edges Y.position
    unfold FunctionFieldBranch.stressDim
    omega
  have hTrdeg := Y.trdeg_le_ambient S
  unfold FunctionFieldBranch.SemismallBudget
  simpa [hStress, hFlagCard, hV] using hTrdeg

/-! ## Private strong-induction engine -/

/-- The exact recursive resource available at a state with `n` live
vertices.  It ranges over actual function fields, live types, flag types,
states, and coordinate-generated branches in the same universe levels. -/
abbrev SmallerSemismall (k : Type u) [Field k] (n : ℕ) : Prop :=
  ∀ {K : Type v} {V : Type w} {Flag : Type x}
    [Field K] [Algebra k K]
    [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag],
    Fintype.card V < n →
      ∀ (S : State V Flag)
        (Y : FunctionFieldBranch (k := k) (K := K) S),
        S.CompletionSparse → Y.SemismallBudget S

/-- Strong induction parametrized by the two exceptional-step theorems.
The declaration is private; the public theorem supplies both parameters. -/
private theorem FunctionFieldBranch.semismallBudget_strongInduction_engine
    (hOutsideExceptional :
      ∀ {K : Type v} {V : Type w} {Flag : Type x}
        [Field K] [Algebra k K]
        [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]
        (S : State V Flag)
        (Y : FunctionFieldBranch (k := k) (K := K) S)
        (v : V),
        S.CompletionSparse →
        S.flagMultiplicity v = 0 →
        edgeSetDegree S.edges v ≤ 3 →
        SmallerSemismall.{u, v, w, x} (k := k) (Fintype.card V) →
        OutsideExceptional (k := k) S.edges Y.position v →
        Y.SemismallBudget S)
    (hPrivateExceptional :
      ∀ {K : Type v} {V : Type w} {Flag : Type x}
        [Field K] [Algebra k K]
        [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]
        (S : State V Flag)
        (Y : FunctionFieldBranch (k := k) (K := K) S)
        (v : V) (t : Flag),
        S.CompletionSparse →
        S.flagMultiplicity v = 1 →
        v ∈ S.terminals t →
        edgeSetDegree S.edges v ≤ 2 →
        SmallerSemismall.{u, v, w, x} (k := k) (Fintype.card V) →
        PrivateExceptional (k := k) S.edges Y.position v →
        Y.SemismallBudget S)
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (hSparse : S.CompletionSparse) :
    Y.SemismallBudget S := by
  let P : ℕ → Prop := fun n ↦
    ∀ {K : Type v} {V : Type w} {Flag : Type x}
      [Field K] [Algebra k K]
      [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag],
      Fintype.card V = n →
        ∀ (S : State V Flag)
          (Y : FunctionFieldBranch (k := k) (K := K) S),
          S.CompletionSparse → Y.SemismallBudget S
  have hAll : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro K' V' Flag' _instField _instAlgebra
          _instFintypeV _instDecidableV _instFintypeFlag _instDecidableFlag
          hCard S' Y' hSparse'
        have hSmaller :
            SmallerSemismall.{u, v, w, x}
              (k := k) (Fintype.card V') := by
          intro K'' V'' Flag'' _instField'' _instAlgebra''
            _instFintypeV'' _instDecidableV''
            _instFintypeFlag'' _instDecidableFlag''
            hCardLt S'' Y'' hSparse''
          exact ih (Fintype.card V'') (by omega) rfl S'' Y'' hSparse''
        by_cases hZero : Fintype.card V' = 0
        · exact Y'.semismallBudget_of_card_live_eq_zero S' hZero
        have hVPos : 0 < Fintype.card V' := Nat.pos_of_ne_zero hZero
        obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hVPos
        have hUniverse : (Finset.univ : Finset V').Nonempty :=
          ⟨v₀, Finset.mem_univ v₀⟩
        rcases S'.exists_outside_degree_le_three_or_private_degree_le_two
            hSparse' hUniverse with hOutside | hPrivate
        · obtain ⟨v₀, hvOutside, hDegree⟩ := hOutside
          have hChildCard : Fintype.card (RemainingVertex v₀) < n := by
            have hDrop := card_remainingVertex_add_one v₀
            omega
          have hChild :
              (Y'.deleteOutsideIntrinsic S' v₀ hvOutside).SemismallBudget
                (S'.deleteOutside v₀ hvOutside) := by
            exact ih (Fintype.card (RemainingVertex v₀)) hChildCard rfl
              (S'.deleteOutside v₀ hvOutside)
              (Y'.deleteOutsideIntrinsic S' v₀ hvOutside)
              (S'.deleteOutside_completionSparse v₀ hvOutside hSparse')
          rcases outside_nonexceptional_or_exceptional
              (k := k) S'.edges Y'.position v₀ with hPaid | hExceptional
          · exact Y'.semismallBudget_of_deleteOutsideIntrinsic
              S' v₀ hvOutside hChild hPaid
          · exact hOutsideExceptional S' Y' v₀ hSparse' hvOutside hDegree
              hSmaller hExceptional
        · obtain ⟨v₀, hvPrivate, hDegree⟩ := hPrivate
          have hActive : (S'.activeFlagsAt v₀).Nonempty := by
            apply Finset.card_pos.mp
            change 0 < S'.flagMultiplicity v₀
            omega
          obtain ⟨t₀, ht₀⟩ := hActive
          have hvt : v₀ ∈ S'.terminals t₀ :=
            (S'.mem_activeFlagsAt v₀ t₀).1 ht₀
          have hChildCard : Fintype.card (RemainingVertex v₀) < n := by
            have hDrop := card_remainingVertex_add_one v₀
            omega
          have hChild :
              (Y'.deletePrivateIntrinsic S' v₀ t₀ hvPrivate hvt).SemismallBudget
                (S'.deletePrivate v₀ t₀ hvPrivate hvt) := by
            exact ih (Fintype.card (RemainingVertex v₀)) hChildCard rfl
              (S'.deletePrivate v₀ t₀ hvPrivate hvt)
              (Y'.deletePrivateIntrinsic S' v₀ t₀ hvPrivate hvt)
              (S'.deletePrivate_completionSparse
                v₀ t₀ hvPrivate hvt hSparse')
          rcases private_nonexceptional_or_exceptional
              (k := k) S'.edges Y'.position v₀ with hPaid | hExceptional
          · exact Y'.semismallBudget_of_deletePrivateIntrinsic
              S' v₀ t₀ hvPrivate hvt hChild hPaid
          · exact hPrivateExceptional S' Y' v₀ t₀ hSparse' hvPrivate hvt
              hDegree hSmaller hExceptional
  exact hAll (Fintype.card V) rfl S Y hSparse

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0033

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0033/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0033.json"

section BundleSource0034
/- Source: Papers/RigidityZheng_Combinatorics_Sparse22_DegreeThreeAugmentation.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/Sparse22/DegreeThreeAugmentation.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Adding a missing neighbour edge at a sparse degree-three vertex

The inverse-Henneberg lemmas in `Construction` package their conclusion as
a reduction of a *tight* graph.  Provenance-flag induction needs the local
fact before any tight completion: in an arbitrary sparse graph, if the
three neighbours of a degree-three vertex do not span a triangle, at least
one missing neighbour edge is sparse after deleting the vertex.

The proof is a tight-set obstruction and uncrossing argument that does not
require global tightness or a chosen completion.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- If exactly the pair `ab` is missing among the three neighbour pairs,
then it can be inserted after deleting the degree-three vertex. -/
theorem sparse22_insert_missing_neighbor_edge_of_other_two
    {F : SimpleEdgeSet V} {v a b c : V}
    (hSparse : Sparse22 F)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hacF : simpleEdge a c hac ∈ F)
    (hbcF : simpleEdge b c hbc ∈ F) :
    Sparse22
      (insert (simpleEdge a b hab) (deleteVertexEdges F v)) := by
  by_contra hBad
  have hSparseDelete : Sparse22 (deleteVertexEdges F v) :=
    hSparse.mono (deleteVertexEdges_subset F v)
  obtain ⟨Y, hYne, haY, hbY, hvY, hYtight⟩ :=
    exists_tight22_obstruction_of_not_hennebergTwo_admissible
      hva hab hSparseDelete habF hBad
  have hIncidentEq := incidentEdges_eq_three hva hvb hvc hab hac hbc
    hDegree hvaF hvbF hvcF
  have hcY : c ∉ Y := by
    intro hcY
    have hIncidentSupported :
        SupportedOn (incidentEdges F v) (insert v Y) := by
      intro e he
      rw [hIncidentEq] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · rw [vertices_simpleEdge]
        simp [haY]
      · rw [vertices_simpleEdge]
        simp [hbY]
      · rw [vertices_simpleEdge]
        simp [hcY]
    have hCard := card_edgesInside_insert_eq_degree_add
      F Y v hvY hIncidentSupported
    have hSparseZ := hSparse (insert v Y) ⟨v, by simp⟩
    have hZcard : (insert v Y).card = Y.card + 1 := by
      rw [Finset.card_insert_of_notMem hvY]
    rw [hCard, hDegree, hYtight.2, hZcard] at hSparseZ
    have hYpos : 0 < Y.card := Finset.card_pos.mpr hYne
    omega
  let eac : SimpleEdge V := simpleEdge a c hac
  let ebc : SimpleEdge V := simpleEdge b c hbc
  let R : SimpleEdgeSet V := deleteVertexEdges F v
  have eacR : eac ∈ R := by
    rw [mem_deleteVertexEdges]
    refine ⟨hacF, ?_⟩
    rw [vertices_simpleEdge]
    simp [hva, hvc]
  have ebcR : ebc ∈ R := by
    rw [mem_deleteVertexEdges]
    refine ⟨hbcF, ?_⟩
    rw [vertices_simpleEdge]
    simp [hvb, hvc]
  have eacNew : eac ∈ edgesInside R (insert c Y) := by
    rw [mem_edgesInside]
    refine ⟨eacR, ?_⟩
    rw [vertices_simpleEdge]
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_insert_of_mem haY
    · exact Finset.mem_insert_self _ _
  have ebcNew : ebc ∈ edgesInside R (insert c Y) := by
    rw [mem_edgesInside]
    refine ⟨ebcR, ?_⟩
    rw [vertices_simpleEdge]
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_insert_of_mem hbY
    · exact Finset.mem_insert_self _ _
  have hPairCard : ({eac, ebc} : SimpleEdgeSet V).card = 2 := by
    simp [eac, ebc, hab, hac]
  have hPairDisjoint :
      Disjoint (edgesInside R Y) ({eac, ebc} : SimpleEdgeSet V) := by
    rw [Finset.disjoint_left]
    intro e heOld hePair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hePair
    rcases hePair with rfl | rfl
    · exact hcY ((mem_edgesInside.mp heOld).2 (by simp [eac]))
    · exact hcY ((mem_edgesInside.mp heOld).2 (by simp [ebc]))
  have hUnionSubset :
      edgesInside R Y ∪ ({eac, ebc} : SimpleEdgeSet V) ⊆
        edgesInside R (insert c Y) := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with heOld | hePair
    · exact edgesInside_mono_vertices R (Finset.subset_insert c Y) heOld
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hePair
      rcases hePair with rfl | rfl
      · exact eacNew
      · exact ebcNew
  have hDeletedLower :
      (edgesInside R Y).card + 2 ≤
        (edgesInside R (insert c Y)).card := by
    rw [← hPairCard, ← Finset.card_union_of_disjoint hPairDisjoint]
    exact Finset.card_le_card hUnionSubset
  have hvInsertCY : v ∉ insert c Y := by
    simp [hvc, hvY]
  have hIncidentSupported :
      SupportedOn (incidentEdges F v) (insert v (insert c Y)) := by
    intro e he
    rw [hIncidentEq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [vertices_simpleEdge]
      simp [haY]
    · rw [vertices_simpleEdge]
      simp [hbY]
    · rw [vertices_simpleEdge]
      simp
  have hCard := card_edgesInside_insert_eq_degree_add
    F (insert c Y) v hvInsertCY hIncidentSupported
  have hSparseZ := hSparse (insert v (insert c Y)) ⟨v, by simp⟩
  have hCYcard : (insert c Y).card = Y.card + 1 := by
    rw [Finset.card_insert_of_notMem hcY]
  have hZcard : (insert v (insert c Y)).card = Y.card + 2 := by
    rw [Finset.card_insert_of_notMem hvInsertCY, hCYcard]
  rw [hCard, hDegree, hZcard] at hSparseZ
  dsimp [R] at hDeletedLower
  rw [hYtight.2] at hDeletedLower
  have hYpos : 0 < Y.card := Finset.card_pos.mpr hYne
  omega

/-- If two neighbour pairs are missing, at least one of the two can be
inserted after deleting the degree-three vertex. -/
theorem sparse22_insert_one_of_two_missing_neighbor_edges
    {F : SimpleEdgeSet V} {v a b c : V}
    (hSparse : Sparse22 F)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hbcF : simpleEdge b c hbc ∉ F) :
    Sparse22
        (insert (simpleEdge a b hab) (deleteVertexEdges F v)) ∨
      Sparse22
        (insert (simpleEdge b c hbc) (deleteVertexEdges F v)) := by
  have hSparseR : Sparse22 (deleteVertexEdges F v) :=
    hSparse.mono (deleteVertexEdges_subset F v)
  by_cases hAB :
      Sparse22 (insert (simpleEdge a b hab) (deleteVertexEdges F v))
  · exact Or.inl hAB
  by_cases hBC :
      Sparse22 (insert (simpleEdge b c hbc) (deleteVertexEdges F v))
  · exact Or.inr hBC
  obtain ⟨Yab, _hYabNe, haYab, hbYab, hvYab, hYabTight⟩ :=
    exists_tight22_obstruction_of_not_hennebergTwo_admissible
      hva hab hSparseR habF hAB
  obtain ⟨Ybc, _hYbcNe, hbYbc, hcYbc, hvYbc, hYbcTight⟩ :=
    exists_tight22_obstruction_of_not_hennebergTwo_admissible
      hvb hbc hSparseR hbcF hBC
  have hInterNonempty : (Yab ∩ Ybc).Nonempty :=
    ⟨b, Finset.mem_inter.mpr ⟨hbYab, hbYbc⟩⟩
  have hUnionTight : Tight22 (deleteVertexEdges F v) (Yab ∪ Ybc) :=
    (tight22_union_inter hSparseR hYabTight hYbcTight hInterNonempty).1
  have hvUnion : v ∉ Yab ∪ Ybc := by
    simp [hvYab, hvYbc]
  have hIncidentEq := incidentEdges_eq_three hva hvb hvc hab hac hbc
    hDegree hvaF hvbF hvcF
  have hIncidentSupported :
      SupportedOn (incidentEdges F v) (insert v (Yab ∪ Ybc)) := by
    intro e he
    rw [hIncidentEq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [vertices_simpleEdge]
      simp [haYab]
    · rw [vertices_simpleEdge]
      simp [hbYab]
    · rw [vertices_simpleEdge]
      simp [hcYbc]
  have hCard := card_edgesInside_insert_eq_degree_add
    F (Yab ∪ Ybc) v hvUnion hIncidentSupported
  have hSparseZ := hSparse (insert v (Yab ∪ Ybc)) ⟨v, by simp⟩
  have hZcard :
      (insert v (Yab ∪ Ybc)).card = (Yab ∪ Ybc).card + 1 := by
    rw [Finset.card_insert_of_notMem hvUnion]
  rw [hCard, hDegree, hZcard, hUnionTight.2] at hSparseZ
  have hUnionPos : 0 < (Yab ∪ Ybc).card :=
    Finset.card_pos.mpr hUnionTight.1
  omega

/-- Complete local dichotomy for three named neighbours in an arbitrary
sparse graph: they already span their full triangle, or an actually absent
neighbour edge can be inserted after deleting the degree-three vertex. -/
theorem degree_three_neighbour_triangle_complete_or_addable
    {F : SimpleEdgeSet V} {v a b c : V}
    (hSparse : Sparse22 F)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F) :
    (simpleEdge a b hab ∈ F ∧ simpleEdge a c hac ∈ F ∧
        simpleEdge b c hbc ∈ F) ∨
      ∃ e : SimpleEdge V,
        e ∈ ({simpleEdge a b hab, simpleEdge a c hac,
            simpleEdge b c hbc} : SimpleEdgeSet V) ∧
        e ∉ F ∧ Sparse22 (insert e (deleteVertexEdges F v)) := by
  by_cases hAB : simpleEdge a b hab ∈ F
  · by_cases hAC : simpleEdge a c hac ∈ F
    · by_cases hBC : simpleEdge b c hbc ∈ F
      · exact Or.inl ⟨hAB, hAC, hBC⟩
      · right
        refine ⟨simpleEdge b c hbc, by simp, hBC, ?_⟩
        exact sparse22_insert_missing_neighbor_edge_of_other_two
          hSparse hvb hvc hva hbc (Ne.symm hab) (Ne.symm hac)
          hDegree hvbF hvcF hvaF hBC
          (by rw [← simpleEdge_comm a b hab]; exact hAB)
          (by rw [← simpleEdge_comm a c hac]; exact hAC)
    · by_cases hBC : simpleEdge b c hbc ∈ F
      · right
        refine ⟨simpleEdge a c hac, by simp, hAC, ?_⟩
        exact sparse22_insert_missing_neighbor_edge_of_other_two
          hSparse hva hvc hvb hac hab (Ne.symm hbc)
          hDegree hvaF hvcF hvbF hAC hAB
          (by rw [← simpleEdge_comm b c hbc]; exact hBC)
      · rcases sparse22_insert_one_of_two_missing_neighbor_edges
          hSparse hva hvc hvb hac hab (Ne.symm hbc)
          hDegree hvaF hvcF hvbF hAC
          (by rw [← simpleEdge_comm b c hbc]; exact hBC) with
          hAddAC | hAddCB
        · exact Or.inr ⟨simpleEdge a c hac, by simp, hAC, hAddAC⟩
        · refine Or.inr ⟨simpleEdge b c hbc, by simp, hBC, ?_⟩
          rw [simpleEdge_comm c b (Ne.symm hbc)] at hAddCB
          exact hAddCB
  · by_cases hBC : simpleEdge b c hbc ∈ F
    · by_cases hAC : simpleEdge a c hac ∈ F
      · right
        refine ⟨simpleEdge a b hab, by simp, hAB, ?_⟩
        exact sparse22_insert_missing_neighbor_edge_of_other_two
          hSparse hva hvb hvc hab hac hbc
          hDegree hvaF hvbF hvcF hAB hAC hBC
      · rcases sparse22_insert_one_of_two_missing_neighbor_edges
          hSparse hvb hva hvc (Ne.symm hab) hbc hac
          hDegree hvbF hvaF hvcF
          (by rw [simpleEdge_comm b a (Ne.symm hab)]; exact hAB)
          hAC with hAddBA | hAddAC
        · refine Or.inr ⟨simpleEdge a b hab, by simp, hAB, ?_⟩
          rw [simpleEdge_comm b a (Ne.symm hab)] at hAddBA
          exact hAddBA
        · exact Or.inr ⟨simpleEdge a c hac, by simp, hAC, hAddAC⟩
    · rcases sparse22_insert_one_of_two_missing_neighbor_edges
        hSparse hva hvb hvc hab hac hbc
        hDegree hvaF hvbF hvcF hAB hBC with hAddAB | hAddBC
      · exact Or.inr ⟨simpleEdge a b hab, by simp, hAB, hAddAB⟩
      · exact Or.inr ⟨simpleEdge b c hbc, by simp, hBC, hAddBC⟩

end RB31E2E


end
end BundleSource0034

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0034/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0034.json"

section BundleSource0035
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagOutsideMove.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagOutsideMove.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/





@[expose] public section

/-!
# The combinatorial outside move for provenance flags

An outside live vertex belongs to no active terminal triple.  Consequently
its incidence packet in the completed graph is exactly the lift of its live
incidence packet.  This file proves that equality and applies the arbitrary
sparse degree-three augmentation theorem to the literal completion.

The conclusion is deliberately stated in the completed graph.  It says
that the three lifted neighbours already span a complete triangle, or
returns a genuinely absent completion edge whose insertion after deleting
the outside vertex remains sparse.  Subsequent state constructors may then
either register the complete triangle as a new flag or transport the
addable edge to the outside child.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The canonical inclusion of live vertices into the completion. -/
def completionLiveEmbedding : V ↪ V ⊕ Flag where
  toFun := Sum.inl
  inj' := Sum.inl_injective

omit [Fintype V] [Fintype Flag] in
@[simp]
theorem inl_mem_liftLiveEdge_vertices
    (v : V) (e : SimpleEdge V) :
    Sum.inl v ∈ (liftLiveEdge (Flag := Flag) e).vertices ↔
      v ∈ e.vertices := by
  induction e.1 using Sym2.inductionOn with
  | _ a b =>
      simp [liftLiveEdge, SimpleEdge.vertices]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
@[simp]
theorem liftLiveEdge_eq_mapSimpleEdge (e : SimpleEdge V) :
    liftLiveEdge (Flag := Flag) e =
      Sparse22Transport.mapSimpleEdge
        (completionLiveEmbedding (V := V) (Flag := Flag)) e := by
  rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
/-- Lifting a named live pair is the identically named pair of left-sum
vertices. -/
theorem liftLiveEdge_simpleEdge
    (a b : V) (hab : a ≠ b) :
    liftLiveEdge (Flag := Flag) (simpleEdge a b hab) =
      simpleEdge (Sum.inl a) (Sum.inl b) (by simpa using hab) := by
  rfl

/-- At an outside vertex the completed incidence packet contains no
restored flag edge and no ghost-star edge. -/
theorem State.incidentEdges_completion_outside
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0) :
    incidentEdges S.completionEdges (Sum.inl v) =
      (incidentEdges S.edges v).map
        (liftLiveEdgeEmbedding (V := V) (Flag := Flag)) := by
  ext e
  constructor
  · intro he
    have heData := mem_incidentEdges.mp he
    rw [State.completionEdges] at heData
    rcases Finset.mem_union.mp heData.1 with heLM | heGhost
    · rcases Finset.mem_union.mp heLM with heLive | heMissing
      · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp heLive
        apply Finset.mem_map.mpr
        refine ⟨f, ?_, rfl⟩
        exact mem_incidentEdges.mpr
          ⟨hf, (inl_mem_liftLiveEdge_vertices
            (Flag := Flag) v f).1 heData.2⟩
      · obtain ⟨t, _ht, hte⟩ := Finset.mem_image.mp heMissing
        subst e
        have hvMissing : v ∈ (S.missing t).vertices :=
          (inl_mem_liftLiveEdge_vertices
            (Flag := Flag) v (S.missing t)).1 heData.2
        exact (outside_not_mem_missing_vertices S v hv t hvMissing).elim
    · obtain ⟨t, _ht, heStar⟩ := Finset.mem_biUnion.mp heGhost
      obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp heStar
      subst e
      have hvu : v = u := by
        simpa [vertices_ghostEdge] using heData.2
      subst u
      exact (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t hu).elim
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    apply mem_incidentEdges.mpr
    constructor
    · apply S.liftedLiveEdges_subset_completionEdges
      exact Finset.mem_map.mpr
        ⟨f, (mem_incidentEdges.mp hf).1, rfl⟩
    · exact (inl_mem_liftLiveEdge_vertices
        (Flag := Flag) v f).2 (mem_incidentEdges.mp hf).2

/-- In particular, live degree and completed degree agree at an outside
vertex. -/
theorem State.edgeSetDegree_completion_outside
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0) :
    edgeSetDegree S.completionEdges (Sum.inl v) =
      edgeSetDegree S.edges v := by
  rw [edgeSetDegree, S.incidentEdges_completion_outside v hv,
    Finset.card_map]
  rfl

/-- Lift a named degree-three neighbour packet from the live graph to the
literal completion. -/
def liftDegreeThreeNeighbours
    (S : State V Flag) {v : V}
    (N : DirectionStress.DegreeThreeNeighbours S.edges v) :
    DirectionStress.DegreeThreeNeighbours S.completionEdges (Sum.inl v) where
  p := Sum.inl N.p
  q := Sum.inl N.q
  r := Sum.inl N.r
  hvp := by simp [N.hvp]
  hvq := by simp [N.hvq]
  hvr := by simp [N.hvr]
  hpq := by simp [N.hpq]
  hpr := by simp [N.hpr]
  hqr := by simp [N.hqr]
  vp_mem := by
    change liftLiveEdge (Flag := Flag) (simpleEdge v N.p N.hvp) ∈
      S.completionEdges
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact N.vp_mem
  vq_mem := by
    change liftLiveEdge (Flag := Flag) (simpleEdge v N.q N.hvq) ∈
      S.completionEdges
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact N.vq_mem
  vr_mem := by
    change liftLiveEdge (Flag := Flag) (simpleEdge v N.r N.hvr) ∈
      S.completionEdges
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact N.vr_mem

/-- The exact complete-or-addable alternative in the completed graph at
an outside degree-three vertex. -/
theorem State.outside_neighbour_triangle_complete_or_addable
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hDegree : edgeSetDegree S.edges v = 3) :
    let Nhat := liftDegreeThreeNeighbours S N
    (simpleEdge Nhat.p Nhat.q Nhat.hpq ∈ S.completionEdges ∧
        simpleEdge Nhat.p Nhat.r Nhat.hpr ∈ S.completionEdges ∧
        simpleEdge Nhat.q Nhat.r Nhat.hqr ∈ S.completionEdges) ∨
      ∃ e : SimpleEdge (V ⊕ Flag),
        e ∈ ({simpleEdge Nhat.p Nhat.q Nhat.hpq,
            simpleEdge Nhat.p Nhat.r Nhat.hpr,
            simpleEdge Nhat.q Nhat.r Nhat.hqr} :
              SimpleEdgeSet (V ⊕ Flag)) ∧
        e ∉ S.completionEdges ∧
        Sparse22
          (insert e
            (deleteVertexEdges S.completionEdges (Sum.inl v))) := by
  let Nhat := liftDegreeThreeNeighbours S N
  have hDegreeHat : edgeSetDegree S.completionEdges (Sum.inl v) = 3 := by
    rw [S.edgeSetDegree_completion_outside v hv]
    exact hDegree
  simpa only [Nhat] using
    (degree_three_neighbour_triangle_complete_or_addable
      (F := S.completionEdges) (v := Sum.inl v)
      (a := Nhat.p) (b := Nhat.q) (c := Nhat.r)
      hSparse Nhat.hvp Nhat.hvq Nhat.hvr
      Nhat.hpq Nhat.hpr Nhat.hqr hDegreeHat
      Nhat.vp_mem Nhat.vq_mem Nhat.vr_mem)

/-- The same alternative with an addable edge returned in the original
live vertex type. -/
theorem State.outside_live_neighbour_triangle_complete_or_addable
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hDegree : edgeSetDegree S.edges v = 3) :
    (liftLiveEdge (Flag := Flag) (simpleEdge N.p N.q N.hpq) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.p N.r N.hpr) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.q N.r N.hqr) ∈
          S.completionEdges) ∨
      ∃ f : SimpleEdge V,
        f ∈ ({simpleEdge N.p N.q N.hpq,
            simpleEdge N.p N.r N.hpr,
            simpleEdge N.q N.r N.hqr} : SimpleEdgeSet V) ∧
        liftLiveEdge (Flag := Flag) f ∉ S.completionEdges ∧
        Sparse22
          (insert (liftLiveEdge (Flag := Flag) f)
            (deleteVertexEdges S.completionEdges (Sum.inl v))) := by
  rcases S.outside_neighbour_triangle_complete_or_addable
      hSparse v hv N hDegree with hComplete | hAdd
  · left
    simpa only [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using hComplete
  · obtain ⟨e, heTriangle, heAbsent, heSparse⟩ := hAdd
    simp only [Finset.mem_insert, Finset.mem_singleton] at heTriangle
    rcases heTriangle with he | he | he
    · subst e
      refine Or.inr ⟨simpleEdge N.p N.q N.hpq, by simp, ?_, ?_⟩
      · simpa only [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heAbsent
      · simpa only [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heSparse
    · subst e
      refine Or.inr ⟨simpleEdge N.p N.r N.hpr, by simp, ?_, ?_⟩
      · simpa only [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heAbsent
      · simpa only [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heSparse
    · subst e
      refine Or.inr ⟨simpleEdge N.q N.r N.hqr, by simp, ?_, ?_⟩
      · simpa only [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heAbsent
      · simpa only [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heSparse

/-- A mapped edge of the outside child cannot meet the deleted live vertex
in the parent completion. -/
theorem deletedOutside_not_mem_mappedCompletionEdge
    (v : V) (e : SimpleEdge (RemainingVertex v ⊕ Flag)) :
    Sum.inl v ∉
      (Sparse22Transport.mapSimpleEdge
        (remainingCompletionEmbedding (Flag := Flag) v) e).vertices := by
  intro hvEdge
  have hsub := Sparse22Transport.mapSimpleEdge_vertices_subset
    (remainingCompletionEmbedding (Flag := Flag) v) e
    (Finset.univ : Finset (RemainingVertex v ⊕ Flag)) (by simp)
  have hvRange := hsub hvEdge
  obtain ⟨x, _hx, hxv⟩ := Finset.mem_map.mp hvRange
  cases x with
  | inl u =>
      change Sum.inl (u.1 : V) = Sum.inl v at hxv
      exact u.2 (Sum.inl.inj hxv)
  | inr t =>
      change Sum.inr t = Sum.inl v at hxv
      exact Sum.inr_ne_inl hxv

/-- The mapped outside-child completion lies in the parent completion with
the deleted live vertex removed. -/
theorem State.map_deleteOutside_completionEdges_subset_delete
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0) :
    Sparse22Transport.mapEdgeSet
        (remainingCompletionEmbedding (Flag := Flag) v)
        (S.deleteOutside v hv).completionEdges ⊆
      deleteVertexEdges S.completionEdges (Sum.inl v) := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  exact mem_deleteVertexEdges.mpr
    ⟨map_deleteOutside_completionEdges_subset S v hv
        (Finset.mem_map.mpr ⟨g, hg, rfl⟩),
      deletedOutside_not_mem_mappedCompletionEdge v g⟩

omit [Fintype V] [Fintype Flag] [DecidableEq Flag] in
/-- Mapping a lifted restricted live edge into the parent completion
recovers the original lifted live edge. -/
theorem map_lift_restrictSimpleEdge_remaining
    (v : V) (e : SimpleEdge V) (hve : v ∉ e.vertices) :
    Sparse22Transport.mapSimpleEdge
        (remainingCompletionEmbedding (Flag := Flag) v)
        (liftLiveEdge (Flag := Flag) (restrictSimpleEdge v e hve)) =
      liftLiveEdge (Flag := Flag) e := by
  calc
    _ = liftLiveEdge (Flag := Flag)
          (Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
            (restrictSimpleEdge v e hve)) := by
      apply Subtype.ext
      simp only [Sparse22Transport.mapSimpleEdge_val, liftLiveEdge_val,
        Sym2.map_map]
      induction (restrictSimpleEdge v e hve).1 using Sym2.inductionOn with
      | _ a b =>
          simp [remainingCompletionEmbedding, remainingVertexEmbedding]
    _ = liftLiveEdge (Flag := Flag) e := by
      rw [map_restrictSimpleEdge]

/-- Insert a certified addable completion edge into the outside child.
The child state and its sparse completion are constructed literally. -/
theorem State.exists_insertedOutsideChild_of_addable
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hfAbsent : liftLiveEdge (Flag := Flag) f ∉ S.completionEdges)
    (hSparse : Sparse22
      (insert (liftLiveEdge (Flag := Flag) f)
        (deleteVertexEdges S.completionEdges (Sum.inl v)))) :
    ∃ heMissing : ∀ t : Flag,
        restrictSimpleEdge v f hvf ≠ (S.deleteOutside v hv).missing t,
      ((S.deleteOutside v hv).insertLiveEdge
        (restrictSimpleEdge v f hvf) heMissing).CompletionSparse := by
  have hfMissingParent : ∀ t : Flag, f ≠ S.missing t := by
    intro t hft
    subst f
    exact hfAbsent (S.lifted_missing_mem_completionEdges t)
  have heMissing : ∀ t : Flag,
      restrictSimpleEdge v f hvf ≠ (S.deleteOutside v hv).missing t := by
    intro t hEq
    apply hfMissingParent t
    have hmap := congrArg
      (Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)) hEq
    change Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
        (restrictSimpleEdge v f hvf) =
      Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
        (restrictSimpleEdge v (S.missing t)
          (outside_not_mem_missing_vertices S v hv t)) at hmap
    simpa only [map_restrictSimpleEdge] using hmap
  refine ⟨heMissing, ?_⟩
  apply Sparse22Transport.sparse22_of_mapEdgeSet_subset
    (remainingCompletionEmbedding (Flag := Flag) v) hSparse
  intro e he
  rw [(S.deleteOutside v hv).completionEdges_insertLiveEdge] at he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  rw [Finset.mem_insert] at hg
  rcases hg with rfl | hgOld
  · change Sparse22Transport.mapSimpleEdge
      (remainingCompletionEmbedding (Flag := Flag) v)
      (liftLiveEdge (Flag := Flag) (restrictSimpleEdge v f hvf)) ∈ _
    rw [map_lift_restrictSimpleEdge_remaining]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (S.map_deleteOutside_completionEdges_subset_delete v hv
        (Finset.mem_map.mpr ⟨g, hgOld, rfl⟩))

omit [Fintype V] in
/-- Every neighbour-pair returned by a named degree-three packet avoids
the apex. -/
theorem not_mem_degreeThreeNeighbourPair
    {F : SimpleEdgeSet V} {v : V}
    (N : DirectionStress.DegreeThreeNeighbours F v)
    (f : SimpleEdge V)
    (hf : f ∈ ({simpleEdge N.p N.q N.hpq,
      simpleEdge N.p N.r N.hpr,
      simpleEdge N.q N.r N.hqr} : SimpleEdgeSet V)) :
    v ∉ f.vertices := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl <;>
    simp [vertices_simpleEdge, N.hvp, N.hvq, N.hvr]

/-- Outside complete-or-addable transition with the addable branch already
packaged as an actual smaller sparse flag state. -/
theorem State.outside_complete_or_exists_sparse_insertedChild
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hDegree : edgeSetDegree S.edges v = 3) :
    (liftLiveEdge (Flag := Flag) (simpleEdge N.p N.q N.hpq) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.p N.r N.hpr) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.q N.r N.hqr) ∈
          S.completionEdges) ∨
      ∃ (f : SimpleEdge V)
          (hfTriangle : f ∈ ({simpleEdge N.p N.q N.hpq,
            simpleEdge N.p N.r N.hpr,
            simpleEdge N.q N.r N.hqr} : SimpleEdgeSet V))
          (heMissing : ∀ t : Flag,
            restrictSimpleEdge v f
                (not_mem_degreeThreeNeighbourPair N f hfTriangle) ≠
              (S.deleteOutside v hv).missing t),
        liftLiveEdge (Flag := Flag) f ∉ S.completionEdges ∧
          ((S.deleteOutside v hv).insertLiveEdge
            (restrictSimpleEdge v f
              (not_mem_degreeThreeNeighbourPair N f hfTriangle))
            heMissing).CompletionSparse := by
  rcases S.outside_live_neighbour_triangle_complete_or_addable
      hSparse v hv N hDegree with hComplete | hAdd
  · exact Or.inl hComplete
  · obtain ⟨f, hfTriangle, hfAbsent, hfSparse⟩ := hAdd
    let hvf := not_mem_degreeThreeNeighbourPair N f hfTriangle
    obtain ⟨heMissing, hChildSparse⟩ :=
      S.exists_insertedOutsideChild_of_addable
        v hv f hvf hfAbsent hfSparse
    exact Or.inr ⟨f, hfTriangle, heMissing, hfAbsent, hChildSparse⟩

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0035

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0035/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0035.json"

section BundleSource0036
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagOutsideRegistration.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagOutsideRegistration.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Registering an outside complete triangle as a new provenance flag

The complete branch of the outside move is only usable if the three
neighbour edges in the completion are genuine live edges.  This file first
proves that fact.  If one of them were a restored edge of an old flag, the
old completed `K₄` is tight.  Adding the outside apex acquires two edges;
adding the third neighbour then acquires three, contradicting `(2,2)`
sparsity.

The subsequent state constructor will replace the deleted outside apex by
the private ghost of a new flag.  No provenance conclusion is assumed as a
field of `State`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- Two named distinct edges give a two-edge lower bound. -/
private theorem two_le_card_of_pair_subset
    {W : Type*} [DecidableEq W] {F : SimpleEdgeSet W}
    {e f : SimpleEdge W} (hef : e ≠ f)
    (hsub : ({e, f} : SimpleEdgeSet W) ⊆ F) :
    2 ≤ F.card := by
  have hcard : ({e, f} : SimpleEdgeSet W).card = 2 := by simp [hef]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Three named pairwise distinct edges give a three-edge lower bound. -/
private theorem three_le_card_of_triple_subset
    {W : Type*} [DecidableEq W] {F : SimpleEdgeSet W}
    {e f g : SimpleEdge W}
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hsub : ({e, f, g} : SimpleEdgeSet W) ⊆ F) :
    3 ≤ F.card := by
  have hcard : ({e, f, g} : SimpleEdgeSet W).card = 3 := by
    simp [hef, heg, hfg]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Two neighbours of a completed outside degree-three apex cannot both
belong to one already active terminal triple. -/
theorem State.outside_complete_pair_not_both_terminals
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v a b c : V)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvOutside : S.flagMultiplicity v = 0)
    (hvaLive : simpleEdge v a hva ∈ S.edges)
    (hvbLive : simpleEdge v b hvb ∈ S.edges)
    (hvcLive : simpleEdge v c hvc ∈ S.edges)
    (hacComplete : liftLiveEdge (Flag := Flag) (simpleEdge a c hac) ∈
      S.completionEdges)
    (hbcComplete : liftLiveEdge (Flag := Flag) (simpleEdge b c hbc) ∈
      S.completionEdges)
    (t : Flag) (haT : a ∈ S.terminals t) (hbT : b ∈ S.terminals t) :
    False := by
  let K : Finset (V ⊕ Flag) := S.flagVertices t
  have hKTight : Tight22 S.completionEdges K :=
    S.flagVertices_tight hSparse t
  have hvK : Sum.inl v ∉ K := by
    intro hv
    exact (not_mem_terminals_of_flagMultiplicity_eq_zero S v hvOutside t)
      ((S.mem_flagVertices_live t v).1 hv)
  have haK : Sum.inl a ∈ K := (S.mem_flagVertices_live t a).2 haT
  have hbK : Sum.inl b ∈ K := (S.mem_flagVertices_live t b).2 hbT
  let eva : SimpleEdge (V ⊕ Flag) :=
    simpleEdge (Sum.inl v) (Sum.inl a) (by simpa using hva)
  let evb : SimpleEdge (V ⊕ Flag) :=
    simpleEdge (Sum.inl v) (Sum.inl b) (by simpa using hvb)
  let evc : SimpleEdge (V ⊕ Flag) :=
    simpleEdge (Sum.inl v) (Sum.inl c) (by simpa using hvc)
  have hvaCompletion : eva ∈ S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    change liftLiveEdge (Flag := Flag) (simpleEdge v a hva) ∈
      S.liftedLiveEdges
    rw [S.mem_liftedLiveEdges]
    exact hvaLive
  have hvbCompletion : evb ∈ S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    change liftLiveEdge (Flag := Flag) (simpleEdge v b hvb) ∈
      S.liftedLiveEdges
    rw [S.mem_liftedLiveEdges]
    exact hvbLive
  have hvcCompletion : evc ∈ S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    change liftLiveEdge (Flag := Flag) (simpleEdge v c hvc) ∈
      S.liftedLiveEdges
    rw [S.mem_liftedLiveEdges]
    exact hvcLive
  have hvaNew : eva ∈ newEdgesAt S.completionEdges K (Sum.inl v) := by
    rw [mem_newEdgesAt]
    refine ⟨hvaCompletion, ?_, ?_⟩
    · rw [vertices_simpleEdge]
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem haK⟩
    · intro hsub
      exact hvK (hsub (by rw [vertices_simpleEdge]; simp))
  have hvbNew : evb ∈ newEdgesAt S.completionEdges K (Sum.inl v) := by
    rw [mem_newEdgesAt]
    refine ⟨hvbCompletion, ?_, ?_⟩
    · rw [vertices_simpleEdge]
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hbK⟩
    · intro hsub
      exact hvK (hsub (by rw [vertices_simpleEdge]; simp))
  have hevaevb : eva ≠ evb := by
    simp [eva, evb, simpleEdge_eq_simpleEdge_iff, hab, hvb]
  have hTwoLower :
      2 ≤ (newEdgesAt S.completionEdges K (Sum.inl v)).card :=
    two_le_card_of_pair_subset hevaevb (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hvaNew
      · exact hvbNew)
  have hTwoUpper := card_newEdgesAt_le_two hSparse hKTight hvK
  have hTwo :
      (newEdgesAt S.completionEdges K (Sum.inl v)).card = 2 := by omega
  by_cases hcK : Sum.inl c ∈ K
  · have hvcNew : evc ∈ newEdgesAt S.completionEdges K (Sum.inl v) := by
      rw [mem_newEdgesAt]
      refine ⟨hvcCompletion, ?_, ?_⟩
      · rw [vertices_simpleEdge]
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hcK⟩
      · intro hsub
        exact hvK (hsub (by rw [vertices_simpleEdge]; simp))
    have hevac : eva ≠ evc := by
      simp [eva, evc, simpleEdge_eq_simpleEdge_iff, hac, hvc]
    have hevbc : evb ≠ evc := by
      simp [evb, evc, simpleEdge_eq_simpleEdge_iff, hbc, hvc]
    have hThree :
        3 ≤ (newEdgesAt S.completionEdges K (Sum.inl v)).card :=
      three_le_card_of_triple_subset hevaevb hevac hevbc (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hvaNew
        · exact hvbNew
        · exact hvcNew)
    omega
  · let K' := insert (Sum.inl v) K
    have hK'Tight : Tight22 S.completionEdges K' :=
      tight22_insert_of_card_newEdgesAt_eq_two hKTight hvK hTwo
    have hcK' : Sum.inl c ∉ K' := by simp [K', hcK, hvc.symm]
    let eca : SimpleEdge (V ⊕ Flag) :=
      simpleEdge (Sum.inl c) (Sum.inl a) (by simpa using hac.symm)
    let ecb : SimpleEdge (V ⊕ Flag) :=
      simpleEdge (Sum.inl c) (Sum.inl b) (by simpa using hbc.symm)
    let ecv : SimpleEdge (V ⊕ Flag) :=
      simpleEdge (Sum.inl c) (Sum.inl v) (by simpa using hvc.symm)
    have hcaCompletion : eca ∈ S.completionEdges := by
      change simpleEdge (Sum.inl c) (Sum.inl a) (by simpa using hac.symm) ∈ _
      rw [simpleEdge_comm]
      simpa only [liftLiveEdge_simpleEdge] using hacComplete
    have hcbCompletion : ecb ∈ S.completionEdges := by
      change simpleEdge (Sum.inl c) (Sum.inl b) (by simpa using hbc.symm) ∈ _
      rw [simpleEdge_comm]
      simpa only [liftLiveEdge_simpleEdge] using hbcComplete
    have hcvCompletion : ecv ∈ S.completionEdges := by
      change simpleEdge (Sum.inl c) (Sum.inl v) (by simpa using hvc.symm) ∈ _
      rw [simpleEdge_comm]
      exact hvcCompletion
    have edgeFromCNew (x : V) (hcx : c ≠ x)
        (hxK' : Sum.inl x ∈ K')
        (hmem : simpleEdge (Sum.inl c) (Sum.inl x)
          (by simpa using hcx) ∈ S.completionEdges) :
        simpleEdge (Sum.inl c) (Sum.inl x)
            (by simpa using hcx) ∈
          newEdgesAt S.completionEdges K' (Sum.inl c) := by
      rw [mem_newEdgesAt]
      refine ⟨hmem, ?_, ?_⟩
      · rw [vertices_simpleEdge]
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hxK'⟩
      · intro hsub
        exact hcK' (hsub (by rw [vertices_simpleEdge]; simp))
    have hcaNew : eca ∈ newEdgesAt S.completionEdges K' (Sum.inl c) :=
      edgeFromCNew a hac.symm (by simp [K', haK]) hcaCompletion
    have hcbNew : ecb ∈ newEdgesAt S.completionEdges K' (Sum.inl c) :=
      edgeFromCNew b hbc.symm (by simp [K', hbK]) hcbCompletion
    have hcvNew : ecv ∈ newEdgesAt S.completionEdges K' (Sum.inl c) :=
      edgeFromCNew v hvc.symm (by simp [K']) hcvCompletion
    have hca_cb : eca ≠ ecb := by
      simp [eca, ecb, simpleEdge_eq_simpleEdge_iff, hab, hbc.symm]
    have hca_cv : eca ≠ ecv := by
      simp [eca, ecv, simpleEdge_eq_simpleEdge_iff, hvc.symm, hva.symm]
    have hcb_cv : ecb ≠ ecv := by
      simp [ecb, ecv, simpleEdge_eq_simpleEdge_iff, hvc.symm, hvb.symm]
    have hThree :
        3 ≤ (newEdgesAt S.completionEdges K' (Sum.inl c)).card :=
      three_le_card_of_triple_subset hca_cb hca_cv hcb_cv (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hcaNew
        · exact hcbNew
        · exact hcvNew)
    have hAtMostTwo := card_newEdgesAt_le_two hSparse hK'Tight hcK'
    omega

/-- In particular, a completed neighbour pair cannot be the restored
missing edge of an old flag. -/
theorem State.outside_complete_pair_ne_missing
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v a b c : V)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvOutside : S.flagMultiplicity v = 0)
    (hvaLive : simpleEdge v a hva ∈ S.edges)
    (hvbLive : simpleEdge v b hvb ∈ S.edges)
    (hvcLive : simpleEdge v c hvc ∈ S.edges)
    (hacComplete : liftLiveEdge (Flag := Flag) (simpleEdge a c hac) ∈
      S.completionEdges)
    (hbcComplete : liftLiveEdge (Flag := Flag) (simpleEdge b c hbc) ∈
      S.completionEdges)
    (t : Flag) :
    simpleEdge a b hab ≠ S.missing t := by
  intro habMissing
  apply S.outside_complete_pair_not_both_terminals hSparse v a b c
    hva hvb hvc hab hac hbc hvOutside hvaLive hvbLive hvcLive
    hacComplete hbcComplete t
  · apply S.missing_supported t
    rw [← habMissing, vertices_simpleEdge]
    simp
  · apply S.missing_supported t
    rw [← habMissing, vertices_simpleEdge]
    simp

/-- Hence every completed edge of the outside neighbour triangle is live. -/
theorem State.outside_complete_triangle_live
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hComplete :
      liftLiveEdge (Flag := Flag) (simpleEdge N.p N.q N.hpq) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.p N.r N.hpr) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.q N.r N.hqr) ∈
          S.completionEdges) :
    simpleEdge N.p N.q N.hpq ∈ S.edges ∧
      simpleEdge N.p N.r N.hpr ∈ S.edges ∧
      simpleEdge N.q N.r N.hqr ∈ S.edges := by
  have pairLive (a b c : V)
      (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hvaLive : simpleEdge v a hva ∈ S.edges)
      (hvbLive : simpleEdge v b hvb ∈ S.edges)
      (hvcLive : simpleEdge v c hvc ∈ S.edges)
      (habComplete : liftLiveEdge (Flag := Flag) (simpleEdge a b hab) ∈
        S.completionEdges)
      (hacComplete : liftLiveEdge (Flag := Flag) (simpleEdge a c hac) ∈
        S.completionEdges)
      (hbcComplete : liftLiveEdge (Flag := Flag) (simpleEdge b c hbc) ∈
        S.completionEdges) :
      simpleEdge a b hab ∈ S.edges := by
    rw [State.completionEdges] at habComplete
    rcases Finset.mem_union.mp habComplete with habLM | habGhost
    · rcases Finset.mem_union.mp habLM with habLive | habMissing
      · exact (S.mem_liftedLiveEdges _).1 habLive
      · obtain ⟨t, _ht, htEq⟩ := Finset.mem_image.mp habMissing
        have hEq : simpleEdge a b hab = S.missing t :=
          liftLiveEdge_injective htEq.symm
        exact (S.outside_complete_pair_ne_missing hSparse v a b c
          hva hvb hvc hab hac hbc hvOutside hvaLive hvbLive hvcLive
          hacComplete hbcComplete t hEq).elim
    · obtain ⟨t, _ht, hstar⟩ := Finset.mem_biUnion.mp habGhost
      obtain ⟨x, _hx, hEq⟩ := Finset.mem_image.mp hstar
      have hVertices := congrArg SimpleEdge.vertices hEq
      rw [vertices_ghostEdge, liftLiveEdge_simpleEdge,
        vertices_simpleEdge] at hVertices
      have : Sum.inr t ∈ ({Sum.inl a, Sum.inl b} : Finset (V ⊕ Flag)) := by
        rw [← hVertices]
        simp
      simp at this
  refine ⟨?_, ?_, ?_⟩
  · exact pairLive N.p N.q N.r N.hvp N.hvq N.hvr
      N.hpq N.hpr N.hqr N.vp_mem N.vq_mem N.vr_mem
      hComplete.1 hComplete.2.1 hComplete.2.2
  · exact pairLive N.p N.r N.q N.hvp N.hvr N.hvq
      N.hpr N.hpq N.hqr.symm N.vp_mem N.vr_mem N.vq_mem
      hComplete.2.1 hComplete.1
      (by rw [simpleEdge_comm]; exact hComplete.2.2)
  · exact pairLive N.q N.r N.p N.hvq N.hvr N.hvp
      N.hqr N.hpq.symm N.hpr.symm N.vq_mem N.vr_mem N.vp_mem
      hComplete.2.2
      (by rw [simpleEdge_comm]; exact hComplete.1)
      (by rw [simpleEdge_comm]; exact hComplete.2.1)

/-! ## Literal registration of the new outside flag -/

/-- After deleting the outside apex, the three retained neighbours form
the terminal set of the newly registered flag. -/
def State.registerOutside
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges) :
    State (RemainingVertex v) (Flag ⊕ Unit) where
  edges := (restrictedLiveEdges S.edges v).erase
    (restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
      (not_mem_degreeThreeNeighbourPair N _ (by simp)))
  terminals
    | Sum.inl t => (S.deleteOutside v hvOutside).terminals t
    | Sum.inr _ =>
        {⟨N.p, N.hvp.symm⟩, ⟨N.q, N.hvq.symm⟩, ⟨N.r, N.hvr.symm⟩}
  missing
    | Sum.inl t => (S.deleteOutside v hvOutside).missing t
    | Sum.inr _ => restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
        (not_mem_degreeThreeNeighbourPair N _ (by simp))
  terminals_card
    | Sum.inl t => (S.deleteOutside v hvOutside).terminals_card t
    | Sum.inr _ => by simp [N.hpq, N.hpr, N.hqr]
  missing_supported
    | Sum.inl t => (S.deleteOutside v hvOutside).missing_supported t
    | Sum.inr _ => by
        intro x hx
        rw [mem_restrictSimpleEdge_vertices_iff] at hx
        rw [vertices_simpleEdge] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with hx | hx
        · left
          exact Subtype.ext hx
        · right; left
          exact Subtype.ext hx
  missing_not_live
    | Sum.inl t => by
        exact Finset.not_mem_subset (Finset.erase_subset _ _)
          ((S.deleteOutside v hvOutside).missing_not_live t)
    | Sum.inr _ => by simp
  other_terminal_edges_live
    | Sum.inl t => fun e heT heMissing ↦ by
        apply Finset.mem_erase.mpr
        refine ⟨?_, (S.deleteOutside v hvOutside).other_terminal_edges_live
          t e heT heMissing⟩
        intro heq
        have hpChild : (⟨N.p, N.hvp.symm⟩ : RemainingVertex v) ∈
            e.vertices := by
          rw [heq, mem_restrictSimpleEdge_vertices_iff,
            vertices_simpleEdge]
          simp
        have hqChild : (⟨N.q, N.hvq.symm⟩ : RemainingVertex v) ∈
            e.vertices := by
          rw [heq, mem_restrictSimpleEdge_vertices_iff,
            vertices_simpleEdge]
          simp
        have hpTChild := heT hpChild
        have hqTChild := heT hqChild
        have hpT : N.p ∈ S.terminals t :=
          (mem_restrictVertexSet_iff v (S.terminals t)
            (not_mem_terminals_of_flagMultiplicity_eq_zero
              S v hvOutside t) _).1 hpTChild
        have hqT : N.q ∈ S.terminals t :=
          (mem_restrictVertexSet_iff v (S.terminals t)
            (not_mem_terminals_of_flagMultiplicity_eq_zero
              S v hvOutside t) _).1 hqTChild
        have hprComplete : liftLiveEdge (Flag := Flag)
            (simpleEdge N.p N.r N.hpr) ∈ S.completionEdges := by
          apply S.liftedLiveEdges_subset_completionEdges
          rw [S.mem_liftedLiveEdges]
          exact hTriangleLive.2.1
        have hqrComplete : liftLiveEdge (Flag := Flag)
            (simpleEdge N.q N.r N.hqr) ∈ S.completionEdges := by
          apply S.liftedLiveEdges_subset_completionEdges
          rw [S.mem_liftedLiveEdges]
          exact hTriangleLive.2.2
        exact S.outside_complete_pair_not_both_terminals hSparse
          v N.p N.q N.r N.hvp N.hvq N.hvr N.hpq N.hpr N.hqr
          hvOutside N.vp_mem N.vq_mem N.vr_mem hprComplete hqrComplete
          t hpT hqT
    | Sum.inr _ => fun e heT heMissing ↦ by
        apply Finset.mem_erase.mpr
        refine ⟨heMissing, ?_⟩
        rw [mem_restrictedLiveEdges_iff]
        apply mem_deleteVertexEdges.mpr
        refine ⟨?_, deleted_not_mem_mapped_vertices v e⟩
        have heVertices : e.vertices =
            ({⟨N.p, N.hvp.symm⟩, ⟨N.q, N.hvq.symm⟩} :
              Finset (RemainingVertex v)) ∨
          e.vertices = {⟨N.p, N.hvp.symm⟩, ⟨N.r, N.hvr.symm⟩} ∨
          e.vertices = {⟨N.q, N.hvq.symm⟩, ⟨N.r, N.hvr.symm⟩} := by
          have hsMem : e.source ∈ e.vertices := by
            rw [SimpleEdge.vertices, ← e.source_target_mk]
            simp [Sym2.toFinset_mk_eq]
          have htMem : e.target ∈ e.vertices := by
            rw [SimpleEdge.vertices, ← e.source_target_mk]
            simp [Sym2.toFinset_mk_eq]
          have hs := heT hsMem
          have ht := heT htMem
          have hst := e.source_ne_target
          have hverts : e.vertices = {e.source, e.target} := by
            rw [SimpleEdge.vertices, ← e.source_target_mk]
            simp [Sym2.toFinset_mk_eq]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
          rcases hs with hs | hs | hs <;>
            rcases ht with ht | ht | ht <;>
            simp_all [Finset.pair_comm]
        rcases heVertices with hPQ | hPR | hQR
        · exfalso
          apply heMissing
          apply SimpleEdge.eq_of_vertices_eq
          rw [hPQ]
          ext x
          rw [mem_restrictSimpleEdge_vertices_iff, vertices_simpleEdge]
          simp [Subtype.ext_iff]
        · have hMap : Sparse22Transport.mapSimpleEdge
              (remainingVertexEmbedding v) e = simpleEdge N.p N.r N.hpr := by
            have heq : e = restrictSimpleEdge v
                (simpleEdge N.p N.r N.hpr)
                (not_mem_degreeThreeNeighbourPair N _ (by simp)) := by
              apply SimpleEdge.eq_of_vertices_eq
              rw [hPR]
              ext x
              rw [mem_restrictSimpleEdge_vertices_iff, vertices_simpleEdge]
              simp [Subtype.ext_iff]
            rw [heq, map_restrictSimpleEdge]
          rw [hMap]
          exact hTriangleLive.2.1
        · have hMap : Sparse22Transport.mapSimpleEdge
              (remainingVertexEmbedding v) e = simpleEdge N.q N.r N.hqr := by
            have heq : e = restrictSimpleEdge v
                (simpleEdge N.q N.r N.hqr)
                (not_mem_degreeThreeNeighbourPair N _ (by simp)) := by
              apply SimpleEdge.eq_of_vertices_eq
              rw [hQR]
              ext x
              rw [mem_restrictSimpleEdge_vertices_iff, vertices_simpleEdge]
              simp [Subtype.ext_iff]
            rw [heq, map_restrictSimpleEdge]
          rw [hMap]
          exact hTriangleLive.2.2

/-! ## Completion transport for the registered child -/

/-- The completion of the registered child embeds in the old completion by
sending the new private ghost back to the deleted outside apex. -/
def registeredCompletionEmbedding (v : V) :
    (RemainingVertex v ⊕ (Flag ⊕ Unit)) ↪ (V ⊕ Flag) where
  toFun
    | Sum.inl u => Sum.inl u.1
    | Sum.inr (Sum.inl t) => Sum.inr t
    | Sum.inr (Sum.inr _) => Sum.inl v
  inj' := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            change Sum.inl (x.1 : V) = Sum.inl (y.1 : V) at hxy
            exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj hxy))
        | inr y =>
            cases y with
            | inl y => exact False.elim (Sum.inl_ne_inr hxy)
            | inr y =>
                change Sum.inl (x.1 : V) = Sum.inl v at hxy
                exact False.elim (x.2 (Sum.inl.inj hxy))
    | inr x =>
        cases x with
        | inl x =>
            cases y with
            | inl y => exact False.elim (Sum.inr_ne_inl hxy)
            | inr y =>
                cases y with
                | inl y =>
                    change Sum.inr x = Sum.inr y at hxy
                    exact congrArg (fun z => Sum.inr (Sum.inl z))
                      (Sum.inr.inj hxy)
                | inr y => exact False.elim (Sum.inr_ne_inl hxy)
        | inr x =>
            cases y with
            | inl y =>
                change Sum.inl v = Sum.inl (y.1 : V) at hxy
                exact False.elim (y.2 (Sum.inl.inj hxy).symm)
            | inr y =>
                cases y with
                | inl y => exact False.elim (Sum.inl_ne_inr hxy)
                | inr y =>
                    cases x
                    cases y
                    rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_liftLiveEdge_registered
    (v : V) (e : SimpleEdge (RemainingVertex v)) :
    Sparse22Transport.mapSimpleEdge (registeredCompletionEmbedding
        (Flag := Flag) v)
        (liftLiveEdge (Flag := Flag ⊕ Unit) e) =
      liftLiveEdge (Flag := Flag)
        (Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v) e) := by
  apply Subtype.ext
  simp only [Sparse22Transport.mapSimpleEdge_val, liftLiveEdge_val,
    Sym2.map_map]
  induction e.1 using Sym2.inductionOn with
  | _ a b =>
      simp [registeredCompletionEmbedding, remainingVertexEmbedding]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_ghostEdge_registered_old
    (v : V) (t : Flag) (x : RemainingVertex v) :
    Sparse22Transport.mapSimpleEdge (registeredCompletionEmbedding
        (Flag := Flag) v)
        (ghostEdge (Sum.inl t) x) = ghostEdge t x.1 := by
  apply Subtype.ext
  change s(Sum.inr t, Sum.inl x.1) = s(Sum.inr t, Sum.inl x.1)
  rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_ghostEdge_registered_new
    (v : V) (x : RemainingVertex v) :
    Sparse22Transport.mapSimpleEdge (registeredCompletionEmbedding
        (Flag := Flag) v)
        (ghostEdge (Sum.inr ()) x) =
      liftLiveEdge (Flag := Flag) (simpleEdge v x.1 x.2.symm) := by
  apply Subtype.ext
  change s(Sum.inl v, Sum.inl x.1) = s(Sum.inl v, Sum.inl x.1)
  rfl

@[simp]
theorem State.registerOutside_edges
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges) :
    (S.registerOutside hSparse v hvOutside N hTriangleLive).edges =
      (restrictedLiveEdges S.edges v).erase
        (restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
          (not_mem_degreeThreeNeighbourPair N _ (by simp))) := rfl

/-- Every completed edge of the registered child maps to an edge of the
old completion.  The new ghost star maps exactly to the deleted apex star,
and the newly restored missing edge maps to the old live `pq` edge. -/
theorem State.map_registerOutside_completionEdges_subset
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges) :
    Sparse22Transport.mapEdgeSet
        (registeredCompletionEmbedding (Flag := Flag) v)
        (S.registerOutside hSparse v hvOutside N hTriangleLive).completionEdges ⊆
      S.completionEdges := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
  rw [State.completionEdges] at hf
  rcases Finset.mem_union.mp hf with hfLiveOrMissing | hfGhost
  · rcases Finset.mem_union.mp hfLiveOrMissing with hfLive | hfMissing
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hfLive
      change Sparse22Transport.mapSimpleEdge
        (registeredCompletionEmbedding (Flag := Flag) v)
        (liftLiveEdge (Flag := Flag ⊕ Unit) g) ∈ S.completionEdges
      rw [map_liftLiveEdge_registered]
      apply S.liftedLiveEdges_subset_completionEdges
      rw [S.mem_liftedLiveEdges]
      have hgRestricted : g ∈ restrictedLiveEdges S.edges v := by
        exact Finset.mem_of_mem_erase hg
      exact (mem_deleteVertexEdges.mp
        ((mem_restrictedLiveEdges_iff S.edges v g).1 hgRestricted)).1
    · obtain ⟨t, _ht, hft⟩ := Finset.mem_image.mp hfMissing
      subst f
      cases t with
      | inl t =>
          change Sparse22Transport.mapSimpleEdge
              (registeredCompletionEmbedding (Flag := Flag) v)
              (liftLiveEdge (Flag := Flag ⊕ Unit)
                ((S.registerOutside hSparse v hvOutside N
                  hTriangleLive).missing (Sum.inl t))) ∈ S.completionEdges
          change Sparse22Transport.mapSimpleEdge
              (registeredCompletionEmbedding (Flag := Flag) v)
              (liftLiveEdge (Flag := Flag ⊕ Unit)
                ((S.deleteOutside v hvOutside).missing t)) ∈ S.completionEdges
          rw [map_liftLiveEdge_registered]
          change liftLiveEdge (Flag := Flag)
              (Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
                (restrictSimpleEdge v (S.missing t)
                  (outside_not_mem_missing_vertices S v hvOutside t))) ∈
            S.completionEdges
          rw [map_restrictSimpleEdge]
          exact S.lifted_missing_mem_completionEdges t
      | inr t =>
          cases t
          change Sparse22Transport.mapSimpleEdge
              (registeredCompletionEmbedding (Flag := Flag) v)
              (liftLiveEdge (Flag := Flag ⊕ Unit)
                (restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
                  (not_mem_degreeThreeNeighbourPair N _ (by simp)))) ∈
            S.completionEdges
          rw [map_liftLiveEdge_registered, map_restrictSimpleEdge]
          apply S.liftedLiveEdges_subset_completionEdges
          rw [S.mem_liftedLiveEdges]
          exact hTriangleLive.1
  · obtain ⟨t, _ht, hfStar⟩ := Finset.mem_biUnion.mp hfGhost
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hfStar
    subst f
    cases t with
    | inl t =>
        change Sparse22Transport.mapSimpleEdge
          (registeredCompletionEmbedding (Flag := Flag) v)
          (ghostEdge (Sum.inl t) x) ∈ S.completionEdges
        rw [map_ghostEdge_registered_old]
        apply S.ghostEdge_mem_completionEdges t
        exact (mem_restrictVertexSet_iff v (S.terminals t)
          (not_mem_terminals_of_flagMultiplicity_eq_zero
            S v hvOutside t) x).1 hx
    | inr t =>
        cases t
        change Sparse22Transport.mapSimpleEdge
          (registeredCompletionEmbedding (Flag := Flag) v)
          (ghostEdge (Sum.inr ()) x) ∈ S.completionEdges
        rw [map_ghostEdge_registered_new]
        apply S.liftedLiveEdges_subset_completionEdges
        rw [S.mem_liftedLiveEdges]
        change x ∈
          ({⟨N.p, N.hvp.symm⟩, ⟨N.q, N.hvq.symm⟩,
            ⟨N.r, N.hvr.symm⟩} : Finset (RemainingVertex v)) at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx
        · have hx' : x = ⟨N.p, N.hvp.symm⟩ := hx
          subst x
          exact N.vp_mem
        · have hx' : x = ⟨N.q, N.hvq.symm⟩ := hx
          subst x
          exact N.vq_mem
        · have hx' : x = ⟨N.r, N.hvr.symm⟩ := hx
          subst x
          exact N.vr_mem

/-- Registering the complete outside triangle preserves literal completion
`(2,2)`-sparsity. -/
theorem State.registerOutside_completionSparse
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges) :
    (S.registerOutside hSparse v hvOutside N hTriangleLive).CompletionSparse := by
  exact Sparse22Transport.sparse22_of_mapEdgeSet_subset
    (registeredCompletionEmbedding (Flag := Flag) v) hSparse
    (S.map_registerOutside_completionEdges_subset
      hSparse v hvOutside N hTriangleLive)

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0036

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0036/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0036.json"

section BundleSource0037
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagOutsideRegisteredBranch.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagOutsideRegisteredBranch.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# The intrinsic function-field branch after outside registration

The complete exceptional outside move deletes the degree-three apex and
registers its three retained neighbours as one new active flag.  This file
constructs the literal function-field branch on that registered state.  Old
flag collinearities are inherited from outside deletion; the new one is
proved by descending the actual neighbour collinearity to the field generated
by the retained coordinates.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
/-- A collinear triple of pairwise distinct points is an affine-collinear
three-element set.  This is the small conversion used for the newly
registered flag. -/
theorem affinelyCollinearOn_three_of_collinear
    {W : Type*} [DecidableEq W]
    (a : W → Fin 3 → K) (p q r : W)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpos : a p ≠ a q)
    (hcol : PinCollinearity.Collinear (a p) (a q) (a r)) :
    AffinelyCollinearOn a ({p, q, r} : Finset W) := by
  obtain ⟨t, ht⟩ :=
    (collinear_iff_exists_smul_difference (a p) (a q) (a r) hpos).1 hcol
  refine ⟨a p, a q - a p, ?_⟩
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by module⟩
  · refine ⟨t, ?_⟩
    funext j
    have hj := congrFun ht j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linear_combination hj

/-- The genuine intrinsic branch on the state obtained by registering a
complete outside neighbour triangle. -/
def FunctionFieldBranch.registerOutsideIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges)
    (hcol : PinCollinearity.Collinear
      (Y.position N.p) (Y.position N.q) (Y.position N.r)) :
    FunctionFieldBranch
      (k := k) (K := retainedLiveCoordinateField (k := k) Y.position v)
      (S.registerOutside hSparse v hvOutside N hTriangleLive) where
  position := intrinsicRestrictedPlacement (k := k) Y.position v
  generated := intrinsicRestrictedPlacement_generated (k := k) Y.position v
  distinct := by
    intro a b hab
    apply Subtype.ext
    apply Y.distinct
    funext j
    exact congrArg Subtype.val (congrFun hab j)
  collinear t := by
    cases t with
    | inl t =>
        exact (Y.deleteOutsideIntrinsic S v hvOutside).collinear t
    | inr t =>
        cases t
        let L := retainedLiveCoordinateField (k := k) Y.position v
        let childPosition := intrinsicRestrictedPlacement (k := k) Y.position v
        let p : RemainingVertex v := ⟨N.p, N.hvp.symm⟩
        let q : RemainingVertex v := ⟨N.q, N.hvq.symm⟩
        let r : RemainingVertex v := ⟨N.r, N.hvr.symm⟩
        have hpqChild : p ≠ q := by
          intro h
          exact N.hpq (congrArg Subtype.val h)
        have hprChild : p ≠ r := by
          intro h
          exact N.hpr (congrArg Subtype.val h)
        have hqrChild : q ≠ r := by
          intro h
          exact N.hqr (congrArg Subtype.val h)
        have hpqPosition : childPosition p ≠ childPosition q := by
          intro h
          exact hpqChild ((show Function.Injective childPosition from by
            intro a b hab
            apply Subtype.ext
            apply Y.distinct
            funext j
            exact congrArg Subtype.val (congrFun hab j)) h)
        have hcolL : PinCollinearity.Collinear
            (childPosition p) (childPosition q) (childPosition r) := by
          apply collinear_restrictScalars
            (k := k) (K := K) L
            (childPosition p) (childPosition q) (childPosition r)
            hpqPosition
          simpa [childPosition, intrinsicRestrictedPlacement, p, q, r] using hcol
        change AffinelyCollinearOn childPosition ({p, q, r} :
          Finset (RemainingVertex v))
        exact affinelyCollinearOn_three_of_collinear
          childPosition p q r hpqChild hprChild hqrChild hpqPosition hcolL

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0037

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0037/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0037.json"

section BundleSource0038
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagInsertedBranch.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagInsertedBranch.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Function-field branches after inserting one virtual live edge

Insertion changes only the live edge set.  The coordinate field, placement,
distinctness, active flags, terminal sets, and their collinearities remain
literal copies.  This small constructor lets both exceptional induction
moves apply the recursive semismallness theorem to an actually inserted
child state.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {k K V Flag : Type*}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- Reinterpret a function-field branch on the state obtained by inserting
one certified live edge. -/
def FunctionFieldBranch.insertLiveEdge
    (S : State V Flag)
    (Y : FunctionFieldBranch (k := k) (K := K) S)
    (e : SimpleEdge V) (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    FunctionFieldBranch (k := k) (K := K) (S.insertLiveEdge e heMissing) where
  position := Y.position
  generated := Y.generated
  distinct := Y.distinct
  collinear t := by
    simpa only [State.insertLiveEdge_terminals] using Y.collinear t

@[simp]
theorem FunctionFieldBranch.insertLiveEdge_position
    (S : State V Flag)
    (Y : FunctionFieldBranch (k := k) (K := K) S)
    (e : SimpleEdge V) (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    (Y.insertLiveEdge S e heMissing).position = Y.position := rfl

/-- Its stress dimension is the literal stress dimension of the inserted
edge set at the unchanged placement. -/
theorem FunctionFieldBranch.insertLiveEdge_stressDim
    (S : State V Flag)
    (Y : FunctionFieldBranch (k := k) (K := K) S)
    (e : SimpleEdge V) (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    (Y.insertLiveEdge S e heMissing).stressDim
        (S.insertLiveEdge e heMissing) =
      DirectionStress.directionStressDim (insert e S.edges) Y.position := rfl

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0038

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0038/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0038.json"

section BundleSource0039
/- Source: Papers/RigidityZheng_Algebra_AlgebraicIndependentAffine.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/AlgebraicIndependentAffine.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Affine linear independence from algebraic independence

An algebraically independent family remains linearly independent after a
single constant `1` is adjoined.  This small coefficient-comparison lemma is
the exact algebraic input used by the full three-coordinate response step;
it is proved from injectivity of multivariate polynomial evaluation, rather
than assumed as an affine-genericity predicate.
-/

namespace RB31E2E

namespace AlgebraicIndependentAffine

noncomputable section

open Set Submodule

variable {L K I : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- The constant one is not in the linear span of an algebraically
independent family. -/
theorem one_not_mem_span_range
    (x : I → K) (hx : AlgebraicIndependent L x) :
    (1 : K) ∉ Submodule.span L (Set.range x) := by
  intro hOne
  obtain ⟨c : I → L, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun L).mp hOne
  let P : MvPolynomial I L :=
    MvPolynomial.C 1 -
      ∑ i : I, MvPolynomial.C (c i) * MvPolynomial.X i
  have hEval : MvPolynomial.aeval x P = 0 := by
    dsimp [P]
    simp only [map_sub, map_one, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    rw [show (∑ i : I, algebraMap L K (c i) * x i) = 1 by
      simpa [Algebra.smul_def] using hc]
    exact sub_self 1
  have hPzero : P = 0 :=
    (algebraicIndependent_iff_injective_aeval.mp hx)
      (by simpa using hEval)
  have hAtZero := congrArg
    (MvPolynomial.eval (fun _ : I ↦ (0 : L))) hPzero
  simp [P] at hAtZero

omit [DecidableEq I] in
/-- Adjoining the constant coordinate to an algebraically independent
finite family gives an affine-linearly independent `Option` family. -/
theorem option_one_linearIndependent
    (x : I → K) (hx : AlgebraicIndependent L x) :
    LinearIndependent L (fun o : Option I ↦ o.casesOn' (1 : K) x) := by
  exact hx.linearIndependent.option (one_not_mem_span_range x hx)

end

end AlgebraicIndependentAffine

end RB31E2E


end
end BundleSource0039

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0039/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0039.json"

section BundleSource0040
/- Source: Papers/RigidityZheng_Algebra_AffineSpanDescent.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/AffineSpanDescent.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Descent from an affine-generic scalar extension of a row space

Let `W` be a row space over a field `L`, and extend all its rows
coordinatewise to a field `K`.  If

`constant + ∑ j, x j • coefficient j`

belongs to the extended row space and the finite family `x` is
algebraically independent over `L`, then the constant term and every
coefficient already belong to `W` over `L`.

The proof is literal coefficient comparison.  A coefficient outside `W`
is separated by an `L`-linear functional.  We extend that functional
coordinatewise to `K`; it kills the extended row space and produces an
affine-linear relation among `1` and the `x j`.  The independently proved
`option_one_linearIndependent` theorem then gives the contradiction.
-/

namespace RB31E2E

namespace AffineSpanDescent

noncomputable section

open Set Submodule

variable {L K I C J : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype I] [DecidableEq I]
  [Fintype C] [DecidableEq C]

/-- Coordinatewise scalar extension of a linear functional on a finite
function space. -/
def extendLinearFunctional (phi : (I → L) →ₗ[L] L) :
    (I → K) →ₗ[K] K where
  toFun y := ∑ i : I,
    y i * algebraMap L K (phi (Pi.single i 1))
  map_add' y z := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum,
      RingHom.id_apply]

/-- On a vector defined over `L`, the extended functional is just the
image of the original functional. -/
@[simp]
theorem extendLinearFunctional_mapVector
    (phi : (I → L) →ₗ[L] L) (y : I → L) :
    extendLinearFunctional (K := K) phi
        (FiniteFamilyBaseChange.mapVector (K := K) y) =
      algebraMap L K (phi y) := by
  have hy : y = ∑ i : I,
      y i • (Pi.single i (1 : L) : I → L) := by
    funext j
    simp [Pi.single_apply]
  have hphi : phi y =
      ∑ i : I, y i * phi (Pi.single i (1 : L) : I → L) := by
    calc
      phi y = phi (∑ i : I,
          y i • (Pi.single i (1 : L) : I → L)) := congrArg phi hy
      _ = ∑ i : I,
          phi (y i • (Pi.single i (1 : L) : I → L)) := by
            apply map_sum
      _ = ∑ i : I,
          y i * phi (Pi.single i (1 : L) : I → L) := by
        simp only [map_smul, smul_eq_mul]
  change (∑ i : I,
      algebraMap L K (y i) *
        algebraMap L K (phi (Pi.single i (1 : L) : I → L))) =
    algebraMap L K (phi y)
  rw [hphi, map_sum]
  simp only [map_mul]

/-- The scalar-extended functional kills the scalar-extended span of every
row killed by the original functional. -/
theorem mappedSpan_le_extendLinearFunctional_ker
    (rows : J → I → L) (phi : (I → L) →ₗ[L] L)
    (hkill : span L (Set.range rows) ≤ LinearMap.ker phi) :
    span K (Set.range (fun j ↦
        FiniteFamilyBaseChange.mapVector (K := K) (rows j))) ≤
      LinearMap.ker (extendLinearFunctional (K := K) phi) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change extendLinearFunctional (K := K) phi
      (FiniteFamilyBaseChange.mapVector (K := K) (rows j)) = 0
  rw [extendLinearFunctional_mapVector]
  have hrowZero : phi (rows j) = 0 :=
    hkill (Submodule.subset_span ⟨j, rfl⟩)
  simp [hrowZero]

omit [DecidableEq C] in
/-- Every affine coefficient descends to the original row space.  `none`
selects the constant term and `some j` selects the coefficient of `x j`. -/
theorem affineCoefficient_mem_span
    (rows : J → I → L)
    (x : C → K) (hx : AlgebraicIndependent L x)
    (constant : I → L) (coefficient : C → I → L)
    (hmem :
      FiniteFamilyBaseChange.mapVector (K := K) constant +
          ∑ j : C, x j •
            FiniteFamilyBaseChange.mapVector (K := K) (coefficient j) ∈
        span K (Set.range (fun r ↦
          FiniteFamilyBaseChange.mapVector (K := K) (rows r))))
    (o : Option C) :
    o.casesOn' constant coefficient ∈ span L (Set.range rows) := by
  let W : Submodule L (I → L) := span L (Set.range rows)
  let z : I → L := o.casesOn' constant coefficient
  by_contra hz
  have hzW : z ∉ W := by simpa [W, z] using hz
  obtain ⟨phi, hphiz, hkill⟩ :=
    Submodule.exists_le_ker_of_notMem hzW
  let phiK : (I → K) →ₗ[K] K := extendLinearFunctional (K := K) phi
  have hzero : phiK
      (FiniteFamilyBaseChange.mapVector (K := K) constant +
        ∑ j : C, x j •
          FiniteFamilyBaseChange.mapVector (K := K) (coefficient j)) = 0 := by
    exact (mappedSpan_le_extendLinearFunctional_ker
      (K := K) rows phi hkill) hmem
  have hrelation :
      algebraMap L K (phi constant) +
          ∑ j : C, x j * algebraMap L K (phi (coefficient j)) = 0 := by
    change extendLinearFunctional (K := K) phi
      (FiniteFamilyBaseChange.mapVector (K := K) constant +
        ∑ j : C, x j •
          FiniteFamilyBaseChange.mapVector (K := K) (coefficient j)) = 0
      at hzero
    simpa only [map_add, map_sum, map_smul,
      extendLinearFunctional_mapVector, smul_eq_mul] using hzero
  let affineVector : Option C → K :=
    fun q ↦ q.casesOn' (1 : K) x
  let affineCoefficient : Option C → L :=
    fun q ↦ q.casesOn' (phi constant) (fun j ↦ phi (coefficient j))
  have hsum : ∑ q : Option C,
      affineCoefficient q • affineVector q = 0 := by
    simpa [affineVector, affineCoefficient, Algebra.smul_def, mul_comm]
      using hrelation
  have hLI : LinearIndependent L affineVector := by
    simpa [affineVector] using
      (AlgebraicIndependentAffine.option_one_linearIndependent x hx)
  have hcoefficientZero : ∀ q : Option C, affineCoefficient q = 0 :=
    (Fintype.linearIndependent_iff.mp hLI) affineCoefficient hsum
  have hoZero := hcoefficientZero o
  apply hphiz
  cases o with
  | none => simpa [z, affineCoefficient] using hoZero
  | some j => simpa [z, affineCoefficient] using hoZero

omit [DecidableEq C] in
/-- Bundled form: the constant term and all variable coefficients descend
simultaneously. -/
theorem affineCoefficients_mem_span
    (rows : J → I → L)
    (x : C → K) (hx : AlgebraicIndependent L x)
    (constant : I → L) (coefficient : C → I → L)
    (hmem :
      FiniteFamilyBaseChange.mapVector (K := K) constant +
          ∑ j : C, x j •
            FiniteFamilyBaseChange.mapVector (K := K) (coefficient j) ∈
        span K (Set.range (fun r ↦
          FiniteFamilyBaseChange.mapVector (K := K) (rows r)))) :
    constant ∈ span L (Set.range rows) ∧
      ∀ j, coefficient j ∈ span L (Set.range rows) := by
  constructor
  · exact affineCoefficient_mem_span rows x hx constant coefficient hmem none
  · intro j
    exact affineCoefficient_mem_span rows x hx constant coefficient hmem (some j)

end

end AffineSpanDescent

end RB31E2E


end
end BundleSource0040

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0040/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0040.json"

section BundleSource0041
/- Source: Papers/RigidityZheng_Linear_DirectionResponseBaseChange.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/DirectionResponseBaseChange.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Descent of a virtual direction response through a field extension

For a placement defined over `L`, a direction row belongs to the span of
the old direction rows over `L` exactly when its coordinatewise scalar
extension belongs to their span over `K`.  The reverse implication used below
is proved by comparing the ranks before and after
inserting the virtual row, using the already established invariance of
direction rank under field extension.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {L K V : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype V] [DecidableEq V]

/-- Scalar extension transports membership in a literal direction-row
space. -/
theorem directionRow_mem_mapPlacement_of_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → L) (e : SimpleEdge V)
    (hrow : directionRow a e ∈ directionRowSpace F a) :
    directionRow (mapPlacement (K := K) a) e ∈
      directionRowSpace F (mapPlacement (K := K) a) := by
  -- Avoid choosing row coefficients: compare ranks after adjoining `e`.
  have hInsertL : directionRowSpace (insert e F) a =
      directionRowSpace F a :=
    directionRowSpace_insert_eq_of_mem F a e hrow
  have hRankL : directionEquilibriumRank (insert e F) a =
      directionEquilibriumRank F a := by
    rw [directionEquilibriumRank_eq_finrank_rowSpace,
      directionEquilibriumRank_eq_finrank_rowSpace, hInsertL]
  have hRankK :
      directionEquilibriumRank (insert e F) (mapPlacement (K := K) a) =
        directionEquilibriumRank F (mapPlacement (K := K) a) := by
    rw [directionEquilibriumRank_mapPlacement,
      directionEquilibriumRank_mapPlacement, hRankL]
  have hLe := directionRowSpace_le_insert F
    (mapPlacement (K := K) a) e
  have hEq : directionRowSpace (insert e F) (mapPlacement (K := K) a) =
      directionRowSpace F (mapPlacement (K := K) a) := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hLe
    simpa only [directionEquilibriumRank_eq_finrank_rowSpace] using hRankK.symm
  rw [← hEq]
  apply Submodule.subset_span
  exact ⟨⟨e, Finset.mem_insert_self e F⟩, rfl⟩

/-- If a row defined over the smaller field is a virtual response after
scalar extension, it was already a virtual response over the smaller
field. -/
theorem directionRow_mem_of_mapPlacement_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → L) (e : SimpleEdge V)
    (hrow : directionRow (mapPlacement (K := K) a) e ∈
      directionRowSpace F (mapPlacement (K := K) a)) :
    directionRow a e ∈ directionRowSpace F a := by
  have hInsertK :
      directionRowSpace (insert e F) (mapPlacement (K := K) a) =
        directionRowSpace F (mapPlacement (K := K) a) :=
    directionRowSpace_insert_eq_of_mem F
      (mapPlacement (K := K) a) e hrow
  have hRankK :
      directionEquilibriumRank (insert e F) (mapPlacement (K := K) a) =
        directionEquilibriumRank F (mapPlacement (K := K) a) := by
    rw [directionEquilibriumRank_eq_finrank_rowSpace,
      directionEquilibriumRank_eq_finrank_rowSpace, hInsertK]
  have hRankL : directionEquilibriumRank (insert e F) a =
      directionEquilibriumRank F a := by
    simpa only [directionEquilibriumRank_mapPlacement] using hRankK
  have hLe := directionRowSpace_le_insert F a e
  have hEq : directionRowSpace (insert e F) a = directionRowSpace F a := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hLe
    simpa only [directionEquilibriumRank_eq_finrank_rowSpace] using hRankL.symm
  rw [← hEq]
  apply Submodule.subset_span
  exact ⟨⟨e, Finset.mem_insert_self e F⟩, rfl⟩

/-- Hence response-row membership is equivalent before and after scalar
extension. -/
theorem directionRow_mem_mapPlacement_iff
    (F : SimpleEdgeSet V) (a : V → Fin 3 → L) (e : SimpleEdge V) :
    directionRow (mapPlacement (K := K) a) e ∈
        directionRowSpace F (mapPlacement (K := K) a) ↔
      directionRow a e ∈ directionRowSpace F a := by
  constructor
  · exact directionRow_mem_of_mapPlacement_mem F a e
  · exact directionRow_mem_mapPlacement_of_mem F a e

end

end DirectionStress

end RB31E2E


end
end BundleSource0041

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0041/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0041.json"

section BundleSource0042
/- Source: Papers/RigidityZheng_Linear_OutsideExceptionalFullResponse.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/OutsideExceptionalFullResponse.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/






@[expose] public section

/-!
# Full response of the exceptional outside three-star

In the exceptional outside branch the deleted point contributes three
algebraically independent coordinates over the retained coordinate field.
The three retained neighbours are collinear, and the whole one-dimensional
local kernel has zero connecting class.

This file turns those already proved facts into the response statement
needed by the flag move: every one of the three neighbour-pair direction
rows belongs to the literal row space after deleting the apex.  The key
step is coefficient comparison over the retained coordinate field; no
response row is assumed as an input.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {V : Type w}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V]

open Set Submodule

/-! ## Retained-field models of the deleted row space -/

/-- Put all retained points in their coordinate field and put the deleted
vertex at zero.  The latter value is irrelevant to every deleted edge. -/
def retainedZeroPlacement
    (a : V → Fin 3 → K) (v : V) :
    V → Fin 3 → retainedCoordinateField (k := k) a v :=
  fun z j ↦ if hz : z = v then 0 else
    ⟨a z j, retained_coordinate_mem (k := k) a v z hz j⟩

omit [Fintype V] in
@[simp]
theorem retainedZeroPlacement_apply_of_ne
    (a : V → Fin 3 → K) (v z : V) (hz : z ≠ v) (j : Fin 3) :
    ((retainedZeroPlacement (k := k) a v z j :
      retainedCoordinateField (k := k) a v) : K) = a z j := by
  simp [retainedZeroPlacement, hz]

omit [Fintype V] in
/-- A deleted edge has exactly the same row after passing through the
retained-field zero model and extending scalars back to `K`. -/
theorem directionRow_map_retainedZeroPlacement_of_avoids
    (a : V → Fin 3 → K) (v : V) (e : SimpleEdge V)
    (hve : v ∉ e.vertices) :
    directionRow
        (mapPlacement (K := K) (retainedZeroPlacement (k := k) a v)) e =
      directionRow a e := by
  have hs : e.source ≠ v := by
    intro h
    apply hve
    rw [← h]
    rw [SimpleEdge.vertices, ← e.source_target_mk]
    simp [Sym2.toFinset_mk_eq]
  have ht : e.target ≠ v := by
    intro h
    apply hve
    rw [← h]
    rw [SimpleEdge.vertices, ← e.source_target_mk]
    simp [Sym2.toFinset_mk_eq]
  funext z j
  simp only [directionRow, edgeDirection, mapPlacement]
  split_ifs <;> simp [retainedZeroPlacement, hs, ht]

omit [Fintype V] in
/-- Hence the whole deleted row space is literally the scalar extension of
the retained-field deleted row space. -/
theorem directionRowSpace_map_retainedZeroPlacement_delete
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    directionRowSpace (deleteVertexEdges F v)
        (mapPlacement (K := K) (retainedZeroPlacement (k := k) a v)) =
      directionRowSpace (deleteVertexEdges F v) a := by
  unfold directionRowSpace
  congr 1
  ext row
  constructor <;> rintro ⟨e, rfl⟩
  · refine ⟨e, ?_⟩
    exact (directionRow_map_retainedZeroPlacement_of_avoids
      (k := k) a v e.1 (mem_deleteVertexEdges.mp e.2).2).symm
  · refine ⟨e, ?_⟩
    exact directionRow_map_retainedZeroPlacement_of_avoids
      (k := k) a v e.1 (mem_deleteVertexEdges.mp e.2).2

omit [Fintype V] [DecidableEq V] in
/-- Flattening a nested finite load is a linear equivalence, so it
preserves membership in the span of a labelled row family. -/
theorem flattenVector_mem_span_iff
    {I : Type*} [Finite I]
    (row : I → V → Fin 3 → k) (z : V → Fin 3 → k) :
    flattenVector z ∈
        span k (Set.range (fun i ↦ flattenVector (row i))) ↔
      z ∈ span k (Set.range row) := by
  let flat : (V → Fin 3 → k) ≃ₗ[k] (V × Fin 3 → k) :=
    (LinearEquiv.curry k k V (Fin 3)).symm
  have hset : flat '' Set.range row =
      Set.range (fun i ↦ flattenVector (row i)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨row i, ⟨i, rfl⟩, rfl⟩
  have hspan :
      (span k (Set.range row)).map
          (flat : (V → Fin 3 → k) →ₗ[k] (V × Fin 3 → k)) =
        span k (Set.range (fun i ↦ flattenVector (row i))) := by
    rw [Submodule.map_span]
    change span k (flat '' Set.range row) = _
    rw [hset]
  rw [← hspan]
  constructor
  · intro hz
    obtain ⟨y, hy, hflat⟩ := Submodule.mem_map.mp hz
    have : y = z := flat.injective hflat
    simpa [this] using hy
  · intro hz
    exact ⟨z, hz, rfl⟩

/-! ## Affine coefficient loads -/

/-- Insert a spatial vector as the load at one named vertex. -/
def vertexLoad (p : V) (z : Fin 3 → k) : V → Fin 3 → k :=
  Pi.single p z

/-- The spatial coordinate basis vector. -/
def coordinateUnit (j : Fin 3) : Fin 3 → k :=
  Pi.single j 1

/-- Constant term of the away-load of the collinear three-star. -/
def outsideAwayConstant
    (pos : V → Fin 3 → k) (p q r : V) (t : k) :
    V → Fin 3 → k :=
  (1 - t) • vertexLoad p (pos p) +
    t • vertexLoad q (pos q) - vertexLoad r (pos r)

/-- Coefficient of an arbitrary apex vector in the same away-load. -/
def outsideAwayCoefficient
    (p q r : V) (t : k) (z : Fin 3 → k) :
    V → Fin 3 → k :=
  -(1 - t) • vertexLoad p z -
    t • vertexLoad q z + vertexLoad r z

omit [Fintype V] in
/-- The arbitrary-vector coefficient is the linear combination of its
three coordinate coefficients. -/
theorem outsideAwayCoefficient_eq_sum_coordinateUnit
    (p q r : V) (t : k) (z : Fin 3 → k) :
    outsideAwayCoefficient p q r t z =
      ∑ j : Fin 3, z j •
        outsideAwayCoefficient p q r t (coordinateUnit j) := by
  funext u c
  by_cases hup : u = p <;> by_cases huq : u = q <;>
      by_cases hur : u = r <;> fin_cases c <;>
    simp_all [outsideAwayCoefficient, vertexLoad, coordinateUnit,
      Pi.single_apply, Fin.sum_univ_three] <;> ring

omit [Fintype V] in
/-- First coefficient identity: constant plus the coefficient evaluated at
the third point is the `pq` direction row, up to the nonzero scalar
`t(1-t)`. -/
theorem outsideAwayConstant_add_coefficient_r
    (pos : V → Fin 3 → k) (p q r : V)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (t : k)
    (hline : pos r - pos p = t • (pos q - pos p)) :
    outsideAwayConstant pos p q r t +
        outsideAwayCoefficient p q r t (pos r) =
      (t * (1 - t)) • directionRow pos (simpleEdge p q hpq) := by
  funext u j
  by_cases hup : u = p
  · subst u
    simp only [outsideAwayConstant, outsideAwayCoefficient,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_left pos p q hpq) j]
    have hj := congrFun hline j
    simp [vertexLoad, hpq, hpr] at hj ⊢
    linear_combination -(1 - t) * hj
  · by_cases huq : u = q
    · subst u
      simp only [outsideAwayConstant, outsideAwayCoefficient,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_right pos p q hpq) j]
      have hj := congrFun hline j
      simp [vertexLoad, hpq, hqr] at hj ⊢
      linear_combination -t * hj
    · by_cases hur : u = r
      · subst u
        simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun
          (directionRow_simpleEdge_at_other pos p q r hpq hpr.symm hqr.symm) j]
        simp [vertexLoad, hpr, hqr]
      · simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun
          (directionRow_simpleEdge_at_other pos p q u hpq hup huq) j]
        simp [vertexLoad, hup, huq, hur]

omit [Fintype V] in
/-- Second coefficient identity, stated without division. -/
theorem outsideAway_one_sub_t_smul_constant_add_coefficient_p
    (pos : V → Fin 3 → k) (p q r : V)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (t : k)
    (hline : pos r - pos p = t • (pos q - pos p)) :
    (1 - t) • (outsideAwayConstant pos p q r t +
        outsideAwayCoefficient p q r t (pos p)) =
      t • directionRow pos (simpleEdge q r hqr) := by
  funext u j
  by_cases hup : u = p
  · subst u
    simp only [outsideAwayConstant, outsideAwayCoefficient,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [congrFun
      (directionRow_simpleEdge_at_other pos q r p hqr hpq hpr) j]
    simp [vertexLoad, hpq, hpr]
    exact Or.inr (by ring)
  · by_cases huq : u = q
    · subst u
      simp only [outsideAwayConstant, outsideAwayCoefficient,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_left pos q r hqr) j]
      have hj := congrFun hline j
      simp [vertexLoad, hpq, hqr] at hj ⊢
      linear_combination t * hj
    · by_cases hur : u = r
      · subst u
        simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_right pos q r hqr) j]
        have hj := congrFun hline j
        simp [vertexLoad, hpr, hqr] at hj ⊢
        linear_combination -hj
      · simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun
          (directionRow_simpleEdge_at_other pos q r u hqr huq hur) j]
        simp [vertexLoad, hup, huq, hur]

omit [Fintype V] in
/-- Third coefficient identity, again with all denominators cleared. -/
theorem outsideAway_t_smul_constant_add_coefficient_q
    (pos : V → Fin 3 → k) (p q r : V)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (t : k)
    (hline : pos r - pos p = t • (pos q - pos p)) :
    t • (outsideAwayConstant pos p q r t +
        outsideAwayCoefficient p q r t (pos q)) =
      (1 - t) • directionRow pos (simpleEdge p r hpr) := by
  funext u j
  by_cases hup : u = p
  · subst u
    simp only [outsideAwayConstant, outsideAwayCoefficient,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_left pos p r hpr) j]
    have hj := congrFun hline j
    simp [vertexLoad, hpq, hpr] at hj ⊢
    linear_combination (1 - t) * hj
  · by_cases huq : u = q
    · subst u
      simp only [outsideAwayConstant, outsideAwayCoefficient,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [congrFun
        (directionRow_simpleEdge_at_other pos p r q hpr hpq.symm hqr) j]
      simp [vertexLoad, hpq, hqr]
    · by_cases hur : u = r
      · subst u
        simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_right pos p r hpr) j]
        have hj := congrFun hline j
        simp [vertexLoad, hpr, hqr] at hj ⊢
        linear_combination -hj
      · simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun
          (directionRow_simpleEdge_at_other pos p r u hpr hup hur) j]
        simp [vertexLoad, hup, huq, hur]

/-! ## Scalar extension and the three-star away-load -/

omit [Fintype V] in
/-- Scalar extension commutes with the constant away-load. -/
theorem mapPlacement_outsideAwayConstant
    {L : Type*} [Field L] [Algebra L K]
    (pos : V → Fin 3 → L) (p q r : V) (t : L) :
    mapPlacement (K := K) (outsideAwayConstant pos p q r t) =
      outsideAwayConstant (mapPlacement (K := K) pos) p q r
        (algebraMap L K t) := by
  funext z j
  by_cases hzp : z = p <;> by_cases hzq : z = q <;>
      by_cases hzr : z = r <;>
    simp_all [mapPlacement, outsideAwayConstant, vertexLoad,
      map_sub, map_one, map_mul, Algebra.smul_def]

omit [Fintype V] in
/-- Scalar extension commutes with every linear away coefficient. -/
theorem mapPlacement_outsideAwayCoefficient
    {L : Type*} [Field L] [Algebra L K]
    (p q r : V) (t : L) (z : Fin 3 → L) :
    mapPlacement (K := K) (outsideAwayCoefficient p q r t z) =
      outsideAwayCoefficient p q r (algebraMap L K t)
        (fun j ↦ algebraMap L K (z j)) := by
  funext u j
  by_cases hup : u = p <;> by_cases huq : u = q <;>
      by_cases hur : u = r <;>
    simp_all [mapPlacement, outsideAwayCoefficient, vertexLoad,
      map_sub, map_one, map_mul, Algebra.smul_def]

omit [Fintype V] in
/-- A coordinate basis vector is fixed by scalar extension. -/
theorem map_coordinateUnit
    {L : Type*} [Field L] [Algebra L K] (j : Fin 3) :
    (fun c ↦ algebraMap L K (coordinateUnit (k := L) j c)) =
      coordinateUnit (k := K) j := by
  funext c
  simp [coordinateUnit, Pi.single_apply]

omit [Fintype V] in
/-- The affine constant plus its value at the apex is exactly the away-load
of the fixed local relation `(1-t,t,-1)`.  Collinearity is needed only at
the apex, where it says that this relation is locally equilibrated. -/
theorem outsideAwayConstant_add_coefficient_eq_threeStar
    (pos : V → Fin 3 → k) (v p q r : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hvr : v ≠ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (t : k)
    (hline : pos r - pos p = t • (pos q - pos p)) :
    outsideAwayConstant pos p q r t +
        outsideAwayCoefficient p q r t (pos v) =
      (1 - t) • directionRow pos (simpleEdge v p hvp) +
        t • directionRow pos (simpleEdge v q hvq) +
        (-1 : k) • directionRow pos (simpleEdge v r hvr) := by
  funext u j
  by_cases huv : u = v
  · subst u
    simp only [outsideAwayConstant, outsideAwayCoefficient,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_left pos v p hvp) j,
      congrFun (directionRow_simpleEdge_at_left pos v q hvq) j,
      congrFun (directionRow_simpleEdge_at_left pos v r hvr) j]
    have hj := congrFun hline j
    simp [vertexLoad, hvp, hvq, hvr] at hj ⊢
    linear_combination -hj
  · by_cases hup : u = p
    · subst u
      simp only [outsideAwayConstant, outsideAwayCoefficient,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_right pos v p hvp) j,
        congrFun (directionRow_simpleEdge_at_other
          pos v q p hvq hvp.symm hpq) j,
        congrFun (directionRow_simpleEdge_at_other
          pos v r p hvr hvp.symm hpr) j]
      simp [vertexLoad, hpq, hpr]
      ring
    · by_cases huq : u = q
      · subst u
        simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_other
            pos v p q hvp hvq.symm hpq.symm) j,
          congrFun (directionRow_simpleEdge_at_right pos v q hvq) j,
          congrFun (directionRow_simpleEdge_at_other
            pos v r q hvr hvq.symm hqr) j]
        simp [vertexLoad, hpq, hqr]
        ring
      · by_cases hur : u = r
        · subst u
          simp only [outsideAwayConstant, outsideAwayCoefficient,
            Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
          rw [congrFun (directionRow_simpleEdge_at_other
              pos v p r hvp hvr.symm hpr.symm) j,
            congrFun (directionRow_simpleEdge_at_other
              pos v q r hvq hvr.symm hqr.symm) j,
            congrFun (directionRow_simpleEdge_at_right pos v r hvr) j]
          simp [vertexLoad, hpr, hqr]
          ring
        · simp only [outsideAwayConstant, outsideAwayCoefficient,
            Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
          rw [congrFun (directionRow_simpleEdge_at_other
              pos v p u hvp huv hup) j,
            congrFun (directionRow_simpleEdge_at_other
              pos v q u hvq huv huq) j,
            congrFun (directionRow_simpleEdge_at_other
              pos v r u hvr huv hur) j]
          simp [vertexLoad, hup, huq, hur]

omit [Fintype V] [DecidableEq V] in
/-- Collinearity of three scalar-extended points descends to the smaller
field when two of the points are distinct. -/
theorem collinear_restrictScalars_for_response
    {L : Type*} [Field L] [Algebra L K]
    (p q r : Fin 3 → L) (hpq : p ≠ q)
    (hcol : PinCollinearity.Collinear
      (fun j ↦ algebraMap L K (p j))
      (fun j ↦ algebraMap L K (q j))
      (fun j ↦ algebraMap L K (r j))) :
    PinCollinearity.Collinear p q r := by
  have hpqK : (fun j ↦ algebraMap L K (p j)) ≠
      (fun j ↦ algebraMap L K (q j)) := by
    intro h
    apply hpq
    funext j
    exact (RingHom.injective (algebraMap L K)) (congrFun h j)
  obtain ⟨s, hs⟩ :=
    (collinear_iff_exists_smul_difference
      (fun j ↦ algebraMap L K (p j))
      (fun j ↦ algebraMap L K (q j))
      (fun j ↦ algebraMap L K (r j)) hpqK).1 hcol
  have hCoordinate : ∃ j : Fin 3, q j - p j ≠ 0 := by
    by_contra h
    push Not at h
    apply hpq
    funext j
    exact sub_eq_zero.mp (h j) |>.symm
  obtain ⟨j, hj⟩ := hCoordinate
  let t : L := (r j - p j) / (q j - p j)
  have hsEq : s = algebraMap L K t := by
    have hsj := congrFun hs j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsj
    have hjK : algebraMap L K (q j - p j) ≠ 0 := by
      intro hzero
      apply hj
      apply RingHom.injective (algebraMap L K)
      simpa using hzero
    have htMul : t * (q j - p j) = r j - p j := by
      exact div_mul_cancel₀ (r j - p j) hj
    have hmap := congrArg (algebraMap L K) htMul
    simp only [map_mul, map_sub] at hmap
    apply mul_right_cancel₀ hjK
    calc
      s * algebraMap L K (q j - p j) =
          algebraMap L K (r j - p j) := by
        simpa only [map_sub] using hsj.symm
      _ = algebraMap L K t * algebraMap L K (q j - p j) := by
        simpa only [map_sub] using hmap.symm
  apply (collinear_iff_exists_smul_difference p q r hpq).2
  refine ⟨t, ?_⟩
  funext i
  apply (RingHom.injective (algebraMap L K))
  have hi := congrFun hs i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  rw [map_mul, map_sub]
  rw [← hsEq]
  simpa only [map_sub] using hi

set_option maxHeartbeats 800000 in
/-- **PF outside full response.**  A genuinely exceptional degree-at-most
three outside star forces all three virtual neighbour rows into the child
row space.  The returned packet is the packet produced by the literal
exceptional classification. -/
theorem outsideExceptional_fullResponse
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a)
    (hDegree : edgeSetDegree F v ≤ 3)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤)
    (hExceptional : OutsideExceptional (k := k) F a v) :
    ∃ N : DegreeThreeNeighbours F v,
      edgeSetDegree F v = 3 ∧
      outsideExtensionTrdeg (k := k) a v = 3 ∧
      outsideResponseKernelDim F a v = 1 ∧
      PinCollinearity.Collinear (a N.p) (a N.q) (a N.r) ∧
      directionRow a (simpleEdge N.p N.q N.hpq) ∈
          directionRowSpace (deleteVertexEdges F v) a ∧
      directionRow a (simpleEdge N.p N.r N.hpr) ∈
          directionRowSpace (deleteVertexEdges F v) a ∧
      directionRow a (simpleEdge N.q N.r N.hqr) ∈
          directionRowSpace (deleteVertexEdges F v) a := by
  obtain ⟨N, hCollinear, hpqA, hprA, hqrA, hTrdegThree,
      hResponseOne, hKernelOne, hRankTwo, hConnectingZero⟩ :=
    outsideExceptional_classification (k := k) F a v ha hDegree hgen hExceptional
  have hDegreeThree : edgeSetDegree F v = 3 := by
    have hRankNullity := outsideLocalRank_add_kernelDim_eq_degree F a v
    rw [hRankTwo, hKernelOne] at hRankNullity
    omega
  let L : IntermediateField k K := retainedCoordinateField (k := k) a v
  let b : V → Fin 3 → L := retainedZeroPlacement (k := k) a v
  have hbp : (fun j ↦ algebraMap L K (b N.p j)) = a N.p := by
    funext j
    exact retainedZeroPlacement_apply_of_ne
      (k := k) a v N.p N.hvp.symm j
  have hbq : (fun j ↦ algebraMap L K (b N.q j)) = a N.q := by
    funext j
    exact retainedZeroPlacement_apply_of_ne
      (k := k) a v N.q N.hvq.symm j
  have hbr : (fun j ↦ algebraMap L K (b N.r j)) = a N.r := by
    funext j
    exact retainedZeroPlacement_apply_of_ne
      (k := k) a v N.r N.hvr.symm j
  have hbpq : b N.p ≠ b N.q := by
    intro h
    apply N.hpq
    apply ha
    rw [← hbp, ← hbq, h]
  have hCollinearL :
      PinCollinearity.Collinear (b N.p) (b N.q) (b N.r) := by
    apply collinear_restrictScalars_for_response
      (K := K) (b N.p) (b N.q) (b N.r) hbpq
    simpa only [hbp, hbq, hbr] using hCollinear
  obtain ⟨t, hline⟩ :=
    (collinear_iff_exists_smul_difference
      (b N.p) (b N.q) (b N.r) hbpq).1 hCollinearL
  have htZero : t ≠ 0 := by
    intro ht
    have hEqL : b N.r = b N.p := by
      funext j
      have hj := congrFun hline j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj
      rw [ht] at hj
      simp only [zero_mul] at hj
      linear_combination hj
    apply N.hpr
    apply ha
    rw [← hbp, ← hbr, hEqL]
  have htOne : t ≠ 1 := by
    intro ht
    have hEqL : b N.r = b N.q := by
      funext j
      have hj := congrFun hline j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj
      rw [ht] at hj
      simp only [one_mul] at hj
      linear_combination hj
    apply N.hqr
    apply ha
    rw [← hbq, ← hbr, hEqL]
  have hOneSub : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm htOne)
  have hIndependent : AlgebraicIndependent L (deletedCoordinates a v) := by
    apply deletedCoordinates_algebraicIndependent_of_three_le_trdeg
      (k := k) a v
    · exact adjoin_retained_union_deleted_eq_top (k := k) a v hgen
    · rw [hTrdegThree]
  let ep : incidentEdges F v :=
    ⟨simpleEdge v N.p N.hvp,
      mem_incidentEdges.mpr
        ⟨N.vp_mem, by rw [vertices_simpleEdge]; simp⟩⟩
  let eq : incidentEdges F v :=
    ⟨simpleEdge v N.q N.hvq,
      mem_incidentEdges.mpr
        ⟨N.vq_mem, by rw [vertices_simpleEdge]; simp⟩⟩
  let er : incidentEdges F v :=
    ⟨simpleEdge v N.r N.hvr,
      mem_incidentEdges.mpr
        ⟨N.vr_mem, by rw [vertices_simpleEdge]; simp⟩⟩
  let localWeight : incidentEdges F v → K :=
    Pi.single ep (algebraMap L K (1 - t)) +
      Pi.single eq (algebraMap L K t) + Pi.single er (-1)
  have hLineK : a N.r - a N.p =
      algebraMap L K t • (a N.q - a N.p) := by
    rw [← hbp, ← hbq, ← hbr]
    funext j
    have hj := congrFun hline j
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
      using congrArg (algebraMap L K) hj
  have hLocalKernel : localEquilibriumAt F a v localWeight = 0 := by
    change localEquilibriumAt F a v
      (Pi.single ep (algebraMap L K (1 - t)) +
        Pi.single eq (algebraMap L K t) + Pi.single er (-1)) = 0
    rw [map_add, map_add, localEquilibriumAt_piSingle,
      localEquilibriumAt_piSingle, localEquilibriumAt_piSingle]
    change
      algebraMap L K (1 - t) •
          directionRow a (simpleEdge v N.p N.hvp) v +
        algebraMap L K t •
          directionRow a (simpleEdge v N.q N.hvq) v +
        (-1 : K) • directionRow a (simpleEdge v N.r N.hvr) v = 0
    rw [directionRow_simpleEdge_at_left,
      directionRow_simpleEdge_at_left, directionRow_simpleEdge_at_left]
    funext j
    have hj := congrFun hLineK j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      map_sub, map_one, Pi.zero_apply] at hj ⊢
    linear_combination hj
  let localRelation : LinearMap.ker (localEquilibriumAt F a v) :=
    ⟨localWeight, hLocalKernel⟩
  have hClassZero : deletedConnectingClass F a v localRelation = 0 := by
    rw [hConnectingZero]
    rfl
  have hAwayMem :=
    (deletedConnectingClass_eq_zero_iff F a v localRelation).1 hClassZero
  let fullLoad : V → Fin 3 → K :=
    directionEquilibrium (incidentEdges F v) a localWeight
  have hFullAtV : fullLoad v = 0 := by
    exact hLocalKernel
  have hFullMem : fullLoad ∈ directionRowSpace (deleteVertexEdges F v) a := by
    change localToOldEquilibrium F a v localWeight ∈
      deletedAwayRowSpace F a v at hAwayMem
    change restrictAway v fullLoad ∈
      (directionRowSpace (deleteVertexEdges F v) a).map (restrictAway v)
      at hAwayMem
    obtain ⟨childLoad, hChildLoad, hChildRestrict⟩ :=
      Submodule.mem_map.mp hAwayMem
    have hChildAtV : childLoad v = 0 := by
      have hChildRange := hChildLoad
      rw [directionRowSpace_eq_range] at hChildRange
      obtain ⟨childWeight, rfl⟩ := hChildRange
      exact old_packet_equilibrium_at_deleted F a v childWeight
    have hEq : childLoad = fullLoad := by
      funext z
      by_cases hz : z = v
      · subst z
        rw [hChildAtV, hFullAtV]
      · exact congrFun hChildRestrict ⟨z, hz⟩
    rwa [← hEq]
  let constant : V → Fin 3 → L :=
    outsideAwayConstant b N.p N.q N.r t
  let coefficient : Fin 3 → V → Fin 3 → L :=
    fun j ↦ outsideAwayCoefficient N.p N.q N.r t (coordinateUnit j)
  have hFullFormula : fullLoad =
      algebraMap L K (1 - t) • directionRow a (simpleEdge v N.p N.hvp) +
        algebraMap L K t • directionRow a (simpleEdge v N.q N.hvq) +
        (-1 : K) • directionRow a (simpleEdge v N.r N.hvr) := by
    change directionEquilibrium (incidentEdges F v) a
      (Pi.single ep (algebraMap L K (1 - t)) +
        Pi.single eq (algebraMap L K t) + Pi.single er (-1)) = _
    rw [map_add, map_add, directionEquilibrium_piSingle,
      directionEquilibrium_piSingle, directionEquilibrium_piSingle]
  have hbp' : mapPlacement (K := K) b N.p = a N.p := hbp
  have hbq' : mapPlacement (K := K) b N.q = a N.q := hbq
  have hbr' : mapPlacement (K := K) b N.r = a N.r := hbr
  have hMapConstant : mapPlacement (K := K) constant =
      outsideAwayConstant a N.p N.q N.r (algebraMap L K t) := by
    calc
      mapPlacement (K := K) constant =
          outsideAwayConstant (mapPlacement (K := K) b)
            N.p N.q N.r (algebraMap L K t) := by
        exact mapPlacement_outsideAwayConstant
          (K := K) b N.p N.q N.r t
      _ = outsideAwayConstant a N.p N.q N.r (algebraMap L K t) := by
        unfold outsideAwayConstant
        rw [hbp', hbq', hbr']
  have hMapCoefficient (j : Fin 3) :
      mapPlacement (K := K) (coefficient j) =
        outsideAwayCoefficient N.p N.q N.r (algebraMap L K t)
          (coordinateUnit (k := K) j) := by
    calc
      mapPlacement (K := K) (coefficient j) =
          outsideAwayCoefficient N.p N.q N.r (algebraMap L K t)
            (fun c ↦ algebraMap L K (coordinateUnit (k := L) j c)) := by
        exact mapPlacement_outsideAwayCoefficient
          (K := K) N.p N.q N.r t (coordinateUnit j)
      _ = outsideAwayCoefficient N.p N.q N.r (algebraMap L K t)
          (coordinateUnit (k := K) j) := by
        rw [map_coordinateUnit (K := K) (L := L) j]
  have hAffineIdentity :
      mapPlacement (K := K) constant +
          ∑ j : Fin 3, deletedCoordinates a v j •
            mapPlacement (K := K) (coefficient j) = fullLoad := by
    calc
      mapPlacement (K := K) constant +
            ∑ j : Fin 3, deletedCoordinates a v j •
              mapPlacement (K := K) (coefficient j) =
          outsideAwayConstant a N.p N.q N.r (algebraMap L K t) +
            ∑ j : Fin 3, deletedCoordinates a v j •
              outsideAwayCoefficient N.p N.q N.r (algebraMap L K t)
                (coordinateUnit j) := by
        rw [hMapConstant]
        congr 1
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hMapCoefficient j]
      _ = outsideAwayConstant a N.p N.q N.r (algebraMap L K t) +
          outsideAwayCoefficient N.p N.q N.r (algebraMap L K t) (a v) := by
        congr 1
        simpa only [deletedCoordinates] using
          (outsideAwayCoefficient_eq_sum_coordinateUnit
            N.p N.q N.r (algebraMap L K t) (a v)).symm
      _ = algebraMap L K (1 - t) •
            directionRow a (simpleEdge v N.p N.hvp) +
          algebraMap L K t • directionRow a (simpleEdge v N.q N.hvq) +
          (-1 : K) • directionRow a (simpleEdge v N.r N.hvr) := by
        simpa only [map_sub, map_one] using
          (outsideAwayConstant_add_coefficient_eq_threeStar
            a v N.p N.q N.r N.hvp N.hvq N.hvr
              N.hpq N.hpr N.hqr (algebraMap L K t) hLineK)
      _ = fullLoad := hFullFormula.symm
  have hAffineMemCurried :
      mapPlacement (K := K) constant +
          ∑ j : Fin 3, deletedCoordinates a v j •
            mapPlacement (K := K) (coefficient j) ∈
        directionRowSpace (deleteVertexEdges F v)
          (mapPlacement (K := K) b) := by
    rw [hAffineIdentity,
      directionRowSpace_map_retainedZeroPlacement_delete (k := k)]
    exact hFullMem
  have hAffineMemFlat :
      FiniteFamilyBaseChange.mapVector (K := K) (flattenVector constant) +
          ∑ j : Fin 3, deletedCoordinates a v j •
            FiniteFamilyBaseChange.mapVector (K := K)
              (flattenVector (coefficient j)) ∈
        span K (Set.range (fun e : deleteVertexEdges F v ↦
          FiniteFamilyBaseChange.mapVector (K := K)
            (flattenVector (directionRow b e.1)))) := by
    have hFlat := (flattenVector_mem_span_iff
      (k := K)
      (fun e : deleteVertexEdges F v ↦
        directionRow (mapPlacement (K := K) b) e.1)
      (mapPlacement (K := K) constant +
        ∑ j : Fin 3, deletedCoordinates a v j •
          mapPlacement (K := K) (coefficient j))).2
      (by simpa [directionRowSpace] using hAffineMemCurried)
    have hFlatten :
        flattenVector (mapPlacement (K := K) constant +
          ∑ j : Fin 3, deletedCoordinates a v j •
            mapPlacement (K := K) (coefficient j)) =
        FiniteFamilyBaseChange.mapVector (K := K) (flattenVector constant) +
          ∑ j : Fin 3, deletedCoordinates a v j •
            FiniteFamilyBaseChange.mapVector (K := K)
              (flattenVector (coefficient j)) := by
      funext x
      simp [flattenVector, mapPlacement, FiniteFamilyBaseChange.mapVector,
        Pi.smul_apply, smul_eq_mul]
    rw [hFlatten] at hFlat
    simpa only [directionRow_mapPlacement] using hFlat
  have hDescended := AffineSpanDescent.affineCoefficients_mem_span
    (K := K)
    (fun e : deleteVertexEdges F v ↦ flattenVector (directionRow b e.1))
    (deletedCoordinates a v) hIndependent
    (flattenVector constant)
    (fun j ↦ flattenVector (coefficient j)) hAffineMemFlat
  let W : Submodule L (V × Fin 3 → L) :=
    span L (Set.range (fun e : deleteVertexEdges F v ↦
      flattenVector (directionRow b e.1)))
  have hConstant : flattenVector constant ∈ W := hDescended.1
  have hCoefficient : ∀ j, flattenVector (coefficient j) ∈ W :=
    hDescended.2
  have coefficientMem (z : Fin 3 → L) :
      flattenVector (outsideAwayCoefficient N.p N.q N.r t z) ∈ W := by
    let term : Fin 3 → (V × Fin 3 → L) :=
      fun j x ↦ z j * flattenVector (coefficient j) x
    have hFlatSum :
        flattenVector (outsideAwayCoefficient N.p N.q N.r t z) =
          ∑ j : Fin 3, term j := by
      rw [outsideAwayCoefficient_eq_sum_coordinateUnit]
      funext x
      simp only [flattenVector, Pi.smul_apply, Finset.sum_apply,
        smul_eq_mul, term, coefficient]
    rw [hFlatSum]
    apply W.sum_mem
    intro j _hj
    have hj := W.smul_mem (z j) (hCoefficient j)
    exact hj
  have hpqFlat :
      flattenVector (directionRow b (simpleEdge N.p N.q N.hpq)) ∈ W := by
    have hScaled := W.add_mem hConstant (coefficientMem (b N.r))
    change flattenVector
      (outsideAwayConstant b N.p N.q N.r t +
        outsideAwayCoefficient N.p N.q N.r t (b N.r)) ∈ W at hScaled
    rw [outsideAwayConstant_add_coefficient_r
      b N.p N.q N.r N.hpq N.hpr N.hqr t hline] at hScaled
    let row : V × Fin 3 → L :=
      flattenVector (directionRow b (simpleEdge N.p N.q N.hpq))
    change (fun x : V × Fin 3 ↦ (t * (1 - t)) * row x) ∈ W at hScaled
    have h := W.smul_mem (t * (1 - t))⁻¹ hScaled
    change (fun x : V × Fin 3 ↦
      (t * (1 - t))⁻¹ * ((t * (1 - t)) * row x)) ∈ W at h
    have hScalar : t * (1 - t) ≠ 0 := mul_ne_zero htZero hOneSub
    have hCancel : (fun x : V × Fin 3 ↦
        (t * (1 - t))⁻¹ * ((t * (1 - t)) * row x)) = row := by
      funext x
      rw [← mul_assoc, inv_mul_cancel₀ hScalar, one_mul]
    rw [hCancel] at h
    exact h
  have hqrFlat :
      flattenVector (directionRow b (simpleEdge N.q N.r N.hqr)) ∈ W := by
    have hScaled := W.smul_mem (1 - t)
      (W.add_mem hConstant (coefficientMem (b N.p)))
    let row : V × Fin 3 → L :=
      flattenVector (directionRow b (simpleEdge N.q N.r N.hqr))
    have hId := outsideAway_one_sub_t_smul_constant_add_coefficient_p
      b N.p N.q N.r N.hpq N.hpr N.hqr t hline
    have hFlatId : (fun x : V × Fin 3 ↦
        (1 - t) * (flattenVector constant x +
          flattenVector (outsideAwayCoefficient N.p N.q N.r t (b N.p)) x)) =
        (fun x : V × Fin 3 ↦ t * row x) := by
      funext x
      exact congrFun (congrFun hId x.1) x.2
    change (fun x : V × Fin 3 ↦
      (1 - t) * (flattenVector constant x +
        flattenVector (outsideAwayCoefficient N.p N.q N.r t (b N.p)) x)) ∈ W
      at hScaled
    rw [hFlatId] at hScaled
    have h := W.smul_mem t⁻¹ hScaled
    change (fun x : V × Fin 3 ↦ t⁻¹ * (t * row x)) ∈ W at h
    have hCancel : (fun x : V × Fin 3 ↦ t⁻¹ * (t * row x)) = row := by
      funext x
      rw [← mul_assoc, inv_mul_cancel₀ htZero, one_mul]
    rw [hCancel] at h
    exact h
  have hprFlat :
      flattenVector (directionRow b (simpleEdge N.p N.r N.hpr)) ∈ W := by
    have hScaled := W.smul_mem t
      (W.add_mem hConstant (coefficientMem (b N.q)))
    let row : V × Fin 3 → L :=
      flattenVector (directionRow b (simpleEdge N.p N.r N.hpr))
    have hId := outsideAway_t_smul_constant_add_coefficient_q
      b N.p N.q N.r N.hpq N.hpr N.hqr t hline
    have hFlatId : (fun x : V × Fin 3 ↦
        t * (flattenVector constant x +
          flattenVector (outsideAwayCoefficient N.p N.q N.r t (b N.q)) x)) =
        (fun x : V × Fin 3 ↦ (1 - t) * row x) := by
      funext x
      exact congrFun (congrFun hId x.1) x.2
    change (fun x : V × Fin 3 ↦
      t * (flattenVector constant x +
        flattenVector (outsideAwayCoefficient N.p N.q N.r t (b N.q)) x)) ∈ W
      at hScaled
    rw [hFlatId] at hScaled
    have h := W.smul_mem (1 - t)⁻¹ hScaled
    change (fun x : V × Fin 3 ↦ (1 - t)⁻¹ * ((1 - t) * row x)) ∈ W at h
    have hCancel : (fun x : V × Fin 3 ↦
        (1 - t)⁻¹ * ((1 - t) * row x)) = row := by
      funext x
      rw [← mul_assoc, inv_mul_cancel₀ hOneSub, one_mul]
    rw [hCancel] at h
    exact h
  have hpqL : directionRow b (simpleEdge N.p N.q N.hpq) ∈
      directionRowSpace (deleteVertexEdges F v) b := by
    apply (flattenVector_mem_span_iff
      (fun e : deleteVertexEdges F v ↦ directionRow b e.1)
      (directionRow b (simpleEdge N.p N.q N.hpq))).1
    exact hpqFlat
  have hprL : directionRow b (simpleEdge N.p N.r N.hpr) ∈
      directionRowSpace (deleteVertexEdges F v) b := by
    apply (flattenVector_mem_span_iff
      (fun e : deleteVertexEdges F v ↦ directionRow b e.1)
      (directionRow b (simpleEdge N.p N.r N.hpr))).1
    exact hprFlat
  have hqrL : directionRow b (simpleEdge N.q N.r N.hqr) ∈
      directionRowSpace (deleteVertexEdges F v) b := by
    apply (flattenVector_mem_span_iff
      (fun e : deleteVertexEdges F v ↦ directionRow b e.1)
      (directionRow b (simpleEdge N.q N.r N.hqr))).1
    exact hqrFlat
  have hpqK := directionRow_mem_mapPlacement_of_mem
    (K := K) (deleteVertexEdges F v) b
    (simpleEdge N.p N.q N.hpq) hpqL
  have hprK := directionRow_mem_mapPlacement_of_mem
    (K := K) (deleteVertexEdges F v) b
    (simpleEdge N.p N.r N.hpr) hprL
  have hqrK := directionRow_mem_mapPlacement_of_mem
    (K := K) (deleteVertexEdges F v) b
    (simpleEdge N.q N.r N.hqr) hqrL
  rw [directionRowSpace_map_retainedZeroPlacement_delete (k := k)] at hpqK hprK hqrK
  have hpqRow : directionRow
      (mapPlacement (K := K) b) (simpleEdge N.p N.q N.hpq) =
      directionRow a (simpleEdge N.p N.q N.hpq) := by
    apply directionRow_map_retainedZeroPlacement_of_avoids (k := k)
    simp [vertices_simpleEdge, N.hvp, N.hvq]
  have hprRow : directionRow
      (mapPlacement (K := K) b) (simpleEdge N.p N.r N.hpr) =
      directionRow a (simpleEdge N.p N.r N.hpr) := by
    apply directionRow_map_retainedZeroPlacement_of_avoids (k := k)
    simp [vertices_simpleEdge, N.hvp, N.hvr]
  have hqrRow : directionRow
      (mapPlacement (K := K) b) (simpleEdge N.q N.r N.hqr) =
      directionRow a (simpleEdge N.q N.r N.hqr) := by
    apply directionRow_map_retainedZeroPlacement_of_avoids (k := k)
    simp [vertices_simpleEdge, N.hvq, N.hvr]
  rw [hpqRow] at hpqK
  rw [hprRow] at hprK
  rw [hqrRow] at hqrK
  exact ⟨N, hDegreeThree, hTrdegThree, hResponseOne,
    hCollinear, hpqK, hprK, hqrK⟩

end

end DirectionStress

end RB31E2E


end
end BundleSource0042

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0042/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0042.json"

section BundleSource0043
/- Source: Papers/RigidityZheng_Linear_DirectionResponseVertexDeletion.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/DirectionResponseVertexDeletion.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Virtual responses under literal vertex deletion

This file combines the cross-type vertex-deletion equivalence with the
virtual-row augmentation calculus.  A response edge avoiding the deleted
vertex may be inserted either before deletion or after restricting to the
remaining-vertex subtype; the two presentations have the same stress
dimension.  Consequently a virtual response row in the parent deleted
graph becomes a virtual response row in the literal child graph, and then
descends further to the child's intrinsic coordinate field.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

open ProvenanceFlag Sparse22Transport

variable {L K V : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Restricting after inserting an edge which avoids `v` is literally
insertion of the restricted edge. -/
theorem restrictedLiveEdges_insert
    (F : SimpleEdgeSet V) (v : V) (f : SimpleEdge V)
    (hvf : v ∉ f.vertices) :
    restrictedLiveEdges (insert f F) v =
      insert (restrictSimpleEdge v f hvf) (restrictedLiveEdges F v) := by
  ext e
  rw [mem_restrictedLiveEdges_iff]
  constructor
  · intro he
    obtain ⟨heParent, heAvoid⟩ := mem_deleteVertexEdges.mp he
    rcases Finset.mem_insert.mp heParent with heEq | heF
    · rw [Finset.mem_insert]
      left
      apply mapSimpleEdge_injective (remainingVertexEmbedding v)
      rw [map_restrictSimpleEdge, heEq]
    · rw [Finset.mem_insert]
      right
      rw [mem_restrictedLiveEdges_iff]
      exact mem_deleteVertexEdges.mpr ⟨heF, heAvoid⟩
  · intro he
    rw [Finset.mem_insert] at he
    rcases he with heEq | heOld
    · subst e
      rw [map_restrictSimpleEdge]
      exact mem_deleteVertexEdges.mpr
        ⟨Finset.mem_insert_self _ _, hvf⟩
    · rw [mem_restrictedLiveEdges_iff] at heOld
      obtain ⟨heF, heAvoid⟩ := mem_deleteVertexEdges.mp heOld
      exact mem_deleteVertexEdges.mpr
        ⟨Finset.mem_insert_of_mem heF, heAvoid⟩

omit [Fintype V] in
/-- Stress after inserting an avoiding edge agrees in the parent-deleted
and literal-child presentations. -/
theorem directionStressDim_insert_restricted
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices) :
    directionStressDim
        (insert (restrictSimpleEdge v f hvf) (restrictedLiveEdges F v))
        (restrictPlacement a v) =
      directionStressDim (insert f (deleteVertexEdges F v)) a := by
  rw [← restrictedLiveEdges_insert F v f hvf]
  rw [directionStressDim_restrictedLiveEdges]
  congr 2
  ext e
  simp only [mem_deleteVertexEdges, Finset.mem_insert]
  constructor
  · rintro ⟨he, heAvoid⟩
    exact he.elim (fun h => Or.inl h) (fun h => Or.inr ⟨h, heAvoid⟩)
  · rintro (rfl | ⟨heF, heAvoid⟩)
    · exact ⟨Or.inl rfl, hvf⟩
    · exact ⟨Or.inr heF, heAvoid⟩

/-- Converse to virtual augmentation: for an absent edge, gaining exactly
one stress after insertion forces its row to have been in the old row
space. -/
theorem directionRow_mem_of_stress_insert_eq_add_one
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (f : SimpleEdge V)
    (hf : f ∉ F)
    (hStress : directionStressDim (insert f F) a =
      directionStressDim F a + 1) :
    directionRow a f ∈ directionRowSpace F a := by
  have hParent := directionStressDim_add_directionEquilibriumRank
    (insert f F) a
  have hOld := directionStressDim_add_directionEquilibriumRank F a
  have hRank : directionEquilibriumRank (insert f F) a =
      directionEquilibriumRank F a := by
    rw [Finset.card_insert_of_notMem hf, hStress] at hParent
    omega
  have hLe := directionRowSpace_le_insert F a f
  have hEq : directionRowSpace (insert f F) a = directionRowSpace F a := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hLe
    simpa only [directionEquilibriumRank_eq_finrank_rowSpace] using hRank.symm
  rw [← hEq]
  apply Submodule.subset_span
  exact ⟨⟨f, Finset.mem_insert_self _ _⟩, rfl⟩

/-- An ambient virtual response in the parent deleted graph restricts to a
virtual response in the literal child graph. -/
theorem directionRow_restrict_mem_of_deleted_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hf : f ∉ deleteVertexEdges F v)
    (hrow : directionRow a f ∈
      directionRowSpace (deleteVertexEdges F v) a) :
    directionRow (restrictPlacement a v) (restrictSimpleEdge v f hvf) ∈
      directionRowSpace (restrictedLiveEdges F v)
        (restrictPlacement a v) := by
  have hParentStress := directionStressDim_insert_eq_add_one_of_row_mem
    (deleteVertexEdges F v) a f hf hrow
  have hChildOld := directionStressDim_restrictedLiveEdges F a v
  have hChildInserted :=
    directionStressDim_insert_restricted F a v f hvf
  have hChildStress :
      directionStressDim
          (insert (restrictSimpleEdge v f hvf) (restrictedLiveEdges F v))
          (restrictPlacement a v) =
        directionStressDim (restrictedLiveEdges F v)
          (restrictPlacement a v) + 1 := by
    rw [hChildInserted, hParentStress, hChildOld]
  have hfChild : restrictSimpleEdge v f hvf ∉ restrictedLiveEdges F v := by
    intro hmem
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge] at hmem
    exact hf hmem
  exact directionRow_mem_of_stress_insert_eq_add_one
    (restrictedLiveEdges F v) (restrictPlacement a v)
    (restrictSimpleEdge v f hvf) hfChild hChildStress

/-- Final intrinsic form: if the parent ambient deleted graph carries a
virtual response edge, then the same restricted edge is in the child row
space over the field generated by the retained coordinates. -/
theorem directionRow_intrinsicRestricted_mem_of_deleted_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hf : f ∉ deleteVertexEdges F v)
    (hrow : directionRow a f ∈
      directionRowSpace (deleteVertexEdges F v) a) :
    directionRow
        (ProvenanceFlag.intrinsicRestrictedPlacement (k := L) a v)
        (restrictSimpleEdge v f hvf) ∈
      directionRowSpace (restrictedLiveEdges F v)
        (ProvenanceFlag.intrinsicRestrictedPlacement (k := L) a v) := by
  apply directionRow_mem_of_mapPlacement_mem
    (K := K) (restrictedLiveEdges F v)
    (ProvenanceFlag.intrinsicRestrictedPlacement (k := L) a v)
    (restrictSimpleEdge v f hvf)
  rw [ProvenanceFlag.map_intrinsicRestrictedPlacement]
  exact directionRow_restrict_mem_of_deleted_mem F a v f hvf hf hrow

end

end DirectionStress

end RB31E2E


end
end BundleSource0043

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0043/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0043.json"

section BundleSource0044
/- Source: Papers/RigidityZheng_Linear_PrivatePivotStress.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/PrivatePivotStress.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Direction-stress invariance under a private flag pivot

On three distinct collinear placed points, every triangle direction row is
in the span of the other two.  Consequently exchanging one live terminal
edge for the distinguished missing terminal edge preserves both the
literal row space and the stress dimension.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

universe u w

variable {K : Type u} {V : Type w}
  [Field K] [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem directionRow_mem_rowSpace_of_mem
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K)
    (e : SimpleEdge V) (he : e ∈ F) :
    directionRow pos e ∈ directionRowSpace F pos := by
  apply Submodule.subset_span
  exact ⟨⟨e, he⟩, rfl⟩

omit [Fintype V] in
/-- For three distinct collinear points, the edge between the second and
third points is a virtual response row generated by the two star edges at
the first point. -/
theorem triangleThirdRow_mem_of_collinear
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxyMem : simpleEdge x y hxy ∈ F)
    (hxzMem : simpleEdge x z hxz ∈ F)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos x) (pos y) (pos z)) :
    directionRow pos (simpleEdge y z hyz) ∈ directionRowSpace F pos := by
  have hxyPos : pos x ≠ pos y := fun h ↦ hxy (hpos h)
  obtain ⟨t, hline⟩ :=
    (collinear_iff_exists_smul_difference
      (pos x) (pos y) (pos z) hxyPos).1 hcol
  have ht : t ≠ 0 := by
    intro htZero
    apply hxz
    apply hpos
    exact (sub_eq_zero.mp (by simpa [htZero] using hline)).symm
  have hxyRow := directionRow_mem_rowSpace_of_mem
    F pos (simpleEdge x y hxy) hxyMem
  have hxzRow := directionRow_mem_rowSpace_of_mem
    F pos (simpleEdge x z hxz) hxzMem
  have hScaled :
      t • directionRow pos (simpleEdge y z hyz) ∈
        directionRowSpace F pos := by
    rw [triangleRows_scaled_identity pos x y z hxy hxz hyz t hline]
    exact (directionRowSpace F pos).add_mem
      ((directionRowSpace F pos).smul_mem _ hxyRow)
      ((directionRowSpace F pos).smul_mem _ hxzRow)
  have hCancel := (directionRowSpace F pos).smul_mem t⁻¹ hScaled
  have htCancel : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  simpa only [smul_smul, htCancel, one_smul] using hCancel

omit [Fintype V] in
/-- The second star edge is likewise generated by the first star edge and
the opposite triangle edge. -/
theorem triangleSecondRow_mem_of_collinear
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxyMem : simpleEdge x y hxy ∈ F)
    (hyzMem : simpleEdge y z hyz ∈ F)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos x) (pos y) (pos z)) :
    directionRow pos (simpleEdge x z hxz) ∈ directionRowSpace F pos := by
  have hxyPos : pos x ≠ pos y := fun h ↦ hxy (hpos h)
  obtain ⟨t, hline⟩ :=
    (collinear_iff_exists_smul_difference
      (pos x) (pos y) (pos z) hxyPos).1 hcol
  have htOne : t - 1 ≠ 0 := by
    intro ht
    have htEq : t = 1 := sub_eq_zero.mp ht
    apply hyz
    apply hpos
    have hzero : pos z - pos y = 0 := by
      funext j
      have hj := congrFun hline j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at hj ⊢
      rw [htEq] at hj
      linear_combination hj
    exact (sub_eq_zero.mp hzero).symm
  have hxyRow := directionRow_mem_rowSpace_of_mem
    F pos (simpleEdge x y hxy) hxyMem
  have hyzRow := directionRow_mem_rowSpace_of_mem
    F pos (simpleEdge y z hyz) hyzMem
  have hIdentity :=
    triangleRows_scaled_identity pos x y z hxy hxz hyz t hline
  have hScaled :
      (t - 1) • directionRow pos (simpleEdge x z hxz) ∈
        directionRowSpace F pos := by
    have hEq :
        (t - 1) • directionRow pos (simpleEdge x z hxz) =
          t • directionRow pos (simpleEdge y z hyz) -
            (t * (1 - t)) • directionRow pos (simpleEdge x y hxy) := by
      rw [hIdentity]
      module
    rw [hEq]
    exact (directionRowSpace F pos).sub_mem
      ((directionRowSpace F pos).smul_mem _ hyzRow)
      ((directionRowSpace F pos).smul_mem _ hxyRow)
  have hCancel := (directionRowSpace F pos).smul_mem (t - 1)⁻¹ hScaled
  have htCancel : (t - 1)⁻¹ * (t - 1) = 1 := inv_mul_cancel₀ htOne
  simpa only [smul_smul, htCancel, one_smul] using hCancel

omit [Fintype V] in
/-- Exchanging one labelled row for a genuinely new labelled row preserves
the row space when each exchanged row lies in the other system's span. -/
theorem directionRowSpace_exchange_eq
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K)
    (remove add : SimpleEdge V)
    (_hRemove : remove ∈ F) (_hAdd : add ∉ F)
    (hAddRow : directionRow pos add ∈ directionRowSpace F pos)
    (hRemoveRow : directionRow pos remove ∈
      directionRowSpace (insert add (F.erase remove)) pos) :
    directionRowSpace (insert add (F.erase remove)) pos =
      directionRowSpace F pos := by
  apply le_antisymm
  · rw [directionRowSpace, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    by_cases hea : e.1 = add
    · change directionRow pos e.1 ∈ directionRowSpace F pos
      rw [hea]
      exact hAddRow
    · apply Submodule.subset_span
      have heErase : e.1 ∈ F.erase remove :=
        (Finset.mem_insert.mp e.2).resolve_left hea
      exact ⟨⟨e.1, Finset.mem_erase.mp heErase |>.2⟩, rfl⟩
  · rw [directionRowSpace, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    by_cases her : e.1 = remove
    · change directionRow pos e.1 ∈
        directionRowSpace (insert add (F.erase remove)) pos
      rw [her]
      exact hRemoveRow
    · apply Submodule.subset_span
      exact ⟨⟨e.1, Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨her, e.2⟩)⟩, rfl⟩

/-- Stress dimension is invariant under a collinear terminal-edge pivot. -/
theorem directionStressDim_exchange_collinear_triangle
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxyMem : simpleEdge x y hxy ∈ F)
    (hxzMem : simpleEdge x z hxz ∈ F)
    (hyzNotMem : simpleEdge y z hyz ∉ F)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos x) (pos y) (pos z)) :
    directionStressDim
        (insert (simpleEdge y z hyz) (F.erase (simpleEdge x z hxz))) pos =
      directionStressDim F pos := by
  let F' := insert (simpleEdge y z hyz) (F.erase (simpleEdge x z hxz))
  have hxyF' : simpleEdge x y hxy ∈ F' := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_erase.mpr
      ⟨by
        intro hEq
        rw [simpleEdge_eq_simpleEdge_iff] at hEq
        rcases hEq with h | h
        · exact hyz h.2
        · exact hxz h.1,
       hxyMem⟩
  have hyzF' : simpleEdge y z hyz ∈ F' := Finset.mem_insert_self _ _
  have hAddRow : directionRow pos (simpleEdge y z hyz) ∈
      directionRowSpace F pos :=
    triangleThirdRow_mem_of_collinear F pos x y z hxy hxz hyz
      hxyMem hxzMem hpos hcol
  have hRemoveRow : directionRow pos (simpleEdge x z hxz) ∈
      directionRowSpace F' pos :=
    triangleSecondRow_mem_of_collinear F' pos x y z hxy hxz hyz
      hxyF' hyzF' hpos hcol
  have hRows : directionRowSpace F' pos = directionRowSpace F pos :=
    directionRowSpace_exchange_eq F pos
      (simpleEdge x z hxz) (simpleEdge y z hyz)
      hxzMem hyzNotMem hAddRow hRemoveRow
  have hRank : directionEquilibriumRank F' pos =
      directionEquilibriumRank F pos := by
    rw [directionEquilibriumRank_eq_finrank_rowSpace,
      directionEquilibriumRank_eq_finrank_rowSpace, hRows]
  have hAddNotErase : simpleEdge y z hyz ∉
      F.erase (simpleEdge x z hxz) := by
    exact fun h ↦ hyzNotMem (Finset.mem_erase.mp h).2
  have hCard : F'.card = F.card := by
    dsimp [F']
    rw [Finset.card_insert_of_notMem hAddNotErase,
      Finset.card_erase_of_mem hxzMem]
    have hCardPos : 0 < F.card :=
      Finset.card_pos.mpr ⟨simpleEdge x z hxz, hxzMem⟩
    omega
  have hPivot := directionStressDim_add_directionEquilibriumRank F' pos
  have hOriginal := directionStressDim_add_directionEquilibriumRank F pos
  rw [hRank, hCard] at hPivot
  exact Nat.add_right_cancel (hPivot.trans hOriginal.symm)

end

end DirectionStress

end RB31E2E


end
end BundleSource0044

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0044/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0044.json"

section BundleSource0045
/- Source: Papers/RigidityZheng_Linear_OutsideRegistrationStress.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/OutsideRegistrationStress.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Stress payment for registering a complete collinear triangle

If all three edges of a triangle are live and its three placed vertices are
distinct and collinear, deleting any one triangle row lowers stress nullity
by exactly one.  The remaining two rows span the deleted row, so rank stays
fixed while the labelled edge count drops by one.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {K V : Type*}
  [Field K] [Fintype V] [DecidableEq V]

/-- Erasing the `pq` row of a complete collinear triangle lowers the stress
dimension by one. -/
theorem directionStressDim_eq_erase_triangle_add_one
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K)
    (p q r : V) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpqMem : simpleEdge p q hpq ∈ F)
    (hprMem : simpleEdge p r hpr ∈ F)
    (hqrMem : simpleEdge q r hqr ∈ F)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos p) (pos q) (pos r)) :
    directionStressDim F pos =
      directionStressDim (F.erase (simpleEdge p q hpq)) pos + 1 := by
  let F0 := F.erase (simpleEdge p q hpq)
  have hpr_ne_pq : simpleEdge p r hpr ≠ simpleEdge p q hpq := by
    intro h
    rw [simpleEdge_eq_simpleEdge_iff] at h
    rcases h with h | h
    · exact hqr h.2.symm
    · exact hpq h.1
  have hqr_ne_pq : simpleEdge q r hqr ≠ simpleEdge p q hpq := by
    intro h
    rw [simpleEdge_eq_simpleEdge_iff] at h
    rcases h with h | h
    · exact hpq h.1.symm
    · exact hpr h.2.symm
  have hprF0 : simpleEdge r p hpr.symm ∈ F0 := by
    rw [simpleEdge_comm r p hpr.symm]
    exact Finset.mem_erase.mpr ⟨hpr_ne_pq, hprMem⟩
  have hqrF0 : simpleEdge r q hqr.symm ∈ F0 := by
    rw [simpleEdge_comm r q hqr.symm]
    exact Finset.mem_erase.mpr ⟨hqr_ne_pq, hqrMem⟩
  have hcolRPQ :
      PinCollinearity.Collinear (pos r) (pos p) (pos q) :=
    collinear_cycle (pos q) (pos r) (pos p)
      (collinear_cycle (pos p) (pos q) (pos r) hcol)
  have hrow : directionRow pos (simpleEdge p q hpq) ∈
      directionRowSpace F0 pos := by
    exact triangleThirdRow_mem_of_collinear F0 pos r p q
      hpr.symm hqr.symm hpq hprF0 hqrF0 hpos hcolRPQ
  have hAug := directionStressDim_insert_eq_add_one_of_row_mem
    F0 pos (simpleEdge p q hpq) (by simp [F0]) hrow
  have hRecover : insert (simpleEdge p q hpq) F0 = F := by
    exact Finset.insert_erase hpqMem
  rw [hRecover] at hAug
  exact hAug

end

end DirectionStress

end RB31E2E


end
end BundleSource0045

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0045/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0045.json"

section BundleSource0046
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagOutsideExceptionalBudget.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagOutsideExceptionalBudget.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/






@[expose] public section

/-!
# The exceptional outside budget

This file closes both outcomes of the exceptional outside degree-three
move.  In the incomplete outcome, a virtual neighbour row is inserted in
the literal outside child and recursive semismallness is transported back
with no numerical loss.  In the complete outcome, one collinear triangle
row is erased and the neighbour triple is registered as a new flag; stress
and flag codimension change by exactly two.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The edge returned by the triangle alternative is absent from the live
graph, since every lifted live edge belongs to the completion. -/
theorem outside_addable_edge_not_live
    (S : State V Flag) (f : SimpleEdge V)
    (hf : liftLiveEdge (Flag := Flag) f ∉ S.completionEdges) :
    f ∉ S.edges := by
  intro hfLive
  exact hf (S.liftedLiveEdges_subset_completionEdges
    ((S.mem_liftedLiveEdges f).2 hfLive))

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
/-- Mapping the literal child edge joining two retained vertices recovers
the corresponding parent simple edge. -/
theorem mapSimpleEdge_remaining_simpleEdge
    (v p q : V) (hpv : p ≠ v) (hqv : q ≠ v) (hpq : p ≠ q) :
    Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
        (simpleEdge (⟨p, hpv⟩ : RemainingVertex v) ⟨q, hqv⟩
          (by intro h; exact hpq (congrArg Subtype.val h))) =
      simpleEdge p q hpq := by
  apply Subtype.ext
  simp only [Sparse22Transport.mapSimpleEdge_val, simpleEdge, Sym2.map_mk]
  rfl

/-- Inserting an exceptional virtual response into the intrinsic outside
child produces exactly the parent's stress dimension. -/
theorem outside_insertedChild_stress_eq_parent
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hf : f ∉ deleteVertexEdges S.edges v)
    (hrow : directionRow Y.position f ∈
      directionRowSpace (deleteVertexEdges S.edges v) Y.position)
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1) :
    directionStressDim
        (insert (restrictSimpleEdge v f hvf)
          (S.deleteOutside v hv).edges)
        (intrinsicRestrictedPlacement (k := k) Y.position v) =
      Y.stressDim S := by
  have hIntrinsic := directionRow_intrinsicRestricted_mem_of_deleted_mem
    (L := k) S.edges Y.position v f hvf hf hrow
  have hfChild : restrictSimpleEdge v f hvf ∉
      (S.deleteOutside v hv).edges := by
    change restrictSimpleEdge v f hvf ∉ restrictedLiveEdges S.edges v
    intro hmem
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge] at hmem
    exact hf hmem
  change directionStressDim
      (insert (restrictSimpleEdge v f hvf)
        (restrictedLiveEdges S.edges v))
      (intrinsicRestrictedPlacement (k := k) Y.position v) =
    Y.stressDim S
  rw [directionStressDim_insert_eq_add_one_of_row_mem
    (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v)
    (restrictSimpleEdge v f hvf) hfChild hIntrinsic]
  have hIntrinsicStress := directionStressDim_intrinsicRestrictedPlacement
    (k := k) S.edges Y.position v
  rw [hIntrinsicStress]
  unfold FunctionFieldBranch.stressDim
  have hParentStress := directionStressDim_eq_delete_add_outsideResponseKernelDim
    S.edges Y.position v
  rw [hParentStress, hResponse]

/-- A recursive budget for the inserted outside child implies the parent
budget in the exceptional `d=3, u=1` branch. -/
theorem FunctionFieldBranch.semismallBudget_of_outsideInsertedIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (heMissing : ∀ t : Flag,
      restrictSimpleEdge v f hvf ≠ (S.deleteOutside v hv).missing t)
    (hf : f ∉ deleteVertexEdges S.edges v)
    (hrow : directionRow Y.position f ∈
      directionRowSpace (deleteVertexEdges S.edges v) Y.position)
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1)
    (hTrdeg : outsideExtensionTrdeg (k := k) Y.position v = 3)
    (hChild :
      ((Y.deleteOutsideIntrinsic S v hv).insertLiveEdge
        (S.deleteOutside v hv) (restrictSimpleEdge v f hvf) heMissing).SemismallBudget
        ((S.deleteOutside v hv).insertLiveEdge
          (restrictSimpleEdge v f hvf) heMissing)) :
    Y.SemismallBudget S := by
  let L := retainedLiveCoordinateField (k := k) Y.position v
  let childState := (S.deleteOutside v hv).insertLiveEdge
    (restrictSimpleEdge v f hvf) heMissing
  let childBranch := (Y.deleteOutsideIntrinsic S v hv).insertLiveEdge
    (S.deleteOutside v hv) (restrictSimpleEdge v f hvf) heMissing
  have hStress := outside_insertedChild_stress_eq_parent
    (k := k) S Y v hv f hvf hf hrow hResponse
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  have hVCard := card_remainingVertex_add_one v
  unfold FunctionFieldBranch.SemismallBudget at hChild ⊢
  change
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  change
    (directionStressDim (insert (restrictSimpleEdge v f hvf)
        (S.deleteOutside v hv).edges)
        (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k L + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) at hChild
  have hStressC :
      (directionStressDim S.edges Y.position : Cardinal) =
        directionStressDim (insert (restrictSimpleEdge v f hvf)
          (S.deleteOutside v hv).edges)
          (intrinsicRestrictedPlacement (k := k) Y.position v) := by
    exact_mod_cast hStress.symm
  calc
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) =
        ((directionStressDim (insert (restrictSimpleEdge v f hvf)
            (S.deleteOutside v hv).edges)
            (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k L + 2 * (Fintype.card Flag : Cardinal)) + 3 := by
      rw [hStressC, ← hTower, hTrdeg]
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 3 :=
      by simpa [add_comm] using add_le_add_left hChild 3
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 3 = 3 * Fintype.card V)

/-- In the complete branch, the registered child stress is exactly two
less than the parent stress. -/
theorem outside_registeredChild_stress_add_two_eq_parent
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges)
    (hcol : PinCollinearity.Collinear
      (Y.position N.p) (Y.position N.q) (Y.position N.r))
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1) :
    directionStressDim
        (S.registerOutside hSparse v hv N hTriangleLive).edges
        (intrinsicRestrictedPlacement (k := k) Y.position v) + 2 =
      Y.stressDim S := by
  let e : SimpleEdge (RemainingVertex v) :=
    restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
      (not_mem_degreeThreeNeighbourPair N _ (by simp))
  have hChildCol : PinCollinearity.Collinear
      ((intrinsicRestrictedPlacement (k := k) Y.position v) ⟨N.p, N.hvp.symm⟩)
      ((intrinsicRestrictedPlacement (k := k) Y.position v) ⟨N.q, N.hvq.symm⟩)
      ((intrinsicRestrictedPlacement (k := k) Y.position v) ⟨N.r, N.hvr.symm⟩) := by
    apply collinear_restrictScalars
      (k := k) (K := K)
      (retainedLiveCoordinateField (k := k) Y.position v)
      _ _ _
    · intro hpq
      exact N.hpq (Y.distinct (by
        funext j
        exact congrArg Subtype.val (congrFun hpq j)))
    · simpa [intrinsicRestrictedPlacement] using hcol
  have hpqMemChild : simpleEdge
      (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
      ⟨N.q, N.hvq.symm⟩ (by
        intro h; exact N.hpq (congrArg Subtype.val h)) ∈
      restrictedLiveEdges S.edges v := by
    rw [mem_restrictedLiveEdges_iff]
    rw [mapSimpleEdge_remaining_simpleEdge v N.p N.q N.hvp.symm N.hvq.symm N.hpq]
    exact mem_deleteVertexEdges.mpr
      ⟨hTriangleLive.1,
        not_mem_degreeThreeNeighbourPair N _ (by simp)⟩
  have hprMemChild : simpleEdge
      (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
      ⟨N.r, N.hvr.symm⟩ (by
        intro h; exact N.hpr (congrArg Subtype.val h)) ∈
      (S.deleteOutside v hv).edges := by
    change simpleEdge
        (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
        ⟨N.r, N.hvr.symm⟩ _ ∈ restrictedLiveEdges S.edges v
    rw [mem_restrictedLiveEdges_iff]
    rw [mapSimpleEdge_remaining_simpleEdge v N.p N.r N.hvp.symm N.hvr.symm N.hpr]
    exact mem_deleteVertexEdges.mpr
      ⟨hTriangleLive.2.1,
        not_mem_degreeThreeNeighbourPair N _ (by simp)⟩
  have hqrMemChild : simpleEdge
      (⟨N.q, N.hvq.symm⟩ : RemainingVertex v)
      ⟨N.r, N.hvr.symm⟩ (by
        intro h; exact N.hqr (congrArg Subtype.val h)) ∈
      (S.deleteOutside v hv).edges := by
    change simpleEdge
        (⟨N.q, N.hvq.symm⟩ : RemainingVertex v)
        ⟨N.r, N.hvr.symm⟩ _ ∈ restrictedLiveEdges S.edges v
    rw [mem_restrictedLiveEdges_iff]
    rw [mapSimpleEdge_remaining_simpleEdge v N.q N.r N.hvq.symm N.hvr.symm N.hqr]
    exact mem_deleteVertexEdges.mpr
      ⟨hTriangleLive.2.2,
        not_mem_degreeThreeNeighbourPair N _ (by simp)⟩
  have hErase := directionStressDim_eq_erase_triangle_add_one
    (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v)
    (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
    ⟨N.q, N.hvq.symm⟩ ⟨N.r, N.hvr.symm⟩
    (by intro h; exact N.hpq (congrArg Subtype.val h))
    (by intro h; exact N.hpr (congrArg Subtype.val h))
    (by intro h; exact N.hqr (congrArg Subtype.val h))
    hpqMemChild hprMemChild hqrMemChild
    (by
      intro a b hab
      apply Subtype.ext
      apply Y.distinct
      funext j
      exact congrArg Subtype.val (congrFun hab j)) hChildCol
  have hParentDelete := directionStressDim_eq_delete_add_outsideResponseKernelDim
    S.edges Y.position v
  have hIntrinsic := directionStressDim_intrinsicRestrictedPlacement
    (k := k) S.edges Y.position v
  have he : e = simpleEdge
      (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
      ⟨N.q, N.hvq.symm⟩ (by
        intro h; exact N.hpq (congrArg Subtype.val h)) := by
    apply Sparse22Transport.mapSimpleEdge_injective
      (remainingVertexEmbedding v)
    dsimp only [e]
    rw [map_restrictSimpleEdge, mapSimpleEdge_remaining_simpleEdge]
  change directionStressDim
      ((S.deleteOutside v hv).edges.erase e)
      (intrinsicRestrictedPlacement (k := k) Y.position v) + 2 = _
  change directionStressDim
      ((restrictedLiveEdges S.edges v).erase e)
      (intrinsicRestrictedPlacement (k := k) Y.position v) + 2 = _
  rw [he]
  unfold FunctionFieldBranch.stressDim
  rw [hIntrinsic] at hErase
  rw [hParentDelete, hResponse, hErase]

/-- A recursive budget on the genuinely registered intrinsic branch pays
the exceptional complete outside move exactly. -/
theorem FunctionFieldBranch.semismallBudget_of_registerOutsideIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges)
    (hcol : PinCollinearity.Collinear
      (Y.position N.p) (Y.position N.q) (Y.position N.r))
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1)
    (hTrdeg : outsideExtensionTrdeg (k := k) Y.position v = 3)
    (hChild :
      (Y.registerOutsideIntrinsic S hSparse v hv N hTriangleLive hcol).SemismallBudget
      (S.registerOutside hSparse v hv N hTriangleLive)) :
    Y.SemismallBudget S := by
  let L := retainedLiveCoordinateField (k := k) Y.position v
  let registered := S.registerOutside hSparse v hv N hTriangleLive
  have hStress := outside_registeredChild_stress_add_two_eq_parent
    (k := k) S Y hSparse v hv N hTriangleLive hcol hResponse
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  have hVCard := card_remainingVertex_add_one v
  have hFlagCard : Fintype.card (Flag ⊕ Unit) = Fintype.card Flag + 1 := by
    simp
  unfold FunctionFieldBranch.SemismallBudget at hChild ⊢
  change
    (directionStressDim registered.edges
        (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k L + 2 * (Fintype.card (Flag ⊕ Unit) : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) at hChild
  change
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  have hStressC :
      (directionStressDim S.edges Y.position : Cardinal) =
        (directionStressDim registered.edges
          (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) + 2 := by
    exact_mod_cast hStress.symm
  calc
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) =
        ((directionStressDim registered.edges
            (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k L + 2 * (Fintype.card (Flag ⊕ Unit) : Cardinal)) + 3 := by
      rw [hStressC, ← hTower, hTrdeg, hFlagCard]
      push_cast
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 3 :=
      by simpa [add_comm] using add_le_add_left hChild 3
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 3 = 3 * Fintype.card V)

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0046

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0046/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0046.json"

section BundleSource0047
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagOutsideExceptional.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagOutsideExceptional.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Closing the outside exceptional induction move

The full-response theorem supplies the actual degree-three neighbour
packet.  Completion sparsity then gives a complete-or-addable alternative.
Both alternatives construct literal smaller sparse states, so the supplied
strong-induction hypothesis is applied only to genuinely smaller live types.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The outside exceptional step.  The response rows and numerical
equalities follow from the local classification and coefficient descent. -/
theorem FunctionFieldBranch.semismallBudget_of_outsideExceptional
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V)
    (hSparse : S.CompletionSparse)
    (hv : S.flagMultiplicity v = 0)
    (hDegree : edgeSetDegree S.edges v ≤ 3)
    (hSmaller :
      ∀ {K' : Type v} {V' : Type w} {Flag' : Type x}
        [Field K'] [Algebra k K']
        [Fintype V'] [DecidableEq V'] [Fintype Flag'] [DecidableEq Flag'],
        Fintype.card V' < Fintype.card V →
          ∀ (S' : State V' Flag')
            (Y' : FunctionFieldBranch (k := k) (K := K') S'),
            S'.CompletionSparse → Y'.SemismallBudget S')
    (hExceptional : OutsideExceptional (k := k) S.edges Y.position v) :
    Y.SemismallBudget S := by
  obtain ⟨N, hDegreeThree, hTrdegThree, hResponseOne, hcol,
      hpqRow, hprRow, hqrRow⟩ :=
    outsideExceptional_fullResponse (k := k)
      S.edges Y.position v Y.distinct hDegree Y.generated hExceptional
  rcases S.outside_complete_or_exists_sparse_insertedChild
      hSparse v hv N hDegreeThree with hComplete | hAddable
  · have hTriangleLive :=
      S.outside_complete_triangle_live hSparse v hv N hComplete
    let registered := S.registerOutside hSparse v hv N hTriangleLive
    let child := Y.registerOutsideIntrinsic
      S hSparse v hv N hTriangleLive hcol
    have hCard : Fintype.card (RemainingVertex v) < Fintype.card V := by
      have hDrop := card_remainingVertex_add_one v
      omega
    have hChild : child.SemismallBudget registered := by
      exact hSmaller hCard registered child
        (S.registerOutside_completionSparse
          hSparse v hv N hTriangleLive)
    exact Y.semismallBudget_of_registerOutsideIntrinsic
      S hSparse v hv N hTriangleLive hcol hResponseOne hTrdegThree hChild
  · obtain ⟨f, hfTriangle, heMissing, hfAbsent, hChildSparse⟩ := hAddable
    let hvf := not_mem_degreeThreeNeighbourPair N f hfTriangle
    have hfLive : f ∉ S.edges := outside_addable_edge_not_live S f hfAbsent
    have hfDeleted : f ∉ deleteVertexEdges S.edges v := by
      intro h
      exact hfLive (mem_deleteVertexEdges.mp h).1
    have hrow : directionRow Y.position f ∈
        directionRowSpace (deleteVertexEdges S.edges v) Y.position := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfTriangle
      rcases hfTriangle with rfl | rfl | rfl
      · exact hpqRow
      · exact hprRow
      · exact hqrRow
    let childState := (S.deleteOutside v hv).insertLiveEdge
      (restrictSimpleEdge v f hvf) heMissing
    let childBase := Y.deleteOutsideIntrinsic S v hv
    let child := childBase.insertLiveEdge
      (S.deleteOutside v hv) (restrictSimpleEdge v f hvf) heMissing
    have hCard : Fintype.card (RemainingVertex v) < Fintype.card V := by
      have hDrop := card_remainingVertex_add_one v
      omega
    have hChild : child.SemismallBudget childState := by
      exact hSmaller hCard childState child hChildSparse
    exact Y.semismallBudget_of_outsideInsertedIntrinsic
      S v hv f hvf heMissing hfDeleted hrow hResponseOne hTrdegThree hChild

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0047

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0047/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0047.json"

section BundleSource0048
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagPrivateMove.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagPrivateMove.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# The private exceptional augmentation move

In a pivoted private
flag `T = {v,p,q}` the distinguished missing edge is `vq`, while `vp` and
`pq` are live.  If the degree-two star has second endpoint `z`, then after
deleting `v` and the consumed ghost `T`, at least one of `pz,qz` is a
genuinely absent edge whose insertion preserves completion sparsity.

The obstruction proof uses the literal tight completed `K₄` of the old
flag.  A blocking tight set containing `p,q` would uncross with this `K₄`
to a two-vertex tight set, impossible in a simple `(2,2)`-sparse graph.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

private theorem privateMove_two_le_card_of_pair_subset
    {W : Type*} [DecidableEq W] {F : SimpleEdgeSet W}
    {e f : SimpleEdge W} (hef : e ≠ f)
    (hsub : ({e, f} : SimpleEdgeSet W) ⊆ F) :
    2 ≤ F.card := by
  have hcard : ({e, f} : SimpleEdgeSet W).card = 2 := by simp [hef]
  rw [← hcard]
  exact Finset.card_le_card hsub

private theorem privateMove_three_le_card_of_triple_subset
    {W : Type*} [DecidableEq W] {F : SimpleEdgeSet W}
    {e f g : SimpleEdge W}
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hsub : ({e, f, g} : SimpleEdgeSet W) ⊆ F) :
    3 ≤ F.card := by
  have hcard : ({e, f, g} : SimpleEdgeSet W).card = 3 := by
    simp [hef, heg, hfg]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- No tight set in the double-deleted completion can contain both retained
endpoints of the consumed pivoted flag. -/
private theorem State.no_tightSet_in_privateDoubleDelete_containing_endpoints
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (_hvq : v ≠ q) (hpq : p ≠ q)
    (hTerminals : S.terminals t = {v, p, q})
    (U : Finset (V ⊕ Flag))
    (hU : Tight22
      (deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v)) U)
    (hpU : Sum.inl p ∈ U) (hqU : Sum.inl q ∈ U) :
    False := by
  let Q := deleteVertexEdges
    (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v)
  have hQSub : Q ⊆ S.completionEdges :=
    (deleteVertexEdges_subset _ _).trans (deleteVertexEdges_subset _ _)
  have hQSparse : Sparse22 Q := hSparse.mono hQSub
  have hvU : Sum.inl v ∉ U := by
    exact not_mem_of_tight22_deleteVertexEdges hQSparse hU hpU
      (by simpa using hvp)
  have hDeleteComm : Q =
      deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inl v)) (Sum.inr t) := by
    ext e
    simp only [Q, mem_deleteVertexEdges]
    tauto
  have hQSparseComm : Sparse22
      (deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inl v)) (Sum.inr t)) := by
    rw [← hDeleteComm]
    exact hQSparse
  have hUComm : Tight22
      (deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inl v)) (Sum.inr t)) U := by
    rw [← hDeleteComm]
    exact hU
  have htU : Sum.inr t ∉ U := by
    exact not_mem_of_tight22_deleteVertexEdges hQSparseComm hUComm hpU (by simp)
  have hInsideSub :
      edgesInside Q U ⊆ edgesInside S.completionEdges U :=
    edgesInside_mono_edges hQSub U
  have hLower := Finset.card_le_card hInsideSub
  have hUpper := hSparse U hU.1
  have hParentTight : Tight22 S.completionEdges U := by
    refine ⟨hU.1, ?_⟩
    rw [hU.2] at hLower
    omega
  let Kt := S.flagVertices t
  have hInterEq : U ∩ Kt = {Sum.inl p, Sum.inl q} := by
    ext x
    constructor
    · intro hx
      have hxU := (Finset.mem_inter.mp hx).1
      have hxK := (Finset.mem_inter.mp hx).2
      cases x with
      | inl a =>
          have haT : a ∈ S.terminals t :=
            (S.mem_flagVertices_live t a).1 hxK
          rw [hTerminals] at haT
          simp only [Finset.mem_insert, Finset.mem_singleton] at haT
          rcases haT with hav | hap | haq
          · subst a
            exact (hvU hxU).elim
          · apply Finset.mem_insert.mpr
            exact Or.inl (congrArg Sum.inl hap)
          · apply Finset.mem_insert.mpr
            exact Or.inr (Finset.mem_singleton.mpr (congrArg Sum.inl haq))
      | inr u =>
          have hut : u = t := (S.mem_flagVertices_ghost t u).1 hxK
          subst u
          exact (htU hxU).elim
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hxp | hxq
      · subst x
        exact Finset.mem_inter.mpr
          ⟨hpU, (S.mem_flagVertices_live t p).2 (by rw [hTerminals]; simp)⟩
      · subst x
        exact Finset.mem_inter.mpr
          ⟨hqU, (S.mem_flagVertices_live t q).2 (by rw [hTerminals]; simp)⟩
  have hInterNonempty : (U ∩ Kt).Nonempty :=
    ⟨Sum.inl p, Finset.mem_inter.mpr
      ⟨hpU, (S.mem_flagVertices_live t p).2 (by rw [hTerminals]; simp)⟩⟩
  have hInterTight :=
    (tight22_union_inter hSparse hParentTight
      (S.flagVertices_tight hSparse t) hInterNonempty).2
  have hInterTwo : 2 ≤ (U ∩ Kt).card := by
    rw [hInterEq]
    simp [hpq]
  have hFour := four_le_card_of_tight22 hInterTight hInterTwo
  rw [hInterEq] at hFour
  simp [hpq] at hFour

/-- In the pivoted private degree-two shape, one of the two
virtual response edges is genuinely addable to the completed child after
the private terminal and its unique ghost are consumed. -/
theorem State.private_response_edge_addable
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q z : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hvz : v ≠ z)
    (hpq : p ≠ q) (hpz : p ≠ z) (hqz : q ≠ z)
    (hTerminals : S.terminals t = {v, p, q})
    (hpqLive : simpleEdge p q hpq ∈ S.edges)
    (hvzLive : simpleEdge v z hvz ∈ S.edges) :
    ∃ f : SimpleEdge V,
      (f = simpleEdge p z hpz ∨ f = simpleEdge q z hqz) ∧
      liftLiveEdge (Flag := Flag) f ∉ S.completionEdges ∧
      Sparse22
        (insert (liftLiveEdge (Flag := Flag) f)
          (deleteVertexEdges
            (deleteVertexEdges S.completionEdges (Sum.inr t))
            (Sum.inl v))) := by
  let Q := deleteVertexEdges
    (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v)
  let epz : SimpleEdge V := simpleEdge p z hpz
  let eqz : SimpleEdge V := simpleEdge q z hqz
  let epzHat : SimpleEdge (V ⊕ Flag) := liftLiveEdge (Flag := Flag) epz
  let eqzHat : SimpleEdge (V ⊕ Flag) := liftLiveEdge (Flag := Flag) eqz
  have hQSub : Q ⊆ S.completionEdges :=
    (deleteVertexEdges_subset _ _).trans (deleteVertexEdges_subset _ _)
  have hQSparse : Sparse22 Q := hSparse.mono hQSub
  have hpT : p ∈ S.terminals t := by rw [hTerminals]; simp
  have hqT : q ∈ S.terminals t := by rw [hTerminals]; simp
  have hvT : v ∈ S.terminals t := by rw [hTerminals]; simp
  have hpqCompletion :
      liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ∈
        S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact hpqLive
  have hvzCompletion :
      liftLiveEdge (Flag := Flag) (simpleEdge v z hvz) ∈
        S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact hvzLive
  have hpqQ :
      liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ∈ Q := by
    apply mem_deleteVertexEdges.mpr
    refine ⟨mem_deleteVertexEdges.mpr ⟨hpqCompletion, ?_⟩, ?_⟩
    · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp
    · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp [hvp, hvq]
  have candidate_mem_Q_of_mem_completion_pz
      (h : epzHat ∈ S.completionEdges) : epzHat ∈ Q := by
    apply mem_deleteVertexEdges.mpr
    refine ⟨mem_deleteVertexEdges.mpr ⟨h, ?_⟩, ?_⟩
    · dsimp [epzHat, epz]
      rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp
    · dsimp [epzHat, epz]
      rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp [hvp, hvz]
  have candidate_mem_Q_of_mem_completion_qz
      (h : eqzHat ∈ S.completionEdges) : eqzHat ∈ Q := by
    apply mem_deleteVertexEdges.mpr
    refine ⟨mem_deleteVertexEdges.mpr ⟨h, ?_⟩, ?_⟩
    · dsimp [eqzHat, eqz]
      rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp
    · dsimp [eqzHat, eqz]
      rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp [hvq, hvz]
  have noBoth : ¬ (epzHat ∈ Q ∧ eqzHat ∈ Q) := by
    rintro ⟨hpzQ, hqzQ⟩
    let Kt := S.flagVertices t
    have hzKt : Sum.inl z ∉ Kt := by
      change Sum.inl z ∉ S.flagVertices t
      rw [S.mem_flagVertices_live, hTerminals]
      simp [Ne.symm hvz, Ne.symm hpz, Ne.symm hqz]
    have hpzCompletion : epzHat ∈ S.completionEdges := hQSub hpzQ
    have hqzCompletion : eqzHat ∈ S.completionEdges := hQSub hqzQ
    have hvzNew :
        liftLiveEdge (Flag := Flag) (simpleEdge v z hvz) ∈
          newEdgesAt S.completionEdges Kt (Sum.inl z) := by
      rw [mem_newEdgesAt]
      refine ⟨hvzCompletion, ?_, ?_⟩
      · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_of_mem
            ((S.mem_flagVertices_live t v).2 hvT),
          Finset.mem_insert_self _ _⟩
      · intro hsub
        exact hzKt (hsub (by rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]; simp))
    have hpzNew : epzHat ∈
        newEdgesAt S.completionEdges Kt (Sum.inl z) := by
      rw [mem_newEdgesAt]
      refine ⟨hpzCompletion, ?_, ?_⟩
      · dsimp [epzHat, epz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_of_mem
            ((S.mem_flagVertices_live t p).2 hpT),
          Finset.mem_insert_self _ _⟩
      · intro hsub
        exact hzKt (hsub (by
          dsimp [epzHat, epz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp))
    have hqzNew : eqzHat ∈
        newEdgesAt S.completionEdges Kt (Sum.inl z) := by
      rw [mem_newEdgesAt]
      refine ⟨hqzCompletion, ?_, ?_⟩
      · dsimp [eqzHat, eqz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_of_mem
            ((S.mem_flagVertices_live t q).2 hqT),
          Finset.mem_insert_self _ _⟩
      · intro hsub
        exact hzKt (hsub (by
          dsimp [eqzHat, eqz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp))
    have hvz_ne_pz :
        liftLiveEdge (Flag := Flag) (simpleEdge v z hvz) ≠ epzHat := by
      intro hEq
      have hLive : simpleEdge v z hvz = epz := liftLiveEdge_injective hEq
      dsimp [epz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hvp h.1
      · exact hvz h.1
    have hvz_ne_qz :
        liftLiveEdge (Flag := Flag) (simpleEdge v z hvz) ≠ eqzHat := by
      intro hEq
      have hLive : simpleEdge v z hvz = eqz := liftLiveEdge_injective hEq
      dsimp [eqz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hvq h.1
      · exact hvz h.1
    have hpz_ne_qz : epzHat ≠ eqzHat := by
      intro hEq
      have hLive : epz = eqz := liftLiveEdge_injective hEq
      dsimp [epz, eqz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hpq h.1
      · exact hpz h.1
    have hThree : 3 ≤
        (newEdgesAt S.completionEdges Kt (Sum.inl z)).card :=
      privateMove_three_le_card_of_triple_subset hvz_ne_pz hvz_ne_qz hpz_ne_qz (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hvzNew
        · exact hpzNew
        · exact hqzNew)
    have hAtMostTwo :
        (newEdgesAt S.completionEdges Kt (Sum.inl z)).card ≤ 2 := by
      simpa only [Kt] using card_newEdgesAt_le_two hSparse
        (S.flagVertices_tight hSparse t) hzKt
    omega
  have extend_by_p_tight
      (U : Finset (V ⊕ Flag))
      (hU : Tight22 Q U)
      (hqU : Sum.inl q ∈ U) (hzU : Sum.inl z ∈ U)
      (hpU : Sum.inl p ∉ U) (hpzQ : epzHat ∈ Q) :
      Tight22 Q (insert (Sum.inl p) U) := by
    have hpqNew :
        liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ∈
          newEdgesAt Q U (Sum.inl p) := by
      rw [mem_newEdgesAt]
      refine ⟨hpqQ, ?_, ?_⟩
      · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hqU⟩
      · intro hsub
        exact hpU (hsub (by rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]; simp))
    have hpzNew : epzHat ∈ newEdgesAt Q U (Sum.inl p) := by
      rw [mem_newEdgesAt]
      refine ⟨hpzQ, ?_, ?_⟩
      · dsimp [epzHat, epz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hzU⟩
      · intro hsub
        exact hpU (hsub (by
          dsimp [epzHat, epz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp))
    have hEdgesNe :
        liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ≠ epzHat := by
      intro hEq
      have hLive : simpleEdge p q hpq = epz := liftLiveEdge_injective hEq
      dsimp [epz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hqz h.2
      · exact hpz h.1
    have hLower : 2 ≤ (newEdgesAt Q U (Sum.inl p)).card :=
      privateMove_two_le_card_of_pair_subset hEdgesNe (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hpqNew
        · exact hpzNew)
    have hUpper := card_newEdgesAt_le_two hQSparse hU hpU
    apply tight22_insert_of_card_newEdgesAt_eq_two hU hpU
    omega
  have extend_by_q_tight
      (U : Finset (V ⊕ Flag))
      (hU : Tight22 Q U)
      (hpU : Sum.inl p ∈ U) (hzU : Sum.inl z ∈ U)
      (hqU : Sum.inl q ∉ U) (hqzQ : eqzHat ∈ Q) :
      Tight22 Q (insert (Sum.inl q) U) := by
    have hpqNew :
        liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ∈
          newEdgesAt Q U (Sum.inl q) := by
      rw [mem_newEdgesAt]
      refine ⟨hpqQ, ?_, ?_⟩
      · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_of_mem hpU, Finset.mem_insert_self _ _⟩
      · intro hsub
        exact hqU (hsub (by rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]; simp))
    have hqzNew : eqzHat ∈ newEdgesAt Q U (Sum.inl q) := by
      rw [mem_newEdgesAt]
      refine ⟨hqzQ, ?_, ?_⟩
      · dsimp [eqzHat, eqz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hzU⟩
      · intro hsub
        exact hqU (hsub (by
          dsimp [eqzHat, eqz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp))
    have hEdgesNe :
        liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ≠ eqzHat := by
      intro hEq
      have hLive : simpleEdge p q hpq = eqz := liftLiveEdge_injective hEq
      dsimp [eqz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hpq h.1
      · exact hpz h.1
    have hLower : 2 ≤ (newEdgesAt Q U (Sum.inl q)).card :=
      privateMove_two_le_card_of_pair_subset hEdgesNe (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hpqNew
        · exact hqzNew)
    have hUpper := card_newEdgesAt_le_two hQSparse hU hqU
    apply tight22_insert_of_card_newEdgesAt_eq_two hU hqU
    omega
  by_cases hpzQ : epzHat ∈ Q
  · have hqzQ : eqzHat ∉ Q := fun h ↦ noBoth ⟨hpzQ, h⟩
    by_cases hAdd : Sparse22 (insert eqzHat Q)
    · refine ⟨eqz, Or.inr rfl, ?_, hAdd⟩
      intro hParent
      exact hqzQ (candidate_mem_Q_of_mem_completion_qz hParent)
    · obtain ⟨U, _hUne, hqzU, hUTight⟩ :=
        exists_tight22_of_not_sparse22_insert hQSparse hqzQ hAdd
      have hqU : Sum.inl q ∈ U := by
        apply hqzU
        dsimp [eqzHat, eqz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        simp
      have hzU : Sum.inl z ∈ U := by
        apply hqzU
        dsimp [eqzHat, eqz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        simp
      by_cases hpU : Sum.inl p ∈ U
      · exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
          hSparse v p q t hvp hvq hpq hTerminals U hUTight hpU hqU).elim
      · have hInsertTight :=
          extend_by_p_tight U hUTight hqU hzU hpU hpzQ
        exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
          hSparse v p q t hvp hvq hpq hTerminals (insert (Sum.inl p) U)
          hInsertTight (by simp) (by simp [hqU])).elim
  · by_cases hqzQ : eqzHat ∈ Q
    · by_cases hAdd : Sparse22 (insert epzHat Q)
      · refine ⟨epz, Or.inl rfl, ?_, hAdd⟩
        intro hParent
        exact hpzQ (candidate_mem_Q_of_mem_completion_pz hParent)
      · obtain ⟨U, _hUne, hpzU, hUTight⟩ :=
          exists_tight22_of_not_sparse22_insert hQSparse hpzQ hAdd
        have hpU : Sum.inl p ∈ U := by
          apply hpzU
          dsimp [epzHat, epz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp
        have hzU : Sum.inl z ∈ U := by
          apply hpzU
          dsimp [epzHat, epz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp
        by_cases hqU : Sum.inl q ∈ U
        · exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
            hSparse v p q t hvp hvq hpq hTerminals U hUTight hpU hqU).elim
        · have hInsertTight :=
            extend_by_q_tight U hUTight hpU hzU hqU hqzQ
          exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
            hSparse v p q t hvp hvq hpq hTerminals (insert (Sum.inl q) U)
            hInsertTight (by simp [hpU]) (by simp)).elim
    · by_cases hAddP : Sparse22 (insert epzHat Q)
      · refine ⟨epz, Or.inl rfl, ?_, hAddP⟩
        intro hParent
        exact hpzQ (candidate_mem_Q_of_mem_completion_pz hParent)
      · by_cases hAddQ : Sparse22 (insert eqzHat Q)
        · refine ⟨eqz, Or.inr rfl, ?_, hAddQ⟩
          intro hParent
          exact hqzQ (candidate_mem_Q_of_mem_completion_qz hParent)
        · obtain ⟨Up, _hUpNe, hpzUp, hUpTight⟩ :=
            exists_tight22_of_not_sparse22_insert hQSparse hpzQ hAddP
          obtain ⟨Uq, _hUqNe, hqzUq, hUqTight⟩ :=
            exists_tight22_of_not_sparse22_insert hQSparse hqzQ hAddQ
          have hpUp : Sum.inl p ∈ Up := by
            apply hpzUp
            dsimp [epzHat, epz]
            rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
            simp
          have hzUp : Sum.inl z ∈ Up := by
            apply hpzUp
            dsimp [epzHat, epz]
            rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
            simp
          have hqUq : Sum.inl q ∈ Uq := by
            apply hqzUq
            dsimp [eqzHat, eqz]
            rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
            simp
          have hzUq : Sum.inl z ∈ Uq := by
            apply hqzUq
            dsimp [eqzHat, eqz]
            rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
            simp
          have hInterNonempty : (Up ∩ Uq).Nonempty :=
            ⟨Sum.inl z, Finset.mem_inter.mpr ⟨hzUp, hzUq⟩⟩
          have hUnionTight :=
            (tight22_union_inter hQSparse hUpTight hUqTight hInterNonempty).1
          exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
            hSparse v p q t hvp hvq hpq hTerminals (Up ∪ Uq)
            hUnionTight (Finset.mem_union_left _ hpUp)
            (Finset.mem_union_right _ hqUq)).elim

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0048

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0048/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0048.json"

section BundleSource0049
/- Source: Papers/RigidityZheng_Combinatorics_ProvenanceFlagPrivatePivot.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/ProvenanceFlagPrivatePivot.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Pivoting the distinguished missing edge of a private flag

If the old missing terminal edge is opposite a private terminal `v`, this
file exchanges it with one incident live terminal edge.  The live edge set
and restored-missing packet swap one edge each, so the literal provenance
completion is unchanged.  No semismallness or stress assertion is stored
in the resulting state.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- Exchange the opposite missing edge `pq` with the incident edge `vq`.
The hypotheses describe only facts derivable from the old literal state. -/
def State.pivotPrivateOpposite
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    State V Flag where
  edges := insert (simpleEdge p q hpq) (S.edges.erase (simpleEdge v q hvq))
  terminals := S.terminals
  missing u := if h : u = t then simpleEdge v q hvq else S.missing u
  terminals_card := S.terminals_card
  missing_supported u := by
    by_cases hut : u = t
    · subst u
      rw [dif_pos (by rfl)]
      rw [vertices_simpleEdge, hTerminals]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · rw [dif_neg hut]
      exact S.missing_supported u
  missing_not_live u := by
    by_cases hut : u = t
    · subst u
      rw [dif_pos (by rfl)]
      change simpleEdge v q hvq ∉
        insert (simpleEdge p q hpq) (S.edges.erase (simpleEdge v q hvq))
      intro hmem
      rcases Finset.mem_insert.mp hmem with hEq | hErase
      · rw [simpleEdge_eq_simpleEdge_iff] at hEq
        rcases hEq with h | h
        · exact hvp h.1
        · exact hvq h.1
      · exact (Finset.mem_erase.mp hErase).1 rfl
    · rw [dif_neg hut]
      change S.missing u ∉
        insert (simpleEdge p q hpq) (S.edges.erase (simpleEdge v q hvq))
      intro hmem
      rcases Finset.mem_insert.mp hmem with hEq | hErase
      · have hpU : p ∈ S.terminals u := by
          apply S.missing_supported u
          rw [hEq, vertices_simpleEdge]
          simp
        have hqU : q ∈ S.terminals u := by
          apply S.missing_supported u
          rw [hEq, vertices_simpleEdge]
          simp
        have hpT : p ∈ S.terminals t := by rw [hTerminals]; simp
        have hqT : q ∈ S.terminals t := by rw [hTerminals]; simp
        have hTwo : 2 ≤ (S.terminals t ∩ S.terminals u).card := by
          have hPair : ({p, q} : Finset V) ⊆
              S.terminals t ∩ S.terminals u := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hpT, hpU⟩
            · exact Finset.mem_inter.mpr ⟨hqT, hqU⟩
          have hCardPair : ({p, q} : Finset V).card = 2 := by simp [hpq]
          rw [← hCardPair]
          exact Finset.card_le_card hPair
        have hAtMost := S.card_terminal_inter_le_one hSparse (Ne.symm hut)
        omega
      · exact S.missing_not_live u (Finset.mem_erase.mp hErase).2
  other_terminal_edges_live u e heT heMissingNew := by
    by_cases hut : u = t
    · subst u
      rw [dif_pos (by rfl)] at heMissingNew
      change e ≠ simpleEdge v q hvq at heMissingNew
      by_cases heOldMissing : e = simpleEdge p q hpq
      · subst e
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_erase.mpr
        refine ⟨?_, S.other_terminal_edges_live t e heT ?_⟩
        · exact heMissingNew
        · intro hEq
          exact heOldMissing (hEq.trans hMissing)
    · rw [dif_neg hut] at heMissingNew
      change e ≠ S.missing u at heMissingNew
      apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      refine ⟨?_, S.other_terminal_edges_live u e heT heMissingNew⟩
      intro heq
      subst e
      have hvU : v ∈ S.terminals u := by
        apply heT
        rw [vertices_simpleEdge]
        simp
      exact (not_mem_other_terminals_of_flagMultiplicity_eq_one
        S v t hOne hvt u hut hvU)

@[simp]
theorem State.pivotPrivateOpposite_edges
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).edges =
      insert (simpleEdge p q hpq)
        (S.edges.erase (simpleEdge v q hvq)) := rfl

@[simp]
theorem State.pivotPrivateOpposite_terminals
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t u : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).terminals u = S.terminals u := rfl

@[simp]
theorem State.pivotPrivateOpposite_missing_self
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).missing t =
      simpleEdge v q hvq := by
  simp [State.pivotPrivateOpposite]

@[simp]
theorem State.pivotPrivateOpposite_missing_other
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t u : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq)
    (hut : u ≠ t) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).missing u = S.missing u := by
  simp [State.pivotPrivateOpposite, hut]

/-- The edge swapped into the live graph is exactly the old restored edge,
and the edge swapped out becomes exactly the new restored edge; therefore
the full completion is literally unchanged. -/
theorem State.pivotPrivateOpposite_completionEdges
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).completionEdges =
      S.completionEdges := by
  let S' := S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
    hOne hvt hTerminals hMissing
  have hMissingSelf : S'.missing t = simpleEdge v q hvq := by
    simpa only [S'] using S.pivotPrivateOpposite_missing_self hSparse
      v p q t hvp hvq hpq hOne hvt hTerminals hMissing
  have hMissingOther (u : Flag) (hut : u ≠ t) :
      S'.missing u = S.missing u := by
    simpa only [S'] using S.pivotPrivateOpposite_missing_other hSparse
      v p q t u hvp hvq hpq hOne hvt hTerminals hMissing hut
  ext e
  rw [State.completionEdges, State.completionEdges]
  simp only [Finset.mem_union]
  constructor
  · rintro ((heLive | heMissing) | heGhost)
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp heLive
      change f ∈ insert (simpleEdge p q hpq)
        (S.edges.erase (simpleEdge v q hvq)) at hf
      rcases Finset.mem_insert.mp hf with rfl | hfOld
      · left; right
        exact Finset.mem_image.mpr
          ⟨t, Finset.mem_univ t, by
            change liftLiveEdge (Flag := Flag) (S.missing t) =
              liftLiveEdge (Flag := Flag) (simpleEdge p q hpq)
            rw [hMissing]⟩
      · left; left
        exact Finset.mem_map.mpr
          ⟨f, (Finset.mem_erase.mp hfOld).2, rfl⟩
    · obtain ⟨u, _hu, heu⟩ := Finset.mem_image.mp heMissing
      by_cases hut : u = t
      · subst u
        rw [hMissingSelf] at heu
        rw [← heu]
        left; left
        exact Finset.mem_map.mpr
          ⟨simpleEdge v q hvq,
            S.other_terminal_edges_live t _ (by
              rw [vertices_simpleEdge, hTerminals]
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
              rcases hx with rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inr rfl)) (by
              intro hEq
              rw [hMissing, simpleEdge_eq_simpleEdge_iff] at hEq
              rcases hEq with h | h
              · exact hvp h.1
              · exact hvq h.1), rfl⟩
      · left; right
        rw [hMissingOther u hut] at heu
        exact Finset.mem_image.mpr
          ⟨u, Finset.mem_univ u, by
            change liftLiveEdge (Flag := Flag) (S.missing u) = e
            exact heu⟩
    · right
      exact heGhost
  · rintro ((heLive | heMissing) | heGhost)
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp heLive
      by_cases hfq : f = simpleEdge v q hvq
      · subst f
        left; right
        exact Finset.mem_image.mpr
          ⟨t, Finset.mem_univ t, by
            change liftLiveEdge (Flag := Flag) (S'.missing t) =
              liftLiveEdge (Flag := Flag) (simpleEdge v q hvq)
            rw [hMissingSelf]⟩
      · left; left
        exact Finset.mem_map.mpr
          ⟨f, by
            change f ∈ insert (simpleEdge p q hpq)
              (S.edges.erase (simpleEdge v q hvq))
            exact Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hfq, hf⟩), rfl⟩
    · obtain ⟨u, _hu, heu⟩ := Finset.mem_image.mp heMissing
      by_cases hut : u = t
      · subst u
        rw [hMissing] at heu
        left; left
        exact Finset.mem_map.mpr
          ⟨simpleEdge p q hpq, by
            change simpleEdge p q hpq ∈ insert (simpleEdge p q hpq)
              (S.edges.erase (simpleEdge v q hvq))
            exact Finset.mem_insert_self _ _, heu⟩
      · left; right
        exact Finset.mem_image.mpr
          ⟨u, Finset.mem_univ u, by
            change liftLiveEdge (Flag := Flag) (S'.missing u) = e
            rw [hMissingOther u hut]
            exact heu⟩
    · right
      exact heGhost

/-- Completion sparsity is preserved because the completed edge set is
unchanged, not merely because it embeds in the old one. -/
theorem State.pivotPrivateOpposite_completionSparse
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).CompletionSparse := by
  rw [State.CompletionSparse,
    S.pivotPrivateOpposite_completionEdges hSparse v p q t
      hvp hvq hpq hOne hvt hTerminals hMissing]
  exact hSparse

/-- The pivot does not increase the selected private terminal's live
degree; the newly inserted opposite edge avoids `v`. -/
theorem State.pivotPrivateOpposite_degree_le
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    edgeSetDegree
        (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
          hOne hvt hTerminals hMissing).edges v ≤
      edgeSetDegree S.edges v := by
  apply Finset.card_le_card
  intro e he
  have heData := mem_incidentEdges.mp he
  rw [S.pivotPrivateOpposite_edges] at heData
  rcases Finset.mem_insert.mp heData.1 with hEq | heOld
  · subst e
    rw [vertices_simpleEdge] at heData
    simp [hvp, hvq] at heData
  · exact mem_incidentEdges.mpr ⟨(Finset.mem_erase.mp heOld).2, heData.2⟩

@[simp]
theorem State.pivotPrivateOpposite_flagMultiplicity
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).flagMultiplicity v =
      S.flagMultiplicity v := rfl

/-! ## Extracting an oriented pivot from an arbitrary private flag -/

omit [Fintype V] in
/-- A simple edge supported on a named three-element terminal set is one
of its three unordered pairs. -/
theorem simpleEdge_eq_one_of_three_of_supported
    (e : SimpleEdge V) (v a b : V)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hSupported : e.vertices ⊆ ({v, a, b} : Finset V)) :
    e = simpleEdge v a hva ∨ e = simpleEdge v b hvb ∨
      e = simpleEdge a b hab := by
  obtain ⟨x, hx⟩ : e.vertices.Nonempty :=
    Finset.card_pos.mp (by simp)
  obtain ⟨y, hxy, heq⟩ := exists_otherEndpoint e hx
  have hxCases : x = v ∨ x = a ∨ x = b := by
    have hxT := hSupported hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hxT
  have hyMem : y ∈ e.vertices := by
    rw [heq, vertices_simpleEdge]
    simp
  have hyCases : y = v ∨ y = a ∨ y = b := by
    have hyT := hSupported hyMem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hyT
  rcases hxCases with rfl | rfl | rfl <;>
    rcases hyCases with rfl | rfl | rfl
  · exact (hxy rfl).elim
  · left
    simpa using heq
  · right; left
    simpa using heq
  · left
    rw [simpleEdge_comm]
    simpa using heq
  · exact (hxy rfl).elim
  · right; right
    simpa using heq
  · right; left
    rw [simpleEdge_comm]
    simpa using heq
  · right; right
    rw [simpleEdge_comm]
    simpa using heq
  · exact (hxy rfl).elim

/-- Canonical data for the private-local classifier: `p` is a live
terminal neighbour of `v`, `q` is the other terminal, and `vq` is the
distinguished missing edge.  The state may be the original state or the
literal completion-preserving opposite-edge pivot. -/
structure PrivatePivotData
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) where
  state : State V Flag
  p : V
  q : V
  hvp : v ≠ p
  hvq : v ≠ q
  hpq : p ≠ q
  original_terminals : S.terminals t = {v, p, q}
  terminals : state.terminals t = {v, p, q}
  multiplicity : state.flagMultiplicity v = 1
  mem_terminal : v ∈ state.terminals t
  completionSparse : state.CompletionSparse
  completionEdges_eq : state.completionEdges = S.completionEdges
  vp_live : simpleEdge v p hvp ∈ state.edges
  pq_live : simpleEdge p q hpq ∈ state.edges
  vq_missing : state.missing t = simpleEdge v q hvq
  degree_le : edgeSetDegree state.edges v ≤ edgeSetDegree S.edges v
  pivoted : state = S ∨
    ∃ (_hVQLive : simpleEdge v q hvq ∈ S.edges)
      (hPQMissing : S.missing t = simpleEdge p q hpq),
      state = S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
        hOne hvt original_terminals hPQMissing

@[simp]
theorem PrivatePivotData.terminals_eq
    {S : State V Flag} {hSparse : S.CompletionSparse}
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (D : PrivatePivotData S hSparse v t hOne hvt) (u : Flag) :
    D.state.terminals u = S.terminals u := by
  rcases D.pivoted with hState | ⟨_hVQLive, hPQMissing, hState⟩
  · rw [hState]
  · rw [hState]
    rfl

/-- Every private terminal admits an orientation in which the distinguished
missing edge meets `v`.  If the old
missing edge is already incident to `v`, this only renames endpoints; if it
is opposite `v`, the returned state is `pivotPrivateOpposite`. -/
theorem State.exists_privatePivotData
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    Nonempty (PrivatePivotData S hSparse v t hOne hvt) := by
  have solve (a b : V)
      (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
      (hTermAB : S.terminals t = {v, a, b}) :
      Nonempty (PrivatePivotData S hSparse v t hOne hvt) := by
    have hMissingCases := simpleEdge_eq_one_of_three_of_supported
      (S.missing t) v a b hva hvb hab (by
        rw [← hTermAB]
        exact S.missing_supported t)
    rcases hMissingCases with hvaMissing | hvbMissing | habMissing
    · refine ⟨{
        state := S, p := b, q := a,
        hvp := hvb, hvq := hva, hpq := hab.symm,
        original_terminals := by
          rw [hTermAB]
          ext u
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto,
        terminals := by
          rw [hTermAB]
          ext u
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto,
        multiplicity := hOne, mem_terminal := hvt,
        completionSparse := hSparse, completionEdges_eq := rfl,
        vp_live := S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)) (by
          rw [hvaMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hab h.2.symm
          · exact hva h.1),
        pq_live := S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl rfl)) (by
          rw [hvaMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hvb h.1.symm
          · exact hab h.1.symm),
        vq_missing := hvaMissing,
        degree_le := le_rfl,
        pivoted := Or.inl rfl }⟩
    · refine ⟨{
        state := S, p := a, q := b,
        hvp := hva, hvq := hvb, hpq := hab,
        original_terminals := hTermAB,
        terminals := hTermAB,
        multiplicity := hOne, mem_terminal := hvt,
        completionSparse := hSparse, completionEdges_eq := rfl,
        vp_live := S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)) (by
          rw [hvbMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hab h.2
          · exact hvb h.1),
        pq_live := S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)) (by
          rw [hvbMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hva h.1.symm
          · exact hab h.1),
        vq_missing := hvbMissing,
        degree_le := le_rfl,
        pivoted := Or.inl rfl }⟩
    · let S' := S.pivotPrivateOpposite hSparse v a b t
        hva hvb hab hOne hvt hTermAB habMissing
      have hvaLive : simpleEdge v a hva ∈ S.edges :=
        S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)) (by
          rw [habMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hva h.1
          · exact hvb h.1)
      have hvbLive : simpleEdge v b hvb ∈ S.edges :=
        S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)) (by
          rw [habMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hva h.1
          · exact hvb h.1)
      refine ⟨{
        state := S', p := a, q := b,
        hvp := hva, hvq := hvb, hpq := hab,
        original_terminals := hTermAB,
        terminals := by simpa [S'] using hTermAB,
        multiplicity := by simpa [S'] using hOne,
        mem_terminal := by simpa [S'] using hvt,
        completionSparse := S.pivotPrivateOpposite_completionSparse
          hSparse v a b t hva hvb hab hOne hvt hTermAB habMissing,
        completionEdges_eq := S.pivotPrivateOpposite_completionEdges
          hSparse v a b t hva hvb hab hOne hvt hTermAB habMissing,
        vp_live := by
          change simpleEdge v a hva ∈ insert (simpleEdge a b hab)
            (S.edges.erase (simpleEdge v b hvb))
          exact Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨by
              intro hEq
              rw [simpleEdge_eq_simpleEdge_iff] at hEq
              rcases hEq with h | h
              · exact hab h.2
              · exact hvb h.1,
              hvaLive⟩),
        pq_live := by
          change simpleEdge a b hab ∈ insert (simpleEdge a b hab)
            (S.edges.erase (simpleEdge v b hvb))
          exact Finset.mem_insert_self _ _,
        vq_missing :=
          S.pivotPrivateOpposite_missing_self hSparse v a b t
            hva hvb hab hOne hvt hTermAB habMissing,
        degree_le := S.pivotPrivateOpposite_degree_le hSparse v a b t
          hva hvb hab hOne hvt hTermAB habMissing,
        pivoted := Or.inr ⟨hvbLive, habMissing, rfl⟩ }⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, hTerm⟩ :=
    Finset.card_eq_three.mp (S.terminals_card t)
  have hvCases : v = x ∨ v = y ∨ v = z := by
    rw [hTerm] at hvt
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hvt
  rcases hvCases with rfl | rfl | rfl
  · exact solve y z hxy hxz hyz hTerm
  · apply solve x z hxy.symm hyz hxz
    rw [hTerm]
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · apply solve x y hxz.symm hyz.symm hxy
    rw [hTerm]
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0049

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0049/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0049.json"

section BundleSource0050
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagPrivateExceptional.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagPrivateExceptional.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/






@[expose] public section

/-!
# Closing the private exceptional induction move

This file first transports a function-field branch across the literal
completion-preserving private pivot.  The pivot changes neither the
coordinates nor the flag triples, and collinearity makes its one-for-one
live-edge exchange preserve direction-stress dimension.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The unchanged coordinate branch on the oriented private-pivot state. -/
def FunctionFieldBranch.privatePivot
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (hSparse : S.CompletionSparse)
    (D : PrivatePivotData S hSparse v t hOne hvt) :
    FunctionFieldBranch (k := k) (K := K) D.state where
  position := Y.position
  generated := Y.generated
  distinct := Y.distinct
  collinear r := by
    rw [D.terminals_eq]
    exact Y.collinear r

@[simp]
theorem FunctionFieldBranch.privatePivot_position
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (hSparse : S.CompletionSparse)
    (D : PrivatePivotData S hSparse v t hOne hvt) :
    (Y.privatePivot S hSparse D).position = Y.position := rfl

/-- The pivoted branch has exactly the original direction-stress
dimension.  In the nontrivial gauge this is the collinear triangle row
exchange theorem, applied to facts reconstructed from the literal state. -/
theorem FunctionFieldBranch.privatePivot_stressDim_eq
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (hSparse : S.CompletionSparse)
    (D : PrivatePivotData S hSparse v t hOne hvt) :
    (Y.privatePivot S hSparse D).stressDim D.state = Y.stressDim S := by
  change directionStressDim D.state.edges Y.position =
    directionStressDim S.edges Y.position
  rcases D.pivoted with hState | ⟨hvqLive, hPQMissing, hState⟩
  · rw [hState]
  · rw [hState]
    apply directionStressDim_exchange_collinear_triangle
      S.edges Y.position v D.p D.q D.hvp D.hvq D.hpq
    · apply S.other_terminal_edges_live t _
      · rw [vertices_simpleEdge, D.original_terminals]
        simp
      · rw [hPQMissing]
        simp [simpleEdge_eq_simpleEdge_iff, D.hvp, D.hvq, D.hpq]
    · exact hvqLive
    · rw [← hPQMissing]
      exact S.missing_not_live t
    · exact Y.distinct
    · apply pinCollinear_of_affinelyCollinearOn
        Y.position (S.terminals t) v D.p D.q (Y.collinear t)
      · rw [D.original_terminals]
        simp
      · rw [D.original_terminals]
        simp
      · rw [D.original_terminals]
        simp

/-- A semismall budget on an oriented pivot state transfers back to the
original state because the function field, live and flag types, and stress
dimension are unchanged. -/
theorem FunctionFieldBranch.semismallBudget_of_privatePivot
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (hSparse : S.CompletionSparse)
    (D : PrivatePivotData S hSparse v t hOne hvt)
    (hPivot : (Y.privatePivot S hSparse D).SemismallBudget D.state) :
    Y.SemismallBudget S := by
  unfold FunctionFieldBranch.SemismallBudget at hPivot ⊢
  rw [Y.privatePivot_stressDim_eq S hSparse D] at hPivot
  exact hPivot

/-! ## The inserted-child exceptional ledger -/

/-- In the classified private exceptional shape, a virtual response edge
inserted into the intrinsic private child restores exactly the parent's
one lost stress.  Its recursive budget therefore lifts to the parent: the
extension degree contributes one and consuming the flag contributes two,
exactly matching the three coordinates of the deleted vertex. -/
theorem FunctionFieldBranch.semismallBudget_of_insertedPrivateExceptional
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices) (hf : f ∉ S.edges)
    (heMissing : ∀ r : RemainingFlag t,
      restrictSimpleEdge v f hvf ≠
        (S.deletePrivate v t hOne hvt).missing r)
    (hExtension : outsideExtensionTrdeg (k := k) Y.position v = 1)
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1)
    (hRow : directionRow Y.position f ∈
      directionRowSpace (deleteVertexEdges S.edges v) Y.position)
    (hChild :
      ((Y.deletePrivateIntrinsic S v t hOne hvt).insertLiveEdge
          (S.deletePrivate v t hOne hvt)
          (restrictSimpleEdge v f hvf) heMissing).SemismallBudget
        ((S.deletePrivate v t hOne hvt).insertLiveEdge
          (restrictSimpleEdge v f hvf) heMissing)) :
    Y.SemismallBudget S := by
  let child := S.deletePrivate v t hOne hvt
  let e := restrictSimpleEdge v f hvf
  let Z := Y.deletePrivateIntrinsic S v t hOne hvt
  let inserted := child.insertLiveEdge e heMissing
  let Zi := Z.insertLiveEdge child e heMissing
  have hfDeleted : f ∉ deleteVertexEdges S.edges v := by
    intro hmem
    exact hf (mem_deleteVertexEdges.mp hmem).1
  have heAbsent : e ∉ restrictedLiveEdges S.edges v := by
    intro hmem
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge] at hmem
    exact hfDeleted hmem
  have hRowIntrinsic :
      directionRow
          (intrinsicRestrictedPlacement (k := k) Y.position v) e ∈
        directionRowSpace (restrictedLiveEdges S.edges v)
          (intrinsicRestrictedPlacement (k := k) Y.position v) := by
    dsimp only [e]
    exact directionRow_intrinsicRestricted_mem_of_deleted_mem
      (L := k) S.edges Y.position v f hvf hfDeleted hRow
  have hAugment := directionStressDim_insert_eq_add_one_of_row_mem
    (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v)
    e heAbsent hRowIntrinsic
  have hParentStress :=
    directionStressDim_eq_delete_add_outsideResponseKernelDim
      S.edges Y.position v
  rw [hResponse] at hParentStress
  have hStress : Zi.stressDim inserted = Y.stressDim S := by
    calc
      Zi.stressDim inserted =
          directionStressDim
            (insert e (restrictedLiveEdges S.edges v))
            (intrinsicRestrictedPlacement (k := k) Y.position v) := rfl
      _ = directionStressDim (restrictedLiveEdges S.edges v)
            (intrinsicRestrictedPlacement (k := k) Y.position v) + 1 :=
        hAugment
      _ = directionStressDim (deleteVertexEdges S.edges v) Y.position + 1 := by
        rw [directionStressDim_intrinsicRestrictedPlacement]
      _ = Y.stressDim S := hParentStress.symm
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  rw [hExtension] at hTower
  have hFlagCard := card_remainingFlag_add_one t
  have hFlagCardC :
      (Fintype.card (RemainingFlag t) : Cardinal) + 1 =
        (Fintype.card Flag : Cardinal) := by
    exact_mod_cast hFlagCard
  have hVertexCard := card_remainingVertex_add_one v
  unfold FunctionFieldBranch.SemismallBudget at hChild ⊢
  change
    (Y.stressDim S : Cardinal) + Algebra.trdeg k K +
          2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  calc
    (Y.stressDim S : Cardinal) + Algebra.trdeg k K +
          2 * (Fintype.card Flag : Cardinal) =
        ((Zi.stressDim inserted : Cardinal) +
            Algebra.trdeg k
              (retainedLiveCoordinateField (k := k) Y.position v) +
            2 * (Fintype.card (RemainingFlag t) : Cardinal)) + 3 := by
      rw [hStress, ← hTower, ← hFlagCardC]
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 3 :=
      add_le_add hChild (le_refl 3)
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 3 =
          3 * Fintype.card V)

/-! ## The private exceptional step -/

/-- The private exceptional induction step.  Its premises describe the
selected private low-degree branch and the induction hypothesis on smaller
live types.  After orienting the unique flag, the proof rechecks the local
inequality on the pivoted state. -/
theorem FunctionFieldBranch.semismallBudget_of_privateExceptional
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (t : Flag)
    (hSparse : S.CompletionSparse)
    (hOne : S.flagMultiplicity v = 1)
    (hvt : v ∈ S.terminals t)
    (hDegree : edgeSetDegree S.edges v ≤ 2)
    (hSmaller :
      ∀ {K' : Type v} {V' : Type w} {Flag' : Type x}
        [Field K'] [Algebra k K']
        [Fintype V'] [DecidableEq V']
        [Fintype Flag'] [DecidableEq Flag'],
        Fintype.card V' < Fintype.card V →
          ∀ (S' : State V' Flag')
            (Y' : FunctionFieldBranch (k := k) (K := K') S'),
            S'.CompletionSparse → Y'.SemismallBudget S')
    (_hExceptional : PrivateExceptional (k := k) S.edges Y.position v) :
    Y.SemismallBudget S := by
  let D : PrivatePivotData S hSparse v t hOne hvt :=
    Classical.choice (S.exists_privatePivotData hSparse v t hOne hvt)
  let P := D.state
  let Yp := Y.privatePivot S hSparse D
  have hDegreeP : edgeSetDegree P.edges v ≤ 2 :=
    D.degree_le.trans hDegree
  have hVQNot : simpleEdge v D.q D.hvq ∉ P.edges := by
    rw [← D.vq_missing]
    exact P.missing_not_live t
  have hCollinear :
      PinCollinearity.Collinear
        (Yp.position v) (Yp.position D.p) (Yp.position D.q) := by
    apply pinCollinear_of_affinelyCollinearOn
      Yp.position (P.terminals t) v D.p D.q (Yp.collinear t)
    · rw [D.terminals]
      simp
    · rw [D.terminals]
      simp
    · rw [D.terminals]
      simp
  have hChildCard :
      Fintype.card (RemainingVertex v) < Fintype.card V := by
    have hDrop := card_remainingVertex_add_one v
    omega
  rcases private_nonexceptional_or_exceptional
      (k := k) P.edges Yp.position v with hPaid | hExceptionalPivot
  · have hChildSparse :=
      P.deletePrivate_completionSparse v t D.multiplicity
        D.mem_terminal D.completionSparse
    have hChild :
        (Yp.deletePrivateIntrinsic P v t D.multiplicity D.mem_terminal).SemismallBudget
          (P.deletePrivate v t D.multiplicity D.mem_terminal) := by
      exact hSmaller hChildCard
        (P.deletePrivate v t D.multiplicity D.mem_terminal)
        (Yp.deletePrivateIntrinsic P v t D.multiplicity D.mem_terminal)
        hChildSparse
    apply Y.semismallBudget_of_privatePivot S hSparse D
    exact Yp.semismallBudget_of_deletePrivateIntrinsic P v t
      D.multiplicity D.mem_terminal hChild hPaid
  · obtain ⟨_Nclass, _hqzClass, _hcolClass, hExtension,
      hResponse, _hLocalKernel, _hLocalRank, _hDegreeTwo,
      _hConnectingZero⟩ :=
      privateExceptional_classification (k := k)
        P.edges Yp.position v D.p D.q
        D.hvp D.hvq D.hpq D.vp_live hVQNot hDegreeP
        Yp.distinct hCollinear Yp.generated hExceptionalPivot
    obtain ⟨N, hqz, hpzRow, hqzRow⟩ :=
      privateExceptional_bothVirtualRows_mem (k := k)
        P.edges Yp.position v D.p D.q
        D.hvp D.hvq D.hpq D.vp_live D.pq_live hVQNot hDegreeP
        Yp.distinct hCollinear Yp.generated hExceptionalPivot
    obtain ⟨f, hfCases, hfCompletion, hAddable⟩ :=
      P.private_response_edge_addable D.completionSparse
        v D.p D.q N.z t D.hvp D.hvq N.hvz D.hpq N.hpz hqz
        D.terminals D.pq_live N.vz_mem
    have hvf : v ∉ f.vertices := by
      rcases hfCases with rfl | rfl
      · rw [vertices_simpleEdge]
        simp [D.hvp, N.hvz]
      · rw [vertices_simpleEdge]
        simp [D.hvq, N.hvz]
    have hfLive : f ∉ P.edges := by
      intro hf
      apply hfCompletion
      apply P.liftedLiveEdges_subset_completionEdges
      rw [P.mem_liftedLiveEdges]
      exact hf
    have hRow : directionRow Yp.position f ∈
        directionRowSpace (deleteVertexEdges P.edges v) Yp.position := by
      rcases hfCases with rfl | rfl
      · exact hpzRow
      · exact hqzRow
    obtain ⟨heMissing, hInsertedSparse⟩ :=
      P.exists_insertedPrivateChild_of_addable
        v t D.multiplicity D.mem_terminal f hvf hfCompletion hAddable
    let child := P.deletePrivate v t D.multiplicity D.mem_terminal
    let e := restrictSimpleEdge v f hvf
    let Z := Yp.deletePrivateIntrinsic P v t D.multiplicity D.mem_terminal
    let inserted := child.insertLiveEdge e heMissing
    let Zi := Z.insertLiveEdge child e heMissing
    have hInsertedBudget : Zi.SemismallBudget inserted := by
      exact hSmaller hChildCard inserted Zi hInsertedSparse
    apply Y.semismallBudget_of_privatePivot S hSparse D
    exact Yp.semismallBudget_of_insertedPrivateExceptional
      P v t D.multiplicity D.mem_terminal f hvf hfLive heMissing
      hExtension hResponse hRow hInsertedBudget

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0050

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0050/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0050.json"

section BundleSource0051
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagSemismallnessFinal.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagSemismallnessFinal.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Provenance-flag semismallness

Strong induction on the number of live vertices combines the outside and
private exceptional steps with the nonexceptional recursion.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The exact smaller-state induction resource. -/
abbrev SmallerSemismallFinal
    (k : Type u) [Field k] (n : ℕ) : Prop :=
  ∀ {K : Type v} {V : Type w} {Flag : Type x}
    [Field K] [Algebra k K]
    [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag],
    Fintype.card V < n →
      ∀ (S : State V Flag)
        (Y : FunctionFieldBranch (k := k) (K := K) S),
        S.CompletionSparse → Y.SemismallBudget S

/-- **Provenance-flag semismallness.**  For every literal flagged state
whose private-ghost completion is `(2,2)`-sparse, every coordinate-generated
injective function-field branch satisfies the stress/codimension budget.

The structures `State` and `FunctionFieldBranch` contain no semismallness or
height conclusion. -/
theorem provenanceFlag_semismallness
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (Y : FunctionFieldBranch (k := k) (K := K) S) :
    Y.SemismallBudget S := by
  let P : ℕ → Prop := fun n ↦
    ∀ {K : Type v} {V : Type w} {Flag : Type x}
      [Field K] [Algebra k K]
      [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag],
      Fintype.card V = n →
        ∀ (S : State V Flag)
          (Y : FunctionFieldBranch (k := k) (K := K) S),
          S.CompletionSparse → Y.SemismallBudget S
  have hAll : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro K' V' Flag' _instField _instAlgebra
          _instFintypeV _instDecidableV _instFintypeFlag _instDecidableFlag
          hCard S' Y' hSparse'
        have hSmaller :
            SmallerSemismallFinal.{u, v, w, x}
              (k := k) (Fintype.card V') := by
          intro K'' V'' Flag'' _instField'' _instAlgebra''
            _instFintypeV'' _instDecidableV''
            _instFintypeFlag'' _instDecidableFlag''
            hCardLt S'' Y'' hSparse''
          exact ih (Fintype.card V'') (by omega) rfl S'' Y'' hSparse''
        by_cases hZero : Fintype.card V' = 0
        · exact Y'.semismallBudget_of_card_live_eq_zero S' hZero
        have hVPos : 0 < Fintype.card V' := Nat.pos_of_ne_zero hZero
        obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hVPos
        have hUniverse : (Finset.univ : Finset V').Nonempty :=
          ⟨v₀, Finset.mem_univ v₀⟩
        rcases S'.exists_outside_degree_le_three_or_private_degree_le_two
            hSparse' hUniverse with hOutside | hPrivate
        · obtain ⟨v₀, hvOutside, hDegree⟩ := hOutside
          rcases outside_nonexceptional_or_exceptional
              (k := k) S'.edges Y'.position v₀ with hPaid | hExceptional
          · have hChildCard :
                Fintype.card (RemainingVertex v₀) < n := by
              have hDrop := card_remainingVertex_add_one v₀
              omega
            have hChild :
                (Y'.deleteOutsideIntrinsic S' v₀ hvOutside).SemismallBudget
                  (S'.deleteOutside v₀ hvOutside) := by
              exact ih (Fintype.card (RemainingVertex v₀)) hChildCard rfl
                (S'.deleteOutside v₀ hvOutside)
                (Y'.deleteOutsideIntrinsic S' v₀ hvOutside)
                (S'.deleteOutside_completionSparse
                  v₀ hvOutside hSparse')
            exact Y'.semismallBudget_of_deleteOutsideIntrinsic
              S' v₀ hvOutside hChild hPaid
          · exact Y'.semismallBudget_of_outsideExceptional
              S' v₀ hSparse' hvOutside hDegree hSmaller hExceptional
        · obtain ⟨v₀, hvPrivate, hDegree⟩ := hPrivate
          have hActive : (S'.activeFlagsAt v₀).Nonempty := by
            apply Finset.card_pos.mp
            change 0 < S'.flagMultiplicity v₀
            omega
          obtain ⟨t₀, ht₀⟩ := hActive
          have hvt : v₀ ∈ S'.terminals t₀ :=
            (S'.mem_activeFlagsAt v₀ t₀).1 ht₀
          rcases private_nonexceptional_or_exceptional
              (k := k) S'.edges Y'.position v₀ with hPaid | hExceptional
          · have hChildCard :
                Fintype.card (RemainingVertex v₀) < n := by
              have hDrop := card_remainingVertex_add_one v₀
              omega
            have hChild :
                (Y'.deletePrivateIntrinsic S' v₀ t₀ hvPrivate hvt).SemismallBudget
                  (S'.deletePrivate v₀ t₀ hvPrivate hvt) := by
              exact ih (Fintype.card (RemainingVertex v₀)) hChildCard rfl
                (S'.deletePrivate v₀ t₀ hvPrivate hvt)
                (Y'.deletePrivateIntrinsic S' v₀ t₀ hvPrivate hvt)
                (S'.deletePrivate_completionSparse
                  v₀ t₀ hvPrivate hvt hSparse')
            exact Y'.semismallBudget_of_deletePrivateIntrinsic
              S' v₀ t₀ hvPrivate hvt hChild hPaid
          · exact Y'.semismallBudget_of_privateExceptional
              S' v₀ t₀ hSparse' hvPrivate hvt hDegree
              hSmaller hExceptional
  exact hAll (Fintype.card V) rfl S Y hSparse

end ProvenanceFlag

end

end RB31E2E


end
end BundleSource0051

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0051/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0051.json"

section BundleSource0052
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagGroundedPF.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagGroundedPF.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
The rooted semismallness proof and its complete supporting lemmas are retained.
The unrelated final zero-defect body-pin corollary is omitted from this extraction.
-/






@[expose] public section

/-!
# From provenance-flag semismallness to grounded PF

The provenance-flag theorem is naturally ungrounded: its empty-flag
specialization has ambient dimension `3 * |V|`.  The selected-null height
assembly needs the corresponding root-zero estimate with ambient dimension
`3 * (|V| - 1)`.

This file proves the exact bridge.  Starting with a root-zero placement over
`K`, it adjoins three independent common-translation variables.  Common
translation leaves every direction row, hence the stress space, unchanged,
while the function-field transcendence degree increases by exactly three.
Applying empty-flag semismallness upstairs and cancelling those three
dimensions gives the grounded estimate.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlagGroundedPF

open ProvenanceFlag

/-! ## Three independent common translations -/

abbrev TranslationRing (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

abbrev TranslationField (K : Type*) [Field K] :=
  FractionRing (TranslationRing K)

def translationCoordinate {K : Type*} [Field K] (j : Fin 3) :
    TranslationField K :=
  algebraMap (TranslationRing K) (TranslationField K) (MvPolynomial.X j)

def translatedPlacement
    {K V : Type*} [Field K]
    (a : V → Fin 3 → K) : V → Fin 3 → TranslationField K :=
  fun v j ↦ algebraMap K (TranslationField K) (a v j) +
    translationCoordinate j

theorem translatedPlacement_root
    {K V : Type*} [Field K] {a : V → Fin 3 → K} {root : V}
    (hroot : a root = 0) (j : Fin 3) :
    translatedPlacement a root j = translationCoordinate j := by
  simp [translatedPlacement, hroot]

theorem translatedPlacement_injective
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (a : V → Fin 3 → K) (ha : Function.Injective a) :
    Function.Injective (translatedPlacement a) := by
  intro u v huv
  apply ha
  funext j
  have hj := congrFun huv j
  simp only [translatedPlacement] at hj
  have : algebraMap K (TranslationField K) (a u j) =
      algebraMap K (TranslationField K) (a v j) := by
    exact add_right_cancel hj
  exact (RingHom.injective (algebraMap K (TranslationField K))) this

theorem directionRow_translatedPlacement
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (a : V → Fin 3 → K) (e : SimpleEdge V) :
    DirectionStress.directionRow (translatedPlacement a) e =
      DirectionStress.directionRow
        (DirectionStress.mapPlacement (K := TranslationField K) a) e := by
  funext v j
  simp only [DirectionStress.directionRow, DirectionStress.edgeDirection,
    translatedPlacement, DirectionStress.mapPlacement]
  split_ifs <;> ring

theorem directionStressDim_translatedPlacement
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) :
    DirectionStress.directionStressDim F (translatedPlacement a) =
      DirectionStress.directionStressDim F a := by
  have hmap :
      DirectionStress.directionEquilibrium F (translatedPlacement a) =
        DirectionStress.directionEquilibrium F
          (DirectionStress.mapPlacement (K := TranslationField K) a) := by
    apply LinearMap.ext
    intro weight
    funext v j
    simp only [DirectionStress.directionEquilibrium_apply,
      DirectionStress.directionEquilibriumCoordinate]
    apply Finset.sum_congr rfl
    intro e _he
    rw [directionRow_translatedPlacement a e.1]
  calc
    DirectionStress.directionStressDim F (translatedPlacement a) =
        DirectionStress.directionStressDim F
          (DirectionStress.mapPlacement (K := TranslationField K) a) := by
      unfold DirectionStress.directionStressDim
      change Module.finrank (TranslationField K)
          (LinearMap.ker
            (DirectionStress.directionEquilibrium F (translatedPlacement a))) =
        Module.finrank (TranslationField K)
          (LinearMap.ker
            (DirectionStress.directionEquilibrium F
              (DirectionStress.mapPlacement
                (K := TranslationField K) a)))
      rw [hmap]
    _ = DirectionStress.directionStressDim F a :=
      DirectionStress.directionStressDim_mapPlacement F a

/-! ## The translation field has relative transcendence degree three -/

theorem adjoin_translationCoordinate_eq_top
    {K : Type*} [Field K] :
    IntermediateField.adjoin K (Set.range (translationCoordinate (K := K))) =
      ⊤ := by
  let A : IntermediateField K (TranslationField K) :=
    IntermediateField.adjoin K
      (Set.range (translationCoordinate (K := K)))
  have hX (j : Fin 3) : translationCoordinate (K := K) j ∈ A :=
    IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  have hpoly : ∀ p : TranslationRing K,
      algebraMap (TranslationRing K) (TranslationField K) p ∈ A := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        simpa [A, IsScalarTower.algebraMap_apply K
          (TranslationRing K) (TranslationField K)] using
          A.algebraMap_mem c
    | add p q hp hq =>
        simpa using A.add_mem hp hq
    | mul_X p j hp =>
        simpa [map_mul, translationCoordinate] using A.mul_mem hp (hX j)
  apply top_unique
  intro z _hz
  obtain ⟨p, q, _hq, rfl⟩ :=
    IsFractionRing.div_surjective (TranslationRing K) z
  exact A.div_mem (hpoly p) (hpoly q)

theorem translationCoordinate_isTranscendenceBasis
    {K : Type*} [Field K] :
    IsTranscendenceBasis K (translationCoordinate (K := K)) := by
  let R := TranslationRing K
  let L := TranslationField K
  have hInjective : Function.Injective
      (algebraMap R L) := IsFractionRing.injective R L
  have hIndependent : AlgebraicIndependent K
      (translationCoordinate (K := K)) := by
    have hX := MvPolynomial.algebraicIndependent_X (Fin 3) K
    have hmap := hX.map
      (f := IsScalarTower.toAlgHom K R L)
      hInjective.injOn
    change AlgebraicIndependent K
      (fun j : Fin 3 => algebraMap R L (MvPolynomial.X j))
    exact hmap
  have hField : Algebra.IsAlgebraic
      (IntermediateField.adjoin K
        (Set.range (translationCoordinate (K := K)))) L :=
    ⟨fun z ↦ by
      have hz : z ∈ IntermediateField.adjoin K
          (Set.range (translationCoordinate (K := K))) := by
        rw [adjoin_translationCoordinate_eq_top]
        exact trivial
      have hmap : algebraMap
          (IntermediateField.adjoin K
            (Set.range (translationCoordinate (K := K)))) L
          (⟨z, hz⟩ : IntermediateField.adjoin K
            (Set.range (translationCoordinate (K := K)))) = z := rfl
      rw [← hmap]
      exact isAlgebraic_algebraMap _⟩
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
    ⟨hIndependent, ?_⟩
  exact (IntermediateField.isAlgebraic_adjoin_iff_top).mp hField

theorem trdeg_translationField
    {K : Type*} [Field K] :
    Algebra.trdeg K (TranslationField K) = 3 := by
  simpa using
    (translationCoordinate_isTranscendenceBasis
      (K := K)).lift_cardinalMk_eq_trdeg.symm

theorem trdeg_translationField_over_base
    {k K : Type*} [Field k] [Field K] [Algebra k K] :
    Algebra.trdeg k (TranslationField K) = Algebra.trdeg k K + 3 := by
  calc
    Algebra.trdeg k (TranslationField K) =
        Algebra.trdeg k K + Algebra.trdeg K (TranslationField K) :=
      (trdeg_add_eq k K).symm
    _ = Algebra.trdeg k K + 3 := by rw [trdeg_translationField]

/-! ## The translated placement still generates the whole field -/

theorem translatedPlacement_generated
    {k K V : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype V] [DecidableEq V]
    (a : V → Fin 3 → K) (root : V)
    (hroot : a root = 0)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤) :
    IntermediateField.adjoin k
      (Set.range (fun x : V × Fin 3 ↦
        translatedPlacement a x.1 x.2)) = ⊤ := by
  let A : IntermediateField k (TranslationField K) :=
    IntermediateField.adjoin k
      (Set.range (fun x : V × Fin 3 ↦
        translatedPlacement a x.1 x.2))
  have htranslated (v : V) (j : Fin 3) :
      translatedPlacement a v j ∈ A :=
    IntermediateField.subset_adjoin k _ ⟨⟨v, j⟩, rfl⟩
  have htranslation (j : Fin 3) :
      translationCoordinate (K := K) j ∈ A := by
    rw [← translatedPlacement_root hroot j]
    exact htranslated root j
  have hcoordinate (v : V) (j : Fin 3) :
      algebraMap K (TranslationField K) (a v j) ∈ A := by
    have hsub := A.sub_mem (htranslated v j) (htranslation j)
    simpa [translatedPlacement] using hsub
  have hbase (x : K) : algebraMap K (TranslationField K) x ∈ A := by
    have hx : x ∈ IntermediateField.adjoin k
        (Set.range (fun y : V × Fin 3 ↦ a y.1 y.2)) := by
      rw [hgen]
      exact trivial
    exact IntermediateField.adjoin_induction k
      (motive := fun y _hy ↦ algebraMap K (TranslationField K) y ∈ A)
      (fun y hy ↦ by
        obtain ⟨⟨v, j⟩, rfl⟩ := hy
        exact hcoordinate v j)
      (fun c ↦ by
        simpa [IsScalarTower.algebraMap_apply k K (TranslationField K)] using
          A.algebraMap_mem c)
      (fun _ _ _ _ hy hz ↦ by simpa using A.add_mem hy hz)
      (fun _ _ hy ↦ by simpa using A.inv_mem hy)
      (fun _ _ _ _ hy hz ↦ by simpa using A.mul_mem hy hz)
      hx
  have hpoly : ∀ p : TranslationRing K,
      algebraMap (TranslationRing K) (TranslationField K) p ∈ A := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        simpa [IsScalarTower.algebraMap_apply K
          (TranslationRing K) (TranslationField K)] using hbase c
    | add p q hp hq =>
        simpa using A.add_mem hp hq
    | mul_X p j hp =>
        simpa [map_mul, translationCoordinate] using
          A.mul_mem hp (htranslation j)
  apply top_unique
  intro z _hz
  obtain ⟨p, q, _hq, rfl⟩ :=
    IsFractionRing.div_surjective (TranslationRing K) z
  exact A.div_mem (hpoly p) (hpoly q)

/-! ## Empty flags and completion sparsity -/

def emptyFlagState {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) : ProvenanceFlag.State V (Fin 0) where
  edges := F
  terminals := Fin.elim0
  missing := Fin.elim0
  terminals_card := fun t ↦ Fin.elim0 t
  missing_supported := fun t ↦ Fin.elim0 t
  missing_not_live := fun t ↦ Fin.elim0 t
  other_terminal_edges_live := fun t ↦ Fin.elim0 t

theorem emptyFlagState_completionEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) :
    (emptyFlagState F).completionEdges =
      (emptyFlagState F).liftedLiveEdges := by
  simp [ProvenanceFlag.State.completionEdges,
    ProvenanceFlag.State.restoredMissingEdges,
    ProvenanceFlag.State.ghostStarEdges]

theorem map_drop_liftLiveEdge
    {V : Type*} [DecidableEq V] (e : SimpleEdge V) :
    Sparse22Transport.mapSimpleEdge
        (Equiv.sumEmpty V (Fin 0)).toEmbedding
        (ProvenanceFlag.liftLiveEdge (Flag := Fin 0) e) = e := by
  apply Subtype.ext
  simp [Sparse22Transport.mapSimpleEdge,
    ProvenanceFlag.liftLiveEdge, Sym2.map_map, Function.comp_def]

theorem emptyFlagState_completionSparse
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) (hF : Sparse22 F) :
    (emptyFlagState F).CompletionSparse := by
  rw [ProvenanceFlag.State.CompletionSparse,
    emptyFlagState_completionEdges]
  apply Sparse22Transport.sparse22_of_mapEdgeSet_subset
    (Equiv.sumEmpty V (Fin 0)).toEmbedding hF
  intro e he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hg
  change Sparse22Transport.mapSimpleEdge
      (Equiv.sumEmpty V (Fin 0)).toEmbedding
      (ProvenanceFlag.liftLiveEdge (Flag := Fin 0) f) ∈ F
  rw [map_drop_liftLiveEdge]
  exact hf

/-! ## Passage to the grounded inequality -/

/-- Empty-flag semismallness implies the rooted direction-stress inequality.
Grounding and all cardinal conversions are proved in this declaration. -/
theorem groundedPF_of_provenanceFlag_semismallness
    (hFlagPF :
      ∀ {k K V Flag : Type}
        [Field k] [Field K] [Algebra k K]
        [Fintype V] [DecidableEq V]
        [Fintype Flag] [DecidableEq Flag]
        (S : ProvenanceFlag.State V Flag),
        S.CompletionSparse →
        ∀ Y : ProvenanceFlag.FunctionFieldBranch (k := k) (K := K) S,
          Y.SemismallBudget S) :
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (F : SimpleEdgeSet V), Sparse22 F →
      ∀ (root : V) {K : Type} [Field K] [Algebra ℚ K]
        (a : V → Fin 3 → K),
        a root = 0 →
        Function.Injective a →
        IntermediateField.adjoin ℚ
            (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
        DirectionStress.directionStressDim F a +
            (Algebra.trdeg ℚ K).toNat ≤
          Nat.card (GroundedTwistSplit.SpatialVariable root) := by
  intro V _instFV _instDV F hSparse root K _instFieldK _instAlgQK
    a hroot hinjective hgenerated
  let S := emptyFlagState F
  let Y : ProvenanceFlag.FunctionFieldBranch
      (k := ℚ) (K := TranslationField K) S := {
    position := translatedPlacement a
    generated := translatedPlacement_generated a root hroot hgenerated
    distinct := translatedPlacement_injective a hinjective
    collinear := fun t ↦ Fin.elim0 t
  }
  have hBudget := hFlagPF S (emptyFlagState_completionSparse F hSparse) Y
  have hEmptyBudget :
      (Y.stressDim S : Cardinal) +
          Algebra.trdeg ℚ (TranslationField K) ≤
        3 * (Fintype.card V : Cardinal) :=
    (Y.semismallBudget_of_flag_card_zero_iff S (by simp)).mp hBudget
  change
      (DirectionStress.directionStressDim F (translatedPlacement a) : Cardinal) +
          Algebra.trdeg ℚ (TranslationField K) ≤
        3 * (Fintype.card V : Cardinal) at hEmptyBudget
  rw [directionStressDim_translatedPlacement,
    trdeg_translationField_over_base] at hEmptyBudget
  have hTrdegFinite : Algebra.trdeg ℚ K < Cardinal.aleph0 :=
    (FiniteCoordinateTrdeg.trdeg_le_three_mul_card
      (fun x : V × Fin 3 ↦ a x.1 x.2) hgenerated).trans_lt
        (Cardinal.mul_lt_aleph0
          Cardinal.natCast_lt_aleph0 Cardinal.natCast_lt_aleph0)
  have hRightFinite :
      3 * (Fintype.card V : Cardinal) < Cardinal.aleph0 :=
    Cardinal.mul_lt_aleph0
      Cardinal.natCast_lt_aleph0 Cardinal.natCast_lt_aleph0
  have hNat := Cardinal.toNat_le_toNat hEmptyBudget hRightFinite
  have hStressFinite :
      (DirectionStress.directionStressDim F a : Cardinal) <
        Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  have hThreeFinite : (3 : Cardinal) < Cardinal.aleph0 := by simp
  rw [Cardinal.toNat_add hStressFinite
      (Cardinal.add_lt_aleph0 hTrdegFinite hThreeFinite),
    Cardinal.toNat_add hTrdegFinite hThreeFinite] at hNat
  simp at hNat
  have hOffRoot :
      Fintype.card (OffRoot root) = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun v : V ↦ v = root)]
    simp
  rw [Nat.card_eq_fintype_card]
  simp only [GroundedTwistSplit.SpatialVariable,
    Fintype.card_prod, Fintype.card_fin, hOffRoot]
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  omega

end ProvenanceFlagGroundedPF

end

end RB31E2E


end
end BundleSource0052

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0052/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0052.json"

section BundleSource0053
/- Source: Papers/RigidityNullHeight.lean -/





@[expose] public section

/-!
# Sparse null-difference height, with all semismallness inputs discharged

The source is Dongzhe Zheng's Apache-2.0 formalization at commit
`e457fde9100c9b7226bd4d81af6860f210a531ab`. The imported files retain their
provenance. This wrapper removes the auxiliary semismallness premise from
the exact minimal-prime height theorem, using its proved source theorem.

The ideal is the actual polynomial ideal generated by
`(ω_i - ω_j) · (t_i - t_j)`. The nonvanishing denominator chooses, for every
pair of distinct body labels, an actual nonzero difference coordinate.
Consequently the theorem concerns the full distinct-twist locus, not a
condition that encodes the desired codimension conclusion.
-/

namespace Papers.Rigidity.NullHeight

open RB31E2E
open RB31E2E.GroundedTwistPolynomial
open RB31E2E.PinOuterActiveHeight
open RB31E2E.PinOuterFullProvenanceHeightTransfer
open RB31E2E.SelectedNullHeight
open RB31E2E.UniversalHomogeneousChart

/-- Each irreducible component of the sparse null-difference equations
meeting the specified distinct-point chart has codimension exactly the
number of selected simple edges. There is no semismallness or height
hypothesis in this statement. -/
theorem coefficientMinimalPrime_height_eq_edgeCard
    {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V) (hSparse : Sparse22 F)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hP : P ∈ (coefficientSelectedNullIdeal root src dst active
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented)).minimalPrimes)
    (hden : coefficientDistinctnessDenominator root chart ∉ P) :
    P.height = (F.card : ℕ∞) := by
  apply WittShearDistinctPrime.coefficientMinimalPrime_height_eq_edgeCard_of_groundedPF
    root src dst active hLoop F hRepresented chart P hP hden
  exact ProvenanceFlagGroundedPF.groundedPF_of_provenanceFlag_semismallness
    ProvenanceFlag.provenanceFlag_semismallness V F hSparse root

theorem coefficientMinimalPrime_height_ge_edgeCard
    {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V) (hSparse : Sparse22 F)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hP : P ∈ (coefficientSelectedNullIdeal root src dst active
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented)).minimalPrimes)
    (hden : coefficientDistinctnessDenominator root chart ∉ P) :
    (F.card : ℕ∞) ≤ P.height :=
  (coefficientMinimalPrime_height_eq_edgeCard
    root src dst active hLoop F hSparse hRepresented chart P hP hden).symm.le

end Papers.Rigidity.NullHeight

end
end BundleSource0053

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0053/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0053.json"

section BundleSource0054
/- Source: Papers/RigidityZheng_NullCellule_SelectedNullHeightPrimewise.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/SelectedNullHeightPrimewise.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Primewise selected-null height

Localization and spectator-variable transport convert a direct height theorem
for surviving coefficient minimal primes into the required selected-null
height bound.  The resulting theorem assumes only grounded collinearity-flag
semismallness.
-/

namespace RB31E2E

namespace SelectedNullHeightPrimewise

noncomputable section

set_option synthInstance.maxHeartbeats 100000

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open PinOuterFullProvenanceHeightTransfer
open PolynomialPrimeTrdegHeight
open UniversalHomogeneousChart
open SelectedNullHeight

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v

/-- A lower-height theorem for all surviving coefficient minimal primes
implies the terminal function-field inequality by the finite polynomial-prime
dimension formula. -/
theorem survivingSelectedFunctionFieldBudget_of_primewiseHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hHeight : ∀ (P : Ideal (TwistCoefficientRing root)),
      P ∈ (coefficientSelectedNullIdeal
        root src dst active selected).minimalPrimes →
      activeAngularDenominator root src dst active angularChart ∉ P →
      coefficientDistinctnessDenominator root distinctChart ∉ P →
      (selected.card : ℕ∞) ≤ P.height) :
    SurvivingSelectedFunctionFieldBudget
      root src dst active angularChart selected distinctChart := by
  intro P hP hAngular hDistinct
  letI : P.IsPrime := hP.1.1
  let t := (Algebra.trdeg ℚ
    (FractionRing (TwistCoefficientRing root ⧸ P))).toNat
  have hformula := polynomialPrime_height_add_fractionTrdeg_eq_natCard P
  have hadd : (selected.card : ℕ∞) + (t : ℕ∞) ≤
      (Nat.card (GroundedTwistVariable root) : ℕ∞) := by
    calc
      (selected.card : ℕ∞) + (t : ℕ∞) ≤
          P.height + (t : ℕ∞) :=
        by simpa [add_comm] using
          (add_le_add_right (hHeight P hP hAngular hDistinct) (t : ℕ∞))
      _ = (Nat.card (GroundedTwistVariable root) : ℕ∞) := hformula
  have hn : t + selected.card ≤ Nat.card (GroundedTwistVariable root) := by
    apply ENat.coe_le_coe.mp
    simpa only [Nat.cast_add, add_comm] using hadd
  simpa [t, add_comm] using hn

/-- Public localization/spectator bridge whose input is direct primewise
height, not a full-twist function-field budget. -/
theorem incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_primewiseHeight
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hHeight : ∀ (P : Ideal (TwistCoefficientRing root)),
      P ∈ (coefficientSelectedNullIdeal
        root src dst active selected).minimalPrimes →
      activeAngularDenominator root src dst active angularChart ∉ P →
      coefficientDistinctnessDenominator root distinctChart ∉ P →
      (selected.card : ℕ∞) ≤ P.height) :
    (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart := by
  exact incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_budget
    root src dst active hLoop angularChart selected distinctChart
      (survivingSelectedFunctionFieldBudget_of_primewiseHeight
        root src dst active angularChart selected distinctChart hHeight)

/-- The selected-null localized lower-height bound required by the incidence
transfer follows directly from grounded PF semismallness.  No
`SurvivingSelectedFunctionFieldBudget`, selected-null height, or generic
fibre identity is a premise. -/
theorem incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_groundedPF
    {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (angularChart : active → Fin 3)
    (distinctChart : DistinctnessChart V)
    (hPF : ∀ {K : Type u} [Field K] [Algebra ℚ K]
      (a : V → Fin 3 → K),
      a root = 0 →
      Function.Injective a →
      IntermediateField.adjoin ℚ
          (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
      DirectionStress.directionStressDim F a +
          (Algebra.trdeg ℚ K).toNat ≤
        Nat.card (GroundedTwistSplit.SpatialVariable root)) :
    let selected := SparseNullIncidence.selectedSkeletonOccurrences
      src dst active hLoop F hRepresented
    (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart := by
  classical
  dsimp only
  let selected := SparseNullIncidence.selectedSkeletonOccurrences
    src dst active hLoop F hRepresented
  apply incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_primewiseHeight
    root src dst active hLoop angularChart selected distinctChart
  intro P hP _hAngular hDistinct
  letI : P.IsPrime := hP.1.1
  have hF :=
    WittShearDistinctPrime.coefficientMinimalPrime_height_eq_edgeCard_of_groundedPF
      root src dst active hLoop F hRepresented distinctChart P hP hDistinct hPF
  rw [SparseNullIncidence.card_selectedSkeletonOccurrences
    src dst active hLoop F hRepresented]
  exact hF.symm.le

end

end SelectedNullHeightPrimewise

end RB31E2E


end
end BundleSource0054

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0054/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0054.json"

section BundleSource0055
/- Source: Papers/RigidityQuantitativeHeight.lean -/





@[expose] public section

/-!
# The quantitative generic incidence height bound

The primewise coordinate-localization argument is adapted from Dongzhe Zheng's
Apache-2.0 `PinOuterFullProvenanceHeightTransfer.lean` at commit
`e457fde9100c9b7226bd4d81af6860f210a531ab`. Its conclusion here retains the
actual number of active pin occurrences and selected sparse null equations,
without specializing to the zero-defect case.

The terminal sparse theorem has no semismallness, codimension, height, or
rigidity hypothesis. Its prime is an ordinary prime over the actual universal
compatibility and selected-null equations, avoiding the literal product of
pairwise-difference and active-angular coordinates. Homogeneity is not needed.
-/

namespace Papers.Rigidity.QuantitativeHeight

noncomputable section

open MvPolynomial
open RB31E2E
open RB31E2E.GroundedTwistPolynomial
open RB31E2E.UniversalHomogeneousChart
open RB31E2E.PinTriangularElimination
open RB31E2E.TotalRingProvenanceSwap
open RB31E2E.PinOuterActiveHeight
open RB31E2E.ActivePinPrimeHeight
open RB31E2E.UniversalActivePinHeightTransfer
open RB31E2E.PinOuterFullProvenanceHeightTransfer

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Every prime over the incidence equations pays two height units for each
active occurrence, in addition to the selected-null coefficient height. -/
theorem genericIncidencePrime_height_ge_active_add_selected
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hselected : (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart) :
    ∀ (Q : Ideal (FiniteGenericRelativeRing root E)), Q.IsPrime →
      finiteGenericUniversalChartIdeal root src dst active angularChart selected ≤ Q →
      finiteGenericIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart ∉ Q →
      ((2 * active.card + selected.card : ℕ) : ℕ∞) ≤ Q.height := by
  intro Q hQprime hchart hdenominator
  letI : Q.IsPrime := hQprime
  let P₀ : Ideal (RelativeRing root E) :=
    Ideal.comap (finiteGenericChartHom root) Q
  letI : P₀.IsPrime := by
    dsimp [P₀]
    exact Ideal.comap_isPrime _ _
  let swap : RelativeRing root E ≃+* PinOuterRing root E :=
    (totalRingSwap (E := E) root).toRingEquiv
  let P₁ : Ideal (PinOuterRing root E) := Ideal.map swap P₀
  letI : P₁.IsPrime := by
    dsimp [P₁]
    exact Ideal.map_isPrime_of_equiv swap
  have hfullP₀ : universalIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart ∉ P₀ := by
    simpa [P₀, finiteGenericIncidenceProvenanceDenominator] using
      hdenominator
  have hfullP₁ : C (coefficientIncidenceProvenanceDenominator
      root src dst active distinctChart angularChart) ∉ P₁ := by
    intro hx
    have hback := (Ideal.symm_apply_mem_of_equiv_iff
      (I := P₀) (f := swap)
      (y := C (coefficientIncidenceProvenanceDenominator
        root src dst active distinctChart angularChart))).2 hx
    have hswap :=
      totalRingSwapHom_universalIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart
    have hinverse : swap.symm
        (C (coefficientIncidenceProvenanceDenominator
          root src dst active distinctChart angularChart)) =
        universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart := by
      rw [← hswap]
      change swap.symm (swap
        (universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart)) = _
      exact swap.symm_apply_apply _
    apply hfullP₀
    simpa [hinverse] using hback
  have hAngular : C (activeAngularDenominator
      root src dst active angularChart) ∉ P₁ :=
    angularDenominator_not_mem_of_incidenceDenominator_not_mem
      root src dst active distinctChart angularChart P₁ hfullP₁
  have hDistinctSource : C (coefficientDistinctnessDenominator
      root distinctChart) ∉ P₁ :=
    distinctnessDenominator_not_mem_of_incidenceDenominator_not_mem
      root src dst active distinctChart angularChart P₁ hfullP₁
  let P₂ : Ideal (PrivatePresentationRing
      root src dst active angularChart) :=
    Ideal.map
      (localizedSplitPinOuterHom
        root src dst active angularChart) P₁
  letI : P₂.IsPrime := by
    dsimp [P₂]
    exact localizedSplitPinOuterHom_isPrime
      root src dst active angularChart P₁ hAngular
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active angularChart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active angularChart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let R := RetainedCoefficientRing
    root src dst active angularChart
  let Cₚ : R →+* PrivatePresentationRing
      root src dst active angularChart := C
  let Pcoeff : Ideal R := Ideal.comap Cₚ P₂
  letI : Pcoeff.IsPrime := by
    dsimp [Pcoeff]
    exact Ideal.comap_isPrime _ _
  have hsource : universalChartIdeal
      root src dst active angularChart selected ≤ P₀ := by
    intro f hf
    change finiteGenericChartHom root f ∈ Q
    exact hchart (Ideal.mem_map_of_mem _ hf)
  have hactiveSource : activeCompatibilityIdeal
      root src dst active angularChart ≤ P₀ :=
    (activeCompatibilityIdeal_le_universalChartIdeal
      root src dst active angularChart selected).trans hsource
  have hselectedSource : Ideal.span
      (selectedNullGeneratorSet root src dst active selected) ≤ P₀ :=
    (selectedNullIdeal_le_universalChartIdeal
      root src dst active angularChart selected).trans hsource
  have himage : Ideal.map
      (localizedPrivatePresentationHom
        root src dst active angularChart) P₀ = P₂ := by
    dsimp [P₂, P₁]
    rw [localizedPrivatePresentationHom, ← Ideal.map_map]
    rfl
  have hmappedActive : Ideal.map
      (localizedPrivatePresentationHom
        root src dst active angularChart)
      (activeCompatibilityIdeal
        root src dst active angularChart) ≤ P₂ := by
    rw [← himage]
    exact Ideal.map_mono hactiveSource
  have hcompat : localizedActiveCompatibilityIdeal
      root src dst active angularChart ≤ P₂ :=
    (localizedActiveCompatibilityIdeal_le_map_activeCompatibilityIdeal
      root src dst active angularChart).trans hmappedActive
  let Iselected : Ideal R := Ideal.span
    (Set.range (fun e : SelectedOccurrence active selected ↦
      retainedNullEquation
        root src dst active angularChart e.1.1))
  have hretainedSelected : Iselected ≤ Pcoeff := by
    dsimp [Iselected]
    rw [Ideal.span_le]
    rintro _ ⟨e, rfl⟩
    change C (retainedNullEquation
      root src dst active angularChart e.1.1) ∈ P₂
    rw [← localizedPrivatePresentationHom_universalNullEquation
      root src dst active angularChart e.1.1, ← himage]
    exact Ideal.mem_map_of_mem _
      (hselectedSource (Ideal.subset_span ⟨e, rfl⟩))
  have hrelative : Pcoeff.height + (2 * active.card : ℕ) ≤
      P₂.height := by
    simpa [Pcoeff, Cₚ, R] using
      (privatePresentation_prime_height_ge_coefficientContraction_add_twice_card
        root src dst active angularChart hLoop P₂ hcompat)
  have hP₀height : P₀.height = Q.height := by
    exact finiteGenericChartHom_height_comap root Q
  have hP₁height : P₁.height = P₀.height := by
    exact RingEquiv.height_map swap P₀
  have hP₂height : P₂.height = P₁.height := by
    exact localizedSplitPinOuterHom_height_map
      root src dst active angularChart hLoop P₁ hAngular
  have hP₂heightQ : P₂.height = Q.height :=
    hP₂height.trans (hP₁height.trans hP₀height)
  have hDistinctAfterAngular :=
    localizedSplitPinOuterHom_not_mem_map_of_not_mem
      root src dst active angularChart P₁ hAngular
        (C (coefficientDistinctnessDenominator root distinctChart))
        hDistinctSource
  have hretainedDistinct : retainedDistinctnessDenominator
      root src dst active angularChart distinctChart ∉ Pcoeff := by
    intro hx
    apply hDistinctAfterAngular
    change C (retainedDistinctnessDenominator
      root src dst active angularChart distinctChart) ∈ P₂ at hx
    simpa [P₂, retainedDistinctnessDenominator] using hx
  let d : R := retainedDistinctnessDenominator
    root src dst active angularChart distinctChart
  let T := Localization.Away d
  let Pfull : Ideal T := Ideal.map
    (algebraMap R T) Pcoeff
  have hdisjDistinct : Disjoint
      (Submonoid.powers d : Set R)
      (Pcoeff : Set R) :=
    (Ideal.disjoint_powers_iff_notMem
      d
      (Ideal.IsPrime.isRadical inferInstance)).2 hretainedDistinct
  have hPfullHeight : Pfull.height = Pcoeff.height := by
    dsimp [Pfull, T]
    exact IsLocalization.height_map_of_disjoint
      (Submonoid.powers d)
      Pcoeff hdisjDistinct
  let Ifull : Ideal T := Ideal.map (algebraMap R T) Iselected
  have hselectedFull : Ifull ≤ Pfull := by
    dsimp [Ifull, Pfull]
    exact Ideal.map_mono hretainedSelected
  have hselectedHeight : (selected.card : ℕ∞) ≤ Ifull.height := by
    simpa [incidenceLocalizedSelectedNullIdealHeight, R, d, T,
      Iselected, Ifull] using hselected
  have hselectedCoeff : (selected.card : ℕ∞) ≤ Pcoeff.height := by
    calc
      (selected.card : ℕ∞) ≤ Ifull.height := hselectedHeight
      _ ≤ Pfull.height := Ideal.height_mono hselectedFull
      _ = Pcoeff.height := hPfullHeight
  calc
    ((2 * active.card + selected.card : ℕ) : ℕ∞) =
        (selected.card : ℕ∞) + (2 * active.card : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_comm]
    _ ≤ Pcoeff.height + (2 * active.card : ℕ) := by
      exact add_le_add hselectedCoeff le_rfl
    _ ≤ P₂.height := hrelative
    _ = Q.height := hP₂heightQ

/-- The exact quantitative sparse-null incidence bound, with the sparse
codimension input fully discharged by the proven semismallness theorem. -/
theorem genericIncidencePrime_height_ge_active_add_sparse
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V) (hSparse : Sparse22 F)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (angularChart : active → Fin 3) (distinctChart : DistinctnessChart V)
    (Q : Ideal (FiniteGenericRelativeRing root E)) [Q.IsPrime]
    (hchart : finiteGenericUniversalChartIdeal root src dst active angularChart
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented) ≤ Q)
    (hdenominator : finiteGenericIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart ∉ Q) :
    ((2 * active.card + F.card : ℕ) : ℕ∞) ≤ Q.height := by
  have hselected :=
    SelectedNullHeightPrimewise.incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_groundedPF
      root src dst active hLoop F hRepresented angularChart distinctChart
      (ProvenanceFlagGroundedPF.groundedPF_of_provenanceFlag_semismallness
        ProvenanceFlag.provenanceFlag_semismallness V F hSparse root)
  have h := genericIncidencePrime_height_ge_active_add_selected
    root src dst active hLoop angularChart
    (SparseNullIncidence.selectedSkeletonOccurrences
      src dst active hLoop F hRepresented) distinctChart hselected
    Q inferInstance hchart hdenominator
  rw [SparseNullIncidence.card_selectedSkeletonOccurrences
    src dst active hLoop F hRepresented] at h
  exact h

end

end Papers.Rigidity.QuantitativeHeight

end
end BundleSource0055

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0055/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0055.json"

section BundleSource0056
/- Source: Papers/RigidityPairPinSparseRank.lean -/




@[expose] public section

/-!
# Quantitative rank paid by active pins and a sparse null skeleton

This theorem combines the ordinary generic motion ideal, its literal row
rank, the charts supplied by actual separating motions, and the proven
sparse null-height dependency. Its conclusion is about the original
occurrence-level pin matrix.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open RB31E2E
open RB31E2E.UniversalHomogeneousChart

/-- Distinct motion classes pay two independent rank units per active pin
and one more per selected simple `(2,2)`-sparse support edge. -/
theorem genericMotionMatrix_rank_ge_active_add_sparse
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (hsep : BodiesSeparated src dst)
    (F : SimpleEdgeSet V) (hSparse : Sparse22 F)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f) :
    2 * active.card + F.card ≤ (genericMotionMatrix root src dst).rank := by
  obtain ⟨dc, ac, hden⟩ :=
    exists_finiteIncidenceChart_of_bodiesSeparated root src dst active hLoop hsep
  have h := QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse
    root src dst active hLoop F hSparse hRepresented ac dc
    (finiteMotionIdeal root src dst)
    (finiteChartIdeal_le_finiteMotionIdeal root src dst active ac _) hden
  rw [finiteMotionIdeal_height_eq_rank] at h
  exact_mod_cast h

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0056

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0056/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0056.json"

section BundleSource0057
/- Source: Papers/RigidityDefectRank.lean -/





@[expose] public section

/-!
# The quantitative defect bound for the separated motion quotient

The sparse edge set is chosen from the actual crossing support. Each of
its edges is represented by an original labelled pin, and the active-pin
cardinality equals the original crossing multiplicity sum. The final rank
estimate therefore counts the literal grounded compatibility matrix.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open RB31E2E
open RB31E2E.UniversalHomogeneousChart

/-- Original pin occurrences crossing an arbitrary body labelling. -/
def crossingPinsOn (H : BodyPinIncidence) {I : Type} [DecidableEq I]
    (label : H.Body → I) : Finset H.Pin :=
  Finset.univ.filter fun e => label (H.left e) ≠ label (H.right e)

@[simp] theorem mem_crossingPinsOn (H : BodyPinIncidence) {I : Type} [DecidableEq I]
    (label : H.Body → I) (e : H.Pin) :
    e ∈ crossingPinsOn H label ↔ label (H.left e) ≠ label (H.right e) := by
  simp [crossingPinsOn]

theorem crossingPinsOn_loopless (H : BodyPinIncidence) {I : Type} [DecidableEq I]
    (label : H.Body → I) :
    ∀ e ∈ crossingPinsOn H label, (label ∘ H.left) e ≠ (label ∘ H.right) e := by
  intro e he
  exact (mem_crossingPinsOn H label e).mp he

/-- Counting fibres of the actual unordered endpoint map counts each
crossing occurrence once. -/
theorem card_crossingPinsOn_eq_fineMassOn (H : BodyPinIncidence)
    {I : Type} [Fintype I] [DecidableEq I] (label : H.Body → I) :
    (crossingPinsOn H label).card = H.fineMassOn label := by
  classical
  let pair : H.Pin → Sym2 I := fun e => s(label (H.left e), label (H.right e))
  have hFiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset H.Pin) ((⊤ : SimpleGraph I).edgeFinset) pair
  calc
    (crossingPinsOn H label).card =
        (Finset.univ.filter fun e => pair e ∈ (⊤ : SimpleGraph I).edgeFinset).card := by
      congr 1
      ext e
      simp [crossingPinsOn, pair, SimpleGraph.edgeSet_top, Sym2.mk_isDiag_iff]
    _ = ∑ b ∈ (⊤ : SimpleGraph I).edgeFinset, H.bundleMultiplicityOn label b := by
      rw [← hFiber]
      apply Finset.sum_congr rfl
      intro b hb
      unfold BodyPinIncidence.bundleMultiplicityOn
      congr 1
    _ = ∑ e : SimpleEdge I, H.fineMultiplicityOn label e :=
      sum_completeEdges_eq_sum_simpleEdges _
    _ = H.fineMassOn label := (H.fineMassOn_eq_sum_simpleEdges label).symm

theorem exists_crossingPinOn_activeEdge_eq (H : BodyPinIncidence)
    {I : Type} [Fintype I] [DecidableEq I] (label : H.Body → I)
    (f : SimpleEdge I) (hf : f ∈ H.fineSupportOn label) :
    ∃ e : crossingPinsOn H label,
      SparseNullIncidence.activeEdge (label ∘ H.left) (label ∘ H.right)
        (crossingPinsOn H label) (crossingPinsOn_loopless H label) e = f := by
  classical
  have hpos := (H.mem_fineSupportOn label f).mp hf
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  have hpair : s(label (H.left e), label (H.right e)) = f.1 := by
    simpa only [BodyPinIncidence.fineMultiplicityOn,
      BodyPinIncidence.bundleMultiplicityOn, Finset.mem_filter,
      Finset.mem_univ, true_and] using he
  have hcross : e ∈ crossingPinsOn H label := by
    rw [mem_crossingPinsOn]
    intro h
    apply f.2
    rw [← hpair]
    simp [h]
  exact ⟨⟨e, hcross⟩, Subtype.ext hpair⟩

/-- Every partition-defect upper bound controls the full grounded kernel
once identical motion classes have been collapsed. -/
theorem six_mul_pred_le_genericMotionRank_add_defect
    (H : BodyPinIncidence) (D : ℕ) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (ht : 2 ≤ t)
    (hpartition : PartitionDefectAtMost H D)
    (hsep : BodiesSeparated (π ∘ H.left) (π ∘ H.right)) (root : Fin t) :
    6 * (t - 1) ≤ (genericMotionMatrix root (π ∘ H.left) (π ∘ H.right)).rank + D := by
  have hsmall : ∀ e ∈ H.fineSupportOn π, H.fineMultiplicityOn π e ≤ 2 := by
    intro e he
    exact fineMultiplicity_le_two_of_bodiesSeparated H π hsep e
  obtain ⟨F, hFsub, hFsparse, hFcard⟩ :=
    exists_sparse_nullSkeleton_of_defect_bound H D π hπ ht hpartition hsmall
  have hRepresented : ∀ f ∈ F, ∃ e : crossingPinsOn H π,
      SparseNullIncidence.activeEdge (π ∘ H.left) (π ∘ H.right)
        (crossingPinsOn H π) (crossingPinsOn_loopless H π) e = f := by
    intro f hf
    exact exists_crossingPinOn_activeEdge_eq H π f (hFsub hf)
  have hrank := genericMotionMatrix_rank_ge_active_add_sparse root
    (π ∘ H.left) (π ∘ H.right) (crossingPinsOn H π)
    (crossingPinsOn_loopless H π) hsep F hFsparse hRepresented
  rw [card_crossingPinsOn_eq_fineMassOn, hFcard] at hrank
  omega

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0057

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0057/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0057.json"

section BundleSource0058
/- Source: Papers/RigidityGenericDefectBound.lean -/



@[expose] public section

/-!
# Every partition defect bound controls the whole generic motion kernel

All bodies that are identical on the actual generic kernel are collapsed.
The resulting kernel is linearly isomorphic to the original one, its
bodies are separated by genuine motions, and the quantitative incidence
rank theorem applies. This proves the complete upper-bound direction of
the pair-pin defect formula over the independent pin coefficient field.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open RB31E2E
open RB31E2E.GroundedTwistPolynomial
open RB31E2E.UniversalHomogeneousChart
open MotionQuotient

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The full generic compatible-motion kernel modulo common twists is at
most every upper bound for all partition defects. All intermediate
separation and codimension obligations are derived, not assumed. -/
theorem genericGroundedKernel_finrank_le_partitionDefectBound
    (H : BodyPinIncidence) (root : H.Body) (D : ℕ)
    (hpartition : PartitionDefectAtMost H D) :
    Module.finrank (GenericPinCoefficientField H.Pin)
      (groundedPinOperator root H.left H.right genericPins).ker ≤ D := by
  classical
  let K := GenericPinCoefficientField H.Pin
  let p : H.Pin → RB31E2E.Vec3 K := genericPins
  let C := BodyClasses H.left H.right p
  let t : ℕ := Fintype.card C
  let e : C ≃ Fin t := Fintype.equivFin C
  let π : H.Body → Fin t := e ∘ bodyClass H.left H.right p
  have hπ : Function.Surjective π :=
    e.surjective.comp Quotient.mk_surjective
  have hsep : BodiesSeparated (π ∘ H.left) (π ∘ H.right) := by
    intro i j hij
    have hclasses : e.symm i ≠ e.symm j := by
      intro h
      exact hij (e.symm.injective h)
    obtain ⟨X, hX⟩ := distinct_classes_separated H.left H.right p
      (e.symm i) (e.symm j) hclasses
    refine ⟨fun q => X.1 (e.symm q), ?_, hX⟩
    intro a
    have ha := (mem_motionSpace_iff _ _ _ _).mp X.2 a
    simpa [π, classSource, classTarget] using ha
  let qroot : Fin t := π root
  let equivGrounded :
      groundedMotionSpace qroot (π ∘ H.left) (π ∘ H.right) p ≃ₗ[K]
        groundedMotionSpace root H.left H.right p :=
    (groundedReindexEquiv e (bodyClass H.left H.right p root)
      (classSource H.left H.right p) (classTarget H.left H.right p) p).trans
      (groundedClassEquiv root H.left H.right p)
  have hnullity :
      Module.finrank K (groundedPinOperator qroot (π ∘ H.left) (π ∘ H.right) p).ker =
        Module.finrank K (groundedPinOperator root H.left H.right p).ker :=
    (groundedKernelEquiv qroot (π ∘ H.left) (π ∘ H.right) p).finrank_eq.trans
      (equivGrounded.finrank_eq.trans (groundedKernelEquiv root H.left H.right p).finrank_eq.symm)
  have hRN := genericMotion_rank_add_nullity qroot (π ∘ H.left) (π ∘ H.right)
  simp only [Fintype.card_fin] at hRN
  change (genericMotionMatrix qroot (π ∘ H.left) (π ∘ H.right)).rank +
    Module.finrank K (groundedPinOperator qroot (π ∘ H.left) (π ∘ H.right) p).ker =
      6 * (t - 1) at hRN
  rw [hnullity] at hRN
  by_cases ht : 2 ≤ t
  · have hRank := six_mul_pred_le_genericMotionRank_add_defect H D π hπ ht hpartition hsep qroot
    change Module.finrank K (groundedPinOperator root H.left H.right p).ker ≤ D
    omega
  · change Module.finrank K (groundedPinOperator root H.left H.right p).ker ≤ D
    have : t - 1 = 0 := by omega
    rw [this] at hRN
    omega

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0058

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0058/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0058.json"

section BundleSource0059
/- Source: Papers/RigidityZheng_Rigidity_TwistNecessity.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Rigidity/TwistNecessity.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Partition necessity for rigid body--twist systems

For a fixed surjective block labelling, we ground one block and group all
pin constraints by their unordered pair of block labels.  Each grouped
operator factors through one relative six-dimensional twist.  Its signed
pin evaluations have the same kernel as ordinary pin evaluations, so the
proved `0,3,5,6` bundle bounds apply without any rank hypothesis.
-/

namespace RB31E2E

/-- The rank of a finite product of linear maps is at most the sum of the
ranks of its coordinate maps. -/
theorem finrank_range_pi_le_sum
    {k I V : Type*} [Field k] [Fintype I]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : I → Type*} [(i : I) → AddCommGroup (W i)]
    [(i : I) → Module k (W i)]
    (f : (i : I) → V →ₗ[k] W i) :
    Module.finrank k (LinearMap.range (LinearMap.pi f)) ≤
      ∑ i, Module.finrank k (LinearMap.range (f i)) := by
  classical
  let Φ : LinearMap.range (LinearMap.pi f) →ₗ[k]
      ((i : I) → LinearMap.range (f i)) :=
    { toFun := fun y i ↦ ⟨y.1 i, by
        obtain ⟨x, hx⟩ := y.2
        refine ⟨x, ?_⟩
        simpa using congrFun hx i⟩
      map_add' := by
        intro y z
        funext i
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a y
        funext i
        apply Subtype.ext
        rfl }
  have hΦ : Function.Injective Φ := by
    intro y z hyz
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hyz i)
  calc
    Module.finrank k (LinearMap.range (LinearMap.pi f)) ≤
        Module.finrank k ((i : I) → LinearMap.range (f i)) :=
      LinearMap.finrank_le_finrank_of_injective hΦ
    _ = ∑ i, Module.finrank k (LinearMap.range (f i)) := by
      rw [Module.finrank_pi_fintype]

namespace Twist

variable {k I : Type*} [Field k]

/-- The proved bundle bound, transported from `Fin m` to an arbitrary finite
occurrence type without losing occurrence provenance. -/
theorem finrank_range_bundleLinear_le_pinCapacity_card
    [Fintype I] (p : I → Vec3 k) :
    Module.finrank k (LinearMap.range (bundleLinear p)) ≤
      pinCapacity (Fintype.card I) := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let q : Fin (Fintype.card I) → Vec3 k := p ∘ e.symm
  have hker : LinearMap.ker (bundleLinear p) =
      LinearMap.ker (bundleLinear q) := by
    ext X
    constructor
    · intro hX
      rw [LinearMap.mem_ker] at hX ⊢
      funext j
      have hj := congrFun hX (e.symm j)
      simpa [q] using hj
    · intro hX
      rw [LinearMap.mem_ker] at hX ⊢
      funext i
      have hi := congrFun hX (e i)
      simpa [q] using hi
  have hp := (bundleLinear p).finrank_range_add_finrank_ker
  have hq := (bundleLinear q).finrank_range_add_finrank_ker
  rw [hker] at hp
  have hrange : Module.finrank k (LinearMap.range (bundleLinear p)) =
      Module.finrank k (LinearMap.range (bundleLinear q)) := by
    omega
  rw [hrange]
  exact finrank_range_bundleLinear_le_pinCapacity (Fintype.card I) q

/-- Coordinatewise signed evaluation of one relative twist. -/
noncomputable def signedBundleLinear [Fintype I]
    (p : I → Vec3 k) (sign : I → k) :
    Twist k →ₗ[k] (I → Vec3 k) :=
  LinearMap.pi fun i ↦ sign i • evalLinear (p i)

@[simp] theorem signedBundleLinear_apply [Fintype I]
    (p : I → Vec3 k) (sign : I → k) (X : Twist k) (i : I) :
    signedBundleLinear p sign X i = sign i • eval X (p i) := by
  simp [signedBundleLinear]

/-- Nonzero coordinate signs do not change the kernel of bundle evaluation. -/
theorem ker_signedBundleLinear_eq [Fintype I]
    (p : I → Vec3 k) (sign : I → k) (hsign : ∀ i, sign i ≠ 0) :
    LinearMap.ker (signedBundleLinear p sign) =
      LinearMap.ker (bundleLinear p) := by
  ext X
  constructor
  · intro hX
    rw [LinearMap.mem_ker] at hX ⊢
    funext i
    have hi := congrFun hX i
    simp only [signedBundleLinear_apply, Pi.zero_apply] at hi
    exact (smul_eq_zero.mp hi).resolve_left (hsign i)
  · intro hX
    rw [LinearMap.mem_ker] at hX ⊢
    funext i
    have hi := congrFun hX i
    simp only [bundleLinear_apply, Pi.zero_apply] at hi
    simp [signedBundleLinear_apply, hi]

/-- The `0,3,5,6` bound is invariant under independent nonzero signs on the
occurrence coordinates. -/
theorem finrank_range_signedBundleLinear_le_pinCapacity_card [Fintype I]
    (p : I → Vec3 k) (sign : I → k) (hsign : ∀ i, sign i ≠ 0) :
    Module.finrank k (LinearMap.range (signedBundleLinear p sign)) ≤
      pinCapacity (Fintype.card I) := by
  have hker := ker_signedBundleLinear_eq p sign hsign
  have hs := (signedBundleLinear p sign).finrank_range_add_finrank_ker
  have hu := (bundleLinear p).finrank_range_add_finrank_ker
  rw [hker] at hs
  have hrange : Module.finrank k (LinearMap.range (signedBundleLinear p sign)) =
      Module.finrank k (LinearMap.range (bundleLinear p)) := by
    omega
  rw [hrange]
  exact finrank_range_bundleLinear_le_pinCapacity_card p

end Twist

namespace BodyPinIncidence

/-- An unordered pair of distinct labels in a `t`-block partition. -/
abbrev PartitionEdge (t : ℕ) :=
  ↑((⊤ : SimpleGraph (Fin t)).edgeFinset)

/-- The occurrence type of pins belonging to one unordered block bundle. -/
abbrev PartitionBundlePin (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :=
  ↑(Finset.univ.filter fun e : H.Pin ↦
    s(π (H.left e), π (H.right e)) = b.1)

@[simp] theorem card_partitionBundlePin (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :
    Fintype.card (H.PartitionBundlePin π b) =
      H.unorderedBundleMultiplicity π b.1 := by
  rw [Fintype.card_subtype]
  simp [PartitionBundlePin, unorderedBundleMultiplicity]

theorem partitionEdge_out_mk {t : ℕ} (b : PartitionEdge t) :
    s(b.1.out.1, b.1.out.2) = b.1 :=
  Quot.out_eq b.1

theorem partitionEdge_out_ne {t : ℕ} (b : PartitionEdge t) :
    b.1.out.1 ≠ b.1.out.2 := by
  intro h
  have hdiag : b.1.IsDiag := by
    rw [← partitionEdge_out_mk b, Sym2.mk_isDiag_iff]
    exact h
  exact (SimpleGraph.not_isDiag_of_mem_edgeFinset b.2) hdiag

/-- The point coordinates in one occurrence-level bundle. -/
def partitionBundlePoint (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → Vec3 ℝ :=
  fun e ↦ p e.1

/-- Sign comparing the stored orientation of a pin occurrence with the
orientation selected by `Sym2.out` for its unordered block bundle. -/
noncomputable def partitionBundleSign (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → ℝ :=
  fun e ↦ if π (H.left e.1) = b.1.out.1 then 1 else -1

theorem partitionBundleSign_ne_zero (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.partitionBundleSign π b e ≠ 0 := by
  classical
  by_cases h : π (H.left e.1) = b.1.out.1 <;>
    simp [partitionBundleSign, h]

/-- All pin constraints in one unordered block bundle, before grounding. -/
noncomputable def blockBundleOperator (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    (Fin t → Twist ℝ) →ₗ[ℝ] (H.PartitionBundlePin π b → Vec3 ℝ) :=
  LinearMap.pi fun e ↦
    (Twist.evalLinear (p e.1)).comp
      (assignmentDifferenceLinear (π (H.left e.1)) (π (H.right e.1)))

@[simp] theorem blockBundleOperator_apply (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t)
    (X : Fin t → Twist ℝ) (e : H.PartitionBundlePin π b) :
    H.blockBundleOperator π p b X e =
      Twist.eval
        (X (π (H.left e.1)) - X (π (H.right e.1))) (p e.1) := by
  simp [blockBundleOperator, assignmentDifferenceLinear]

/-- The oriented relative twist of every occurrence is the selected bundle
relative twist, multiplied by its explicit sign. -/
theorem occurrenceDifference_eq_sign_smul (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (X : Fin t → Twist ℝ) (e : H.PartitionBundlePin π b) :
    X (π (H.left e.1)) - X (π (H.right e.1)) =
      H.partitionBundleSign π b e • (X b.1.out.1 - X b.1.out.2) := by
  classical
  have he : s(π (H.left e.1), π (H.right e.1)) = b.1 :=
    (Finset.mem_filter.mp e.2).2
  have he' : s(π (H.left e.1), π (H.right e.1)) =
      s(b.1.out.1, b.1.out.2) :=
    he.trans (partitionEdge_out_mk b).symm
  rcases Sym2.eq_iff.mp he' with h | h
  · rcases h with ⟨hl, hr⟩
    simp [partitionBundleSign, hl, hr]
  · rcases h with ⟨hl, hr⟩
    have hne : b.1.out.2 ≠ b.1.out.1 := (partitionEdge_out_ne b).symm
    simp [partitionBundleSign, hl, hr, hne]

/-- Explicit factorization of a bundle through one relative twist and its
signed occurrence evaluations. -/
theorem blockBundleOperator_eq_signed_comp (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    H.blockBundleOperator π p b =
      (Twist.signedBundleLinear (H.partitionBundlePoint π p b)
        (H.partitionBundleSign π b)).comp
        (assignmentDifferenceLinear b.1.out.1 b.1.out.2) := by
  apply LinearMap.ext
  intro X
  funext e
  rw [H.blockBundleOperator_apply]
  simp only [LinearMap.comp_apply, Twist.signedBundleLinear_apply,
    assignmentDifferenceLinear]
  rw [H.occurrenceDifference_eq_sign_smul π b X e]
  exact (Twist.evalLinear (p e.1)).map_smul
    (H.partitionBundleSign π b e) (X b.1.out.1 - X b.1.out.2)

/-- Each unordered bundle pays at most its already-proved `0,3,5,6`
capacity, with no genericity or rank premise. -/
theorem finrank_range_blockBundleOperator_le_capacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    Module.finrank ℝ (LinearMap.range (H.blockBundleOperator π p b)) ≤
      pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
  rw [H.blockBundleOperator_eq_signed_comp]
  calc
    Module.finrank ℝ
        (LinearMap.range
          ((Twist.signedBundleLinear (H.partitionBundlePoint π p b)
            (H.partitionBundleSign π b)).comp
            (assignmentDifferenceLinear b.1.out.1 b.1.out.2))) ≤
        Module.finrank ℝ
          (LinearMap.range
            (Twist.signedBundleLinear (H.partitionBundlePoint π p b)
              (H.partitionBundleSign π b))) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    _ ≤ pinCapacity (Fintype.card (H.PartitionBundlePin π b)) :=
      Twist.finrank_range_signedBundleLinear_le_pinCapacity_card _ _
        (H.partitionBundleSign_ne_zero π b)
    _ = pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      rw [H.card_partitionBundlePin]

/-- Rigidity pulls back from bodies to any surjective quotient of the body
set: a block-constant motion is in particular a body motion. -/
theorem twistRigidAt_blocks_of_surjective (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (hπ : Function.Surjective π)
    (p : H.Pin → Vec3 ℝ) (hRigid : TwistRigidAt H.left H.right p) :
    TwistRigidAt (π ∘ H.left) (π ∘ H.right) p := by
  intro X hX
  have hBody : IsTwistMotion H.left H.right p (X ∘ π) := by
    intro e
    exact hX e
  obtain ⟨Y, hY⟩ := hRigid (X ∘ π) hBody
  refine ⟨Y, ?_⟩
  funext i
  obtain ⟨body, hbody⟩ := hπ i
  have hi := congrFun hY body
  simpa [Function.comp_apply, hbody] using hi

/-- All crossing constraints of a grounded block assignment, grouped by
their unordered block bundle.  Internal pins are omitted because a
block-constant twist makes their relative twist identically zero. -/
noncomputable def groupedGroundedBlockOperator (H : BodyPinIncidence)
    {t : ℕ} (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (root : Fin t) :
    (OffRoot root → Twist ℝ) →ₗ[ℝ]
      ((b : PartitionEdge t) → H.PartitionBundlePin π b → Vec3 ℝ) :=
  LinearMap.pi fun b ↦
    (H.blockBundleOperator π p b).comp (extendGroundedLinear root)

@[simp] theorem groupedGroundedBlockOperator_apply
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 ℝ) (root : Fin t)
    (X : OffRoot root → Twist ℝ) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.groupedGroundedBlockOperator π p root X b e =
      Twist.eval
        (extendGrounded root X (π (H.left e.1)) -
          extendGrounded root X (π (H.right e.1))) (p e.1) := by
  simp [groupedGroundedBlockOperator, H.blockBundleOperator_apply,
    extendGroundedLinear]

/-- Under pointwise twist rigidity, the grouped grounded block operator is
injective.  This is the lower-rank half of partition necessity. -/
theorem groupedGroundedBlockOperator_injective_of_twistRigidAt
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (p : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right p) (root : Fin t) :
    Function.Injective (H.groupedGroundedBlockOperator π p root) := by
  classical
  have hBlockRigid : TwistRigidAt (π ∘ H.left) (π ∘ H.right) p :=
    H.twistRigidAt_blocks_of_surjective π hπ p hRigid
  have hGroundInjective : Function.Injective
      (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p) :=
    (groundedPinOperator_injective_iff_twistRigidAt
      root (π ∘ H.left) (π ∘ H.right) p).2 hBlockRigid
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.2
  intro X hX
  have hGroundZero :
      groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p X = 0 := by
    funext e
    by_cases heq : π (H.left e) = π (H.right e)
    · simp [groundedPinOperator_apply, Function.comp_apply, heq,
        Twist.eval, Vec3.cross]
    · let b : PartitionEdge t :=
        ⟨s(π (H.left e), π (H.right e)), by
          simp [Sym2.mk_isDiag_iff, heq]⟩
      let eb : H.PartitionBundlePin π b := ⟨e, by
        simp [PartitionBundlePin, b]⟩
      have hGrouped := congrFun (congrFun hX b) eb
      simpa [groundedPinOperator_apply, Function.comp_apply,
        H.groupedGroundedBlockOperator_apply] using hGrouped
  exact hGroundInjective (by simpa using hGroundZero)

/-- The grouped grounded operator has at least the full dimension of the
grounded block-twist space. -/
theorem six_mul_pred_le_groupedGroundedBlockOperator_rank
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (p : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right p) (root : Fin t) :
    6 * (t - 1) ≤
      Module.finrank ℝ
        (LinearMap.range (H.groupedGroundedBlockOperator π p root)) := by
  have hinj := H.groupedGroundedBlockOperator_injective_of_twistRigidAt
    π hπ p hRigid root
  have hker : LinearMap.ker (H.groupedGroundedBlockOperator π p root) = ⊥ :=
    LinearMap.ker_eq_bot.2 hinj
  have hRN := (H.groupedGroundedBlockOperator π p root).finrank_range_add_finrank_ker
  rw [hker] at hRN
  simp only [finrank_bot, add_zero] at hRN
  have hcard : Fintype.card (OffRoot root) = t - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Fin t ↦ i = root)]
    simp
  have hdomain : Module.finrank ℝ (OffRoot root → Twist ℝ) =
      6 * (t - 1) := by
    rw [Module.finrank_pi_fintype]
    simp [hcard, Nat.mul_comm]
  rw [← hdomain, ← hRN]

/-- The grouped operator's rank is at most the sum of the proved capacities
of its unordered bundles. -/
theorem groupedGroundedBlockOperator_rank_le_partitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 ℝ) (root : Fin t) :
    Module.finrank ℝ
        (LinearMap.range (H.groupedGroundedBlockOperator π p root)) ≤
      H.partitionCapacity π := by
  classical
  calc
    Module.finrank ℝ
        (LinearMap.range (H.groupedGroundedBlockOperator π p root)) ≤
        ∑ b : PartitionEdge t,
          Module.finrank ℝ
            (LinearMap.range
              ((H.blockBundleOperator π p b).comp
                (extendGroundedLinear root))) := by
      exact finrank_range_pi_le_sum fun b ↦
        (H.blockBundleOperator π p b).comp (extendGroundedLinear root)
    _ ≤ ∑ b : PartitionEdge t,
        pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      apply Finset.sum_le_sum
      intro b hb
      calc
        Module.finrank ℝ
            (LinearMap.range
              ((H.blockBundleOperator π p b).comp
                (extendGroundedLinear root))) ≤
            Module.finrank ℝ
              (LinearMap.range (H.blockBundleOperator π p b)) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
        _ ≤ pinCapacity (H.unorderedBundleMultiplicity π b.1) :=
          H.finrank_range_blockBundleOperator_le_capacity π p b
    _ = H.partitionCapacity π := by
      unfold partitionCapacity
      symm
      apply Finset.sum_subtype
      intro b
      rfl

/-- Pointwise twist rigidity forces every body partition to satisfy the
body--pin `0,3,5,6` capacity inequality. -/
theorem partitionCondition_of_twistRigidAt (H : BodyPinIncidence)
    (p : H.Pin → Vec3 ℝ) (hRigid : TwistRigidAt H.left H.right p) :
    H.PartitionCondition := by
  intro t π hπ
  by_cases ht : t = 0
  · subst t
    simp
  · let root : Fin t := ⟨0, Nat.pos_of_ne_zero ht⟩
    exact (H.six_mul_pred_le_groupedGroundedBlockOperator_rank
      π hπ p hRigid root).trans
        (H.groupedGroundedBlockOperator_rank_le_partitionCapacity π p root)

/-- Existential rigid twist realizability implies the complete partition
condition. -/
theorem partitionCondition_of_hasRigidTwistRealization
    (H : BodyPinIncidence)
    (hRigid : HasRigidTwistRealization (k := ℝ) H.left H.right) :
    H.PartitionCondition := by
  obtain ⟨p, hp⟩ := hRigid
  exact H.partitionCondition_of_twistRigidAt p hp

end BodyPinIncidence

end RB31E2E


end
end BundleSource0059

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0059/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0059.json"

section BundleSource0060
/- Source: Papers/RigidityFieldCapacity.lean -/




@[expose] public section

/-!
# Partition capacity over arbitrary coefficient fields

The occurrence-level signed-bundle proof is adapted from Dongzhe Zheng's
Apache-2.0 `TwistNecessity.lean`, commit
`e457fde9100c9b7226bd4d81af6860f210a531ab`. The same actual operators are
used over an arbitrary field, so the rational function coefficient field
in the quantitative proof receives the literal `0,3,5,6` capacity bound.
-/

namespace RB31E2E.BodyPinIncidence

noncomputable section

variable {k : Type*} [Field k]

/-- The point coordinates in one occurrence-level bundle. -/
def partitionBundlePointK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → Vec3 k :=
  fun e ↦ p e.1

/-- Sign comparing the stored orientation of a pin occurrence with the
orientation selected by `Sym2.out` for its unordered block bundle. -/
noncomputable def partitionBundleSignK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → k :=
  fun e ↦ if π (H.left e.1) = b.1.out.1 then 1 else -1

theorem partitionBundleSign_ne_zeroK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.partitionBundleSignK (k := k) π b e ≠ 0 := by
  classical
  by_cases h : π (H.left e.1) = b.1.out.1 <;>
    simp [partitionBundleSignK, h]

/-- All pin constraints in one unordered block bundle, before grounding. -/
noncomputable def blockBundleOperatorK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (b : PartitionEdge t) :
    (Fin t → Twist k) →ₗ[k] (H.PartitionBundlePin π b → Vec3 k) :=
  LinearMap.pi fun e ↦
    (Twist.evalLinear (p e.1)).comp
      (assignmentDifferenceLinear (π (H.left e.1)) (π (H.right e.1)))

@[simp] theorem blockBundleOperator_applyK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (b : PartitionEdge t)
    (X : Fin t → Twist k) (e : H.PartitionBundlePin π b) :
    H.blockBundleOperatorK π p b X e =
      Twist.eval
        (X (π (H.left e.1)) - X (π (H.right e.1))) (p e.1) := by
  simp [blockBundleOperatorK, assignmentDifferenceLinear]

/-- The oriented relative twist of every occurrence is the selected bundle
relative twist, multiplied by its explicit sign. -/
theorem occurrenceDifference_eq_sign_smulK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (X : Fin t → Twist k) (e : H.PartitionBundlePin π b) :
    X (π (H.left e.1)) - X (π (H.right e.1)) =
      H.partitionBundleSignK (k := k) π b e • (X b.1.out.1 - X b.1.out.2) := by
  classical
  have he : s(π (H.left e.1), π (H.right e.1)) = b.1 :=
    (Finset.mem_filter.mp e.2).2
  have he' : s(π (H.left e.1), π (H.right e.1)) =
      s(b.1.out.1, b.1.out.2) :=
    he.trans (partitionEdge_out_mk b).symm
  rcases Sym2.eq_iff.mp he' with h | h
  · rcases h with ⟨hl, hr⟩
    simp [partitionBundleSignK, hl, hr]
  · rcases h with ⟨hl, hr⟩
    have hne : b.1.out.2 ≠ b.1.out.1 := (partitionEdge_out_ne b).symm
    simp [partitionBundleSignK, hl, hr, hne]

/-- Explicit factorization of a bundle through one relative twist and its
signed occurrence evaluations. -/
theorem blockBundleOperator_eq_signed_compK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (b : PartitionEdge t) :
    H.blockBundleOperatorK π p b =
      (Twist.signedBundleLinear (H.partitionBundlePointK π p b)
        (H.partitionBundleSignK (k := k) π b)).comp
        (assignmentDifferenceLinear b.1.out.1 b.1.out.2) := by
  apply LinearMap.ext
  intro X
  funext e
  rw [H.blockBundleOperator_applyK]
  simp only [LinearMap.comp_apply, Twist.signedBundleLinear_apply,
    assignmentDifferenceLinear]
  rw [H.occurrenceDifference_eq_sign_smulK π b X e]
  exact (Twist.evalLinear (p e.1)).map_smul
    (H.partitionBundleSignK (k := k) π b e) (X b.1.out.1 - X b.1.out.2)

/-- Each unordered bundle pays at most its already-proved `0,3,5,6`
capacity, with no genericity or rank premise. -/
theorem finrank_range_blockBundleOperator_le_capacityK
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (b : PartitionEdge t) :
    Module.finrank k (LinearMap.range (H.blockBundleOperatorK π p b)) ≤
      pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
  rw [H.blockBundleOperator_eq_signed_compK]
  calc
    Module.finrank k
        (LinearMap.range
          ((Twist.signedBundleLinear (H.partitionBundlePointK π p b)
            (H.partitionBundleSignK (k := k) π b)).comp
            (assignmentDifferenceLinear b.1.out.1 b.1.out.2))) ≤
        Module.finrank k
          (LinearMap.range
            (Twist.signedBundleLinear (H.partitionBundlePointK π p b)
              (H.partitionBundleSignK (k := k) π b))) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    _ ≤ pinCapacity (Fintype.card (H.PartitionBundlePin π b)) :=
      Twist.finrank_range_signedBundleLinear_le_pinCapacity_card _ _
        (H.partitionBundleSign_ne_zeroK π b)
    _ = pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      rw [H.card_partitionBundlePin]

/-- All crossing constraints of a grounded block assignment, grouped by
their unordered block bundle.  Internal pins are omitted because a
block-constant twist makes their relative twist identically zero. -/
noncomputable def groupedGroundedBlockOperatorK (H : BodyPinIncidence)
    {t : ℕ} (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (root : Fin t) :
    (OffRoot root → Twist k) →ₗ[k]
      ((b : PartitionEdge t) → H.PartitionBundlePin π b → Vec3 k) :=
  LinearMap.pi fun b ↦
    (H.blockBundleOperatorK π p b).comp (extendGroundedLinear root)

@[simp] theorem groupedGroundedBlockOperator_applyK
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t)
    (X : OffRoot root → Twist k) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.groupedGroundedBlockOperatorK π p root X b e =
      Twist.eval
        (extendGrounded root X (π (H.left e.1)) -
          extendGrounded root X (π (H.right e.1))) (p e.1) := by
  simp [groupedGroundedBlockOperatorK, H.blockBundleOperator_applyK,
    extendGroundedLinear]

/-- The grouped operator's rank is at most the sum of the proved capacities
of its unordered bundles. -/
theorem groupedGroundedBlockOperator_rank_le_partitionCapacityK
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t) :
    Module.finrank k
        (LinearMap.range (H.groupedGroundedBlockOperatorK π p root)) ≤
      H.partitionCapacity π := by
  classical
  calc
    Module.finrank k
        (LinearMap.range (H.groupedGroundedBlockOperatorK π p root)) ≤
        ∑ b : PartitionEdge t,
          Module.finrank k
            (LinearMap.range
              ((H.blockBundleOperatorK π p b).comp
                (extendGroundedLinear root))) := by
      exact finrank_range_pi_le_sum fun b ↦
        (H.blockBundleOperatorK π p b).comp (extendGroundedLinear root)
    _ ≤ ∑ b : PartitionEdge t,
        pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      apply Finset.sum_le_sum
      intro b hb
      calc
        Module.finrank k
            (LinearMap.range
              ((H.blockBundleOperatorK π p b).comp
                (extendGroundedLinear root))) ≤
            Module.finrank k
              (LinearMap.range (H.blockBundleOperatorK π p b)) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
        _ ≤ pinCapacity (H.unorderedBundleMultiplicity π b.1) :=
          H.finrank_range_blockBundleOperator_le_capacityK π p b
    _ = H.partitionCapacity π := by
      unfold partitionCapacity
      symm
      apply Finset.sum_subtype
      intro b
      rfl


/-- Grouping occurrences by unordered block pairs changes only the output
indexing and deletes identically zero internal rows. It preserves the
actual kernel. -/
theorem ker_groupedGroundedBlockOperatorK
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t) :
    (H.groupedGroundedBlockOperatorK π p root).ker =
      (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).ker := by
  classical
  ext X
  simp only [LinearMap.mem_ker]
  constructor
  · intro hX
    funext e
    by_cases heq : π (H.left e) = π (H.right e)
    · simp [groundedPinOperator_apply, heq, Twist.eval, Vec3.cross]
    · let b : PartitionEdge t := ⟨s(π (H.left e), π (H.right e)), by
        simp [Sym2.mk_isDiag_iff, heq]⟩
      let eb : H.PartitionBundlePin π b := ⟨e, by simp [PartitionBundlePin, b]⟩
      exact congrFun (congrFun hX b) eb
  · intro hX
    funext b e
    exact congrFun hX e.1

/-- The original grounded block operator has rank at most its actual
partition capacity, including all multiplicities and orientations. -/
theorem groundedBlockOperator_rank_le_partitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t) :
    Module.finrank k (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).range ≤
      H.partitionCapacity π := by
  have h₁ := (H.groupedGroundedBlockOperatorK π p root).finrank_range_add_finrank_ker
  have h₂ := (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).finrank_range_add_finrank_ker
  rw [H.ker_groupedGroundedBlockOperatorK] at h₁
  have hrank := H.groupedGroundedBlockOperator_rank_le_partitionCapacityK π p root
  omega

/-- The partition count is realized as a lower bound on the literal
block-constant grounded kernel, over every field and at every placement. -/
theorem partitionDefect_le_groundedBlockKernel_finrank
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t) :
    6 * (t - 1) - H.partitionCapacity π ≤
      Module.finrank k (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).ker := by
  have hcap := H.groundedBlockOperator_rank_le_partitionCapacity π p root
  have hRN := (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).finrank_range_add_finrank_ker
  have hcard : Fintype.card (OffRoot root) = t - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Fin t => i = root)]
    simp
  have hdim : Module.finrank k (OffRoot root → Twist k) = 6 * (t - 1) := by
    simp [Module.finrank_pi_fintype, hcard, Twist.finrank_twist, Nat.mul_comm]
  rw [hdim] at hRN
  omega

end

end RB31E2E.BodyPinIncidence

end
end BundleSource0060

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0060/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0060.json"

section BundleSource0061
/- Source: Papers/RigidityDefectMaximum.lean -/





@[expose] public section

/-!
# The complete generic pair-pin defect equality

The numerical maximum is taken over every surjective finite labelling of
the body set. Its upper bound is only the elementary six-per-body bound.
The theorem identifies this actual partition maximum with the kernel of
the literal grounded pin operator over independent coordinate parameters.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open RB31E2E
open RB31E2E.UniversalHomogeneousChart
open MotionQuotient

/-- At every placement and over every field, block-constant motions supply
the asserted partition lower bound for the actual grounded kernel. -/
theorem partitionCapacity_add_groundedKernel_finrank_ge
    {k : Type*} [Field k] (H : BodyPinIncidence) (root : H.Body)
    (p : H.Pin → RB31E2E.Vec3 k) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) :
    6 * (t - 1) ≤ H.partitionCapacity π +
      Module.finrank k (groundedPinOperator root H.left H.right p).ker := by
  let block := groundedPinOperator (π root) (π ∘ H.left) (π ∘ H.right) p
  have hrank := H.groundedBlockOperator_rank_le_partitionCapacity π p (π root)
  have hkernel := groundedKernel_finrank_le_of_surjective π hπ root H.left H.right p
  have hRN := block.finrank_range_add_finrank_ker
  have hcard : Fintype.card (OffRoot (π root)) = t - 1 := by
    rw [Fintype.card_subtype_compl (fun v : Fin t => v = π root)]
    simp
  have hdim : Module.finrank k (OffRoot (π root) → RB31E2E.Twist k) = 6 * (t - 1) := by
    simp [Module.finrank_pi_fintype, hcard, RB31E2E.Twist.finrank_twist, Nat.mul_comm]
  rw [hdim] at hRN
  change Module.finrank k block.range ≤ H.partitionCapacity π at hrank
  change Module.finrank k block.ker ≤
    Module.finrank k (groundedPinOperator root H.left H.right p).ker at hkernel
  omega

theorem partitionDefectMaximum_le_groundedKernel_finrank
    {k : Type*} [Field k] (H : BodyPinIncidence) (root : H.Body) (p : H.Pin → RB31E2E.Vec3 k) :
    partitionDefectMaximum H ≤
      Module.finrank k (groundedPinOperator root H.left H.right p).ker := by
  obtain ⟨t, π, hπ, hmax⟩ := partitionDefectMaximum_attained H root
  have h := partitionCapacity_add_groundedKernel_finrank_ge H root p π hπ
  omega

/-- Theorem 5.1, dimension formula over the full independent pin
coefficient field. No pair-pin rank, height, separation, or combinatorial
sparsity assertion is an input. -/
theorem genericGroundedKernel_finrank_eq_partitionDefectMaximum
    (H : BodyPinIncidence) (root : H.Body) :
    Module.finrank (GenericPinCoefficientField H.Pin)
      (groundedPinOperator root H.left H.right genericPins).ker =
      partitionDefectMaximum H := by
  exact le_antisymm
    (genericGroundedKernel_finrank_le_partitionDefectBound H root _
      (partitionDefectMaximum_is_bound H))
    (partitionDefectMaximum_le_groundedKernel_finrank H root genericPins)

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0061

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0061/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0061.json"

section BundleSource0062
/- Source: Papers/RigidityTwistSpace.lean -/



@[expose] public section

/-!
# The actual Euclidean twist space and evaluation maps

These definitions are independent of any rigidity theorem or partition formula.
-/

namespace Papers.Rigidity

open Matrix
open scoped Matrix

/-- Angular velocity and translational velocity. -/
abbrev Twist := Vec3 × Vec3

/-- The velocity of the point `p` under a Euclidean infinitesimal motion. -/
def evaluateTwist (p : Vec3) : Twist →ₗ[ℝ] Vec3 :=
  LinearMap.snd ℝ Vec3 Vec3 +
    ((crossProduct (R := ℝ)).flip p).comp (LinearMap.fst ℝ Vec3 Vec3)

@[simp] theorem evaluateTwist_apply (p : Vec3) (X : Twist) :
    evaluateTwist p X = X.2 + X.1 ⨯₃ p := rfl

/-- Evaluation on a genuine linear subspace of twists. -/
def restrictEvaluation (W : Submodule ℝ Twist) (p : Vec3) : W →ₗ[ℝ] Vec3 :=
  (evaluateTwist p).comp W.subtype

/-- Evaluation has rank at most two at every new pin.  A polynomial generic
rank bound implies this condition; that generic-to-universal bridge is a
separate obligation. -/
def SingularPinSpace (W : Submodule ℝ Twist) : Prop :=
  ∀ p : Vec3, Module.finrank ℝ (restrictEvaluation W p).range ≤ 2

/-- A finite virtual center is exactly the space of rotations fixing it. -/
def finiteCenterSpace (a : Vec3) : Submodule ℝ Twist :=
  (evaluateTwist a).ker

/-- An infinite projective center is represented by a nonzero direction `d`.
Its twists have angular velocity parallel to `d` and translation normal to it. -/
def infiniteCenterSpace (d : Vec3) : Submodule ℝ Twist where
  carrier := {X | X.1 ⨯₃ d = 0 ∧ X.2 ⬝ᵥ d = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    constructor
    · change (X.1 + Y.1) ⨯₃ d = 0
      rw [map_add, LinearMap.add_apply, hX.1, hY.1, add_zero]
    · change (X.2 + Y.2) ⬝ᵥ d = 0
      rw [add_dotProduct, hX.2, hY.2, add_zero]
  smul_mem' := by
    intro c X hX
    constructor
    · change (c • X.1) ⨯₃ d = 0
      rw [map_smul, LinearMap.smul_apply, hX.1, smul_zero]
    · change (c • X.2) ⬝ᵥ d = 0
      simp [smul_dotProduct, hX.2]

theorem evaluateTwist_surjective (p : Vec3) : Function.Surjective (evaluateTwist p) := by
  intro v
  exact ⟨(0, v), by simp⟩

theorem finrank_twist : Module.finrank ℝ Twist = 6 := by
  simp [Twist, Vec3]

theorem finrank_finiteCenterSpace (a : Vec3) :
    Module.finrank ℝ (finiteCenterSpace a) = 3 := by
  have h := (evaluateTwist a).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (evaluateTwist_surjective a)] at h
  have hdim : 3 + Module.finrank ℝ (evaluateTwist a).ker = 6 := by
    simpa [finrank_twist, Vec3] using h
  change Module.finrank ℝ (evaluateTwist a).ker = 3
  omega


end Papers.Rigidity

end
end BundleSource0062

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0062/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0062.json"

section BundleSource0063
/- Source: Papers/RigidityPairPins.lean -/





@[expose] public section

/-!
# Exact pair-pin defect target (Theorem 5.1)

Bodies carry ordinary Euclidean twists; each pin imposes equality of the
velocities assigned by its two bodies. Rank is the attained maximum of the
actual real linear operator, and is not defined by a partition formula.
-/

namespace Papers.Rigidity

open scoped BigOperators
open scoped Classical

structure PairPinGraph (B E : Type) where
  left : E → B
  right : E → B
  loopless : ∀ e, left e ≠ right e

namespace PairPinGraph

variable {B E : Type}

/-- The occurrence-level compatibility operator, with three rows per pin. -/
def compatibilityOperator (J : PairPinGraph B E) (p : E → Vec3) :
    (B → Twist) →ₗ[ℝ] (E → Vec3) :=
  LinearMap.pi fun e =>
    (evaluateTwist (p e)).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.left e) -
        LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.right e))

@[simp] theorem compatibilityOperator_apply
    (J : PairPinGraph B E) (p : E → Vec3) (X : B → Twist) (e : E) :
    compatibilityOperator J p X e =
      evaluateTwist (p e) (X (J.left e)) - evaluateTwist (p e) (X (J.right e)) := by
  simp [compatibilityOperator, sub_add_sub_comm]

noncomputable def pinRank [Fintype B] [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) : ℕ :=
  Module.finrank ℝ (compatibilityOperator J p).range

theorem pinRank_le [Fintype B] [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) : pinRank J p ≤ 6 * Fintype.card B := by
  have h := LinearMap.finrank_range_le (compatibilityOperator J p)
  simpa [pinRank, Module.finrank_pi_fintype, finrank_twist, Nat.mul_comm] using h

noncomputable def genericPinRank [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℕ := by
  classical
  exact Nat.findGreatest (fun r => ∃ p : E → Vec3, pinRank J p = r)
    (6 * Fintype.card B)

theorem pinRank_le_generic [Fintype B] [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) : pinRank J p ≤ genericPinRank J := by
  classical
  exact Nat.le_findGreatest (pinRank_le J p) ⟨p, rfl⟩

theorem genericPinRank_attained [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ∃ p : E → Vec3, pinRank J p = genericPinRank J := by
  classical
  have h := Nat.findGreatest_spec
    (P := fun r => ∃ p : E → Vec3, pinRank J p = r)
    (pinRank_le J (0 : E → Vec3)) ⟨0, rfl⟩
  simpa [genericPinRank] using h

/-- Dimension of compatible motions modulo the six common rigid motions. -/
noncomputable def genericRelativeDof [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℕ :=
  6 * Fintype.card B - genericPinRank J - 6

def commonTwistMap : Twist →ₗ[ℝ] (B → Twist) :=
  LinearMap.pi fun _ => LinearMap.id

@[simp] theorem commonTwistMap_apply (X : Twist) (b : B) :
    commonTwistMap X b = X := rfl

theorem commonTwist_mem_ker (J : PairPinGraph B E) (p : E → Vec3) (X : Twist) :
    commonTwistMap X ∈ (compatibilityOperator J p).ker := by
  rw [LinearMap.mem_ker]
  ext e i
  simp

def commonTwistInKernel (J : PairPinGraph B E) (p : E → Vec3) :
    Twist →ₗ[ℝ] (compatibilityOperator J p).ker :=
  commonTwistMap.codRestrict _ (commonTwist_mem_ker J p)

theorem commonTwistInKernel_injective [Nonempty B]
    (J : PairPinGraph B E) (p : E → Vec3) : Function.Injective (commonTwistInKernel J p) := by
  intro X Y hXY
  obtain ⟨b⟩ := ‹Nonempty B›
  exact congrFun (congrArg Subtype.val hXY) b

/-- Actual compatible motions modulo the actual subspace of common motions. -/
abbrev RelativeMotionSpace (J : PairPinGraph B E) (p : E → Vec3) :=
  (compatibilityOperator J p).ker ⧸ (commonTwistInKernel J p).range

theorem relativeMotionSpace_rank_nullity [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (p : E → Vec3) :
    Module.finrank ℝ (RelativeMotionSpace J p) + pinRank J p + 6 =
      6 * Fintype.card B := by
  have hcommon : Module.finrank ℝ (commonTwistInKernel J p).range = 6 :=
    (LinearMap.finrank_range_of_inj (commonTwistInKernel_injective J p)).trans finrank_twist
  have hquot := (commonTwistInKernel J p).range.finrank_quotient_add_finrank
  have hrank := (compatibilityOperator J p).finrank_range_add_finrank_ker
  have htotal : Module.finrank ℝ (B → Twist) = 6 * Fintype.card B := by
    simp [Module.finrank_pi_fintype, finrank_twist, Nat.mul_comm]
  rw [hcommon] at hquot
  rw [htotal] at hrank
  change Module.finrank ℝ (RelativeMotionSpace J p) + 6 =
    Module.finrank ℝ (compatibilityOperator J p).ker at hquot
  unfold pinRank
  omega

theorem genericPinRank_add_six_le [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) : genericPinRank J + 6 ≤ 6 * Fintype.card B := by
  obtain ⟨p, hp⟩ := genericPinRank_attained J
  have h := relativeMotionSpace_rank_nullity J p
  rw [hp] at h
  omega

/-- At a maximum-rank placement the numerical definition is exactly the
dimension of the quotient by common Euclidean motions; no truncation alters it. -/
theorem genericRelativeDof_eq_finrank_quotient [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (p : E → Vec3) (hp : pinRank J p = genericPinRank J) :
    genericRelativeDof J = Module.finrank ℝ (RelativeMotionSpace J p) := by
  have h := relativeMotionSpace_rank_nullity J p
  rw [hp] at h
  unfold genericRelativeDof
  omega

def pinCapacity : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | _ => 6

noncomputable def multiplicity [Fintype E]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) (i j : Fin t) : ℕ := by
  classical
  exact (Finset.univ.filter fun e =>
    (π (J.left e) = i ∧ π (J.right e) = j) ∨
    (π (J.left e) = j ∧ π (J.right e) = i)).card

noncomputable def partitionCapacity [Fintype E]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) : ℕ :=
  ∑ i : Fin t, ∑ j ∈ Finset.univ.filter (i < ·), pinCapacity (multiplicity J π i j)

/-- Empty labels do not count as blocks. Every partition of a nonempty
finite body set has such a labelling with at most `card B` labels. -/
noncomputable def labelledPartitionDefect [Fintype B] [Fintype E]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) : ℤ :=
  6 * (((Finset.univ.image π).card : ℤ) - 1) - (partitionCapacity J π : ℤ)

/-- The labels used in the maximization represent every equivalence-relation
partition of the finite body set, without a restriction on its number of blocks. -/
theorem exists_partition_labelling [Fintype B] (s : Setoid B) :
    ∃ π : B → Fin (Fintype.card B), ∀ i j, π i = π j ↔ s.r i j := by
  classical
  letI : Fintype (Quotient s) := Fintype.ofFinite _
  have hc : Fintype.card (Quotient s) ≤ Fintype.card B :=
    Fintype.card_le_of_surjective (Quotient.mk s) Quotient.mk_surjective
  let e : Quotient s ↪ Fin (Fintype.card B) :=
    (Fintype.equivFin (Quotient s)).toEmbedding.trans
      ⟨Fin.castLE hc, Fin.castLE_injective hc⟩
  refine ⟨fun b => e (Quotient.mk s b), ?_⟩
  intro i j
  rw [e.injective.eq_iff, Quotient.eq]

noncomputable def maxPartitionDefect [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℤ :=
  (Finset.univ.image (fun π : B → Fin (Fintype.card B) => labelledPartitionDefect J π)).max'
    (Finset.image_nonempty.mpr ⟨Fintype.equivFin B, Finset.mem_univ _⟩)

theorem multiplicity_const_of_ne [Fintype E] (J : PairPinGraph B E)
    {t : ℕ} (a i j : Fin t) (hij : i ≠ j) :
    multiplicity J (fun _ => a) i j = 0 := by
  classical
  have hn : ¬ ((a = i ∧ a = j) ∨ (a = j ∧ a = i)) := by
    rintro (⟨hi, hj⟩ | ⟨hj, hi⟩)
    · exact hij (hi.symm.trans hj)
    · exact hij (hi.symm.trans hj)
  simp [multiplicity, hn]

theorem partitionCapacity_const [Fintype E] (J : PairPinGraph B E)
    {t : ℕ} (a : Fin t) : partitionCapacity J (fun _ => a) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  rw [multiplicity_const_of_ne J a i j hij]
  rfl

theorem labelledPartitionDefect_const [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) {t : ℕ} (a : Fin t) :
    labelledPartitionDefect J (fun _ => a) = 0 := by
  classical
  simp [labelledPartitionDefect, partitionCapacity_const,
    Finset.image_const Finset.univ_nonempty]

/-- The one-block partition gives zero defect, so the integer maximum is
nonnegative before any rigidity or incidence theorem is applied. -/
theorem maxPartitionDefect_nonneg [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) : 0 ≤ maxPartitionDefect J := by
  classical
  let a : Fin (Fintype.card B) := ⟨0, Fintype.card_pos⟩
  have hm : labelledPartitionDefect J (fun _ => a) ∈
      Finset.univ.image (fun π : B → Fin (Fintype.card B) => labelledPartitionDefect J π) :=
    Finset.mem_image.mpr ⟨fun _ => a, Finset.mem_univ _, rfl⟩
  have h := Finset.le_max' _ _ hm
  simpa [maxPartitionDefect, labelledPartitionDefect_const] using h

/-- The finite maximum is attained by an actual partition labelling. -/
theorem maxPartitionDefect_attained [Fintype B] [Fintype E]
    (J : PairPinGraph B E) :
    ∃ π : B → Fin (Fintype.card B), labelledPartitionDefect J π = maxPartitionDefect J := by
  classical
  have hm := Finset.max'_mem
    (Finset.univ.image (fun π : B → Fin (Fintype.card B) => labelledPartitionDefect J π))
    (Finset.image_nonempty.mpr ⟨Fintype.equivFin B, Finset.mem_univ _⟩)
  obtain ⟨π, _, hπ⟩ := Finset.mem_image.mp hm
  exact ⟨π, hπ⟩

noncomputable def singletonPartitionDefect [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℤ :=
  labelledPartitionDefect J (Fintype.equivFin B)

/-- Distinct body pairs are not rigidly linked at generic pin parameters. -/
def NoMergedBodies [Fintype B] [Fintype E] (J : PairPinGraph B E) : Prop :=
  ∀ i j : B, i ≠ j → ∃ p : E → Vec3,
    pinRank J p = genericPinRank J ∧
    ∃ X : B → Twist, X ∈ (compatibilityOperator J p).ker ∧ X i ≠ X j

/-- No parallel pin occurrences. -/
def IsSimple (J : PairPinGraph B E) : Prop :=
  Function.Injective (fun e => s(J.left e, J.right e))

end PairPinGraph

/-- The full three-part assertion of Theorem 5.1, recorded as an unproved
target proposition. A checked definition is not a proof of this claim. -/
def PairPinDefectClaim : Prop :=
  ∀ (B E : Type) [Fintype B] [Fintype E] [Nonempty B] (J : PairPinGraph B E),
    (J.genericRelativeDof : ℤ) = J.maxPartitionDefect ∧
    (J.NoMergedBodies →
      (J.genericRelativeDof : ℤ) = J.singletonPartitionDefect ∧
      (J.IsSimple → J.genericPinRank = 3 * Fintype.card E))

end Papers.Rigidity

end
end BundleSource0063

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0063/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0063.json"

section BundleSource0064
/- Source: Papers/RigidityPairPinIncidence.lean -/




@[expose] public section

namespace Papers.Rigidity.PairPinGraph
noncomputable section
variable {B E : Type} [Fintype B] [Fintype E]

/-- The imported incidence structure carries exactly the same endpoints,
occurrences and looplessness as the paper-facing pair-pin graph. -/
abbrev toBodyPinIncidence (J : PairPinGraph B E) : RB31E2E.BodyPinIncidence where
  Body := B
  Pin := E
  bodyFinite := inferInstance
  pinFinite := inferInstance
  bodyDecidableEq := Classical.decEq B
  pinDecidableEq := Classical.decEq E
  left := J.left
  right := J.right
  loopless := J.loopless

end
end Papers.Rigidity.PairPinGraph

end
end BundleSource0064

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0064/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0064.json"

section BundleSource0065
/- Source: Papers/RigidityPairPinGenericity.lean -/





@[expose] public section

/-!
# Faithfulness of generic pin rank over the real numbers

Grounding removes exactly the common Euclidean motions and does not alter
any output constraint. The rational-function matrix rank is then proved
equal to the attained maximum rank of the original real pin operator.
-/

namespace Papers.Rigidity.PairPinGraph

noncomputable section

open RB31E2E.GroundedTwistPolynomial
open GenericPinIdeal

variable {B E : Type} [Fintype B] [Fintype E]

theorem zheng_motionOperator_eq (J : PairPinGraph B E) (p : E → Vec3) :
    MotionQuotient.motionOperator J.left J.right p = compatibilityOperator J p := by
  apply LinearMap.ext
  intro X
  funext e i
  fin_cases i <;>
    simp [MotionQuotient.motionOperator_apply, compatibilityOperator_apply,
      RB31E2E.Twist.eval, RB31E2E.Vec3.cross, cross_apply]

/-- Every ungrounded output is also obtained after subtracting the twist
of the grounding body. The actual constraint ranges are equal. -/
theorem range_groundedPinOperator_eq [DecidableEq B]
    (J : PairPinGraph B E) (root : B) (p : E → Vec3) :
    (RB31E2E.groundedPinOperator root J.left J.right p).range =
      (compatibilityOperator J p).range := by
  rw [← zheng_motionOperator_eq]
  apply le_antisymm
  · rintro y ⟨X, rfl⟩
    refine ⟨RB31E2E.extendGrounded root X, ?_⟩
    funext e
    simp [MotionQuotient.motionOperator_apply, RB31E2E.groundedPinOperator_apply,
      RB31E2E.Twist.eval_sub]
  · rintro y ⟨X, rfl⟩
    let Y : RB31E2E.OffRoot root → RB31E2E.Twist ℝ := fun w => X w.1 - X root
    have hext : RB31E2E.extendGrounded root Y = fun v => X v - X root := by
      funext v
      by_cases hv : v = root
      · subst v
        simp
      · simp [RB31E2E.extendGrounded, Y, hv]
    refine ⟨Y, ?_⟩
    funext e
    rw [RB31E2E.groundedPinOperator_apply, hext]
    have hdiff : (X (J.left e) - X root) - (X (J.right e) - X root) =
        X (J.left e) - X (J.right e) := by abel
    rw [hdiff, RB31E2E.Twist.eval_sub, MotionQuotient.motionOperator_apply]

theorem pinRank_eq_groundedMatrix_rank [DecidableEq B]
    (J : PairPinGraph B E) (root : B) (p : E → Vec3) :
    pinRank J p = (groundedPinMatrix root J.left J.right p).rank := by
  rw [groundedPinMatrix_rank_eq_operator_rank, range_groundedPinOperator_eq]
  rfl

/-- The independent-parameter rank equals the maximum real rank of the
actual pin operator. Every occurrence and all three coordinate rows are
preserved. -/
theorem genericPinRank_eq_genericMotionMatrix_rank [DecidableEq B]
    (J : PairPinGraph B E) (root : B) :
    genericPinRank J = (genericMotionMatrix root J.left J.right).rank := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := genericPinRank_attained J
    rw [← hp, pinRank_eq_groundedMatrix_rank J root p]
    exact real_groundedPinMatrix_rank_le_generic root J.left J.right p
  · obtain ⟨p, hp⟩ := exists_real_groundedPinMatrix_rank_eq_generic root J.left J.right
    rw [← hp, ← pinRank_eq_groundedMatrix_rank J root p]
    exact pinRank_le_generic J p

/-- Generic dimension modulo the common Euclidean motions is the actual
kernel dimension over the independent rational pin coordinates. -/
theorem genericRelativeDof_eq_genericGroundedKernel_finrank [DecidableEq B]
    (J : PairPinGraph B E) (root : B) :
    genericRelativeDof J =
      Module.finrank (PinField E)
        (RB31E2E.groundedPinOperator root J.left J.right genericPins).ker := by
  have hRN := genericMotion_rank_add_nullity root J.left J.right
  have hcard : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨root⟩
  rw [← genericPinRank_eq_genericMotionMatrix_rank J root] at hRN
  unfold genericRelativeDof
  omega


/-- At every real maximum-rank placement, grounding has exactly the
paper's generic relative number of degrees of freedom. -/
theorem realGroundedKernel_finrank_eq_genericRelativeDof [DecidableEq B]
    (J : PairPinGraph B E) (root : B) (p : E → Vec3)
    (hp : pinRank J p = genericPinRank J) :
    Module.finrank ℝ (RB31E2E.groundedPinOperator root J.left J.right p).ker =
      genericRelativeDof J := by
  have hRN := (RB31E2E.groundedPinOperator root J.left J.right p).finrank_range_add_finrank_ker
  rw [range_groundedPinOperator_eq] at hRN
  have hcard : Fintype.card (RB31E2E.OffRoot root) = Fintype.card B - 1 := by
    rw [Fintype.card_subtype_compl (fun b : B => b = root)]
    simp
  have hdim : Module.finrank ℝ (RB31E2E.OffRoot root → RB31E2E.Twist ℝ) =
      6 * (Fintype.card B - 1) := by
    simp [Module.finrank_pi_fintype, hcard, RB31E2E.Twist.finrank_twist, Nat.mul_comm]
  rw [hdim] at hRN
  change pinRank J p + _ = _ at hRN
  rw [hp] at hRN
  have hpos : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨root⟩
  unfold genericRelativeDof
  omega

end

end Papers.Rigidity.PairPinGraph

end
end BundleSource0065

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0065/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0065.json"

section BundleSource0066
/- Source: Papers/RigidityPartitionCorrespondence.lean -/







@[expose] public section

/-!
# Exact correspondence of the two partition maxima

Unused finite labels have zero incident capacity. Injective relabelling
preserves every nonempty unordered bundle, and normalizing the used labels
turns every paper-facing labelling into a surjection. This identifies the
integer maximum in Theorem 5.1 with the natural maximum used in the generic
kernel proof, including all partitions and the zero-defect case.
-/

noncomputable section

namespace RB31E2E.BodyPinIncidence

/-- Only unordered pairs represented by crossing occurrences can contribute. -/
def actualPairs (H : BodyPinIncidence) {I : Type} [DecidableEq I]
    (label : H.Body → I) : Finset (Sym2 I) :=
  (Finset.univ.image fun e => s(label (H.left e), label (H.right e))).filter
    (fun b => ¬ b.IsDiag)

theorem capacityOn_eq_sum_actualPairs (H : BodyPinIncidence)
    {I : Type} [Fintype I] [DecidableEq I] (label : H.Body → I) :
    H.capacityOn label = ∑ b ∈ H.actualPairs label, pinCapacity (H.bundleMultiplicityOn label b) := by
  classical
  have hsub : H.actualPairs label ⊆ (⊤ : SimpleGraph I).edgeFinset := by
    intro b hb
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet] using
      (Finset.mem_filter.mp hb).2
  unfold capacityOn
  symm
  apply Finset.sum_subset hsub
  intro b hb hnot
  have hdiag : ¬ b.IsDiag := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet] using hb
  have hzero : H.bundleMultiplicityOn label b = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    apply hnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨e, Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩, hdiag⟩
  simp [hzero]

theorem bundleMultiplicityOn_comp_injective (H : BodyPinIncidence)
    {I J : Type} [DecidableEq I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (label : H.Body → I) (b : Sym2 I) :
    H.bundleMultiplicityOn (f ∘ label) (b.map f) = H.bundleMultiplicityOn label b := by
  unfold bundleMultiplicityOn
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro e _
  change Sym2.map f s(label (H.left e), label (H.right e)) = Sym2.map f b ↔ _
  exact (Sym2.map.injective hf).eq_iff

theorem actualPairs_comp_injective (H : BodyPinIncidence)
    {I J : Type} [DecidableEq I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (label : H.Body → I) :
    H.actualPairs (f ∘ label) = (H.actualPairs label).image (Sym2.map f) := by
  unfold actualPairs
  simp only [Function.comp_apply]
  rw [show (Finset.univ.image fun e => s(f (label (H.left e)), f (label (H.right e)))) =
      (Finset.univ.image fun e => s(label (H.left e), label (H.right e))).image
        (Sym2.map f) by rw [Finset.image_image] <;> rfl]
  rw [Finset.filter_image]
  apply congrArg (fun s : Finset (Sym2 I) => s.image (Sym2.map f))
  apply Finset.filter_congr
  intro b _
  exact not_congr (Sym2.isDiag_map hf)

/-- Adding unused labels or permuting labels cannot alter any capacity. -/
theorem capacityOn_comp_injective (H : BodyPinIncidence)
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (label : H.Body → I) :
    H.capacityOn (f ∘ label) = H.capacityOn label := by
  rw [capacityOn_eq_sum_actualPairs, capacityOn_eq_sum_actualPairs,
    actualPairs_comp_injective H f hf label]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [bundleMultiplicityOn_comp_injective H f hf label b]
  · intro a ha b hb hab
    exact Sym2.map.injective hf hab

end RB31E2E.BodyPinIncidence

namespace Papers.Rigidity.PairPinGraph

open GenericPinIdeal

variable {B E : Type} [Fintype B] [Fintype E]

/-- Summing over unordered pairs is the same as summing once over `i < j`.
The equality is about the literal occurrence multiplicities. -/
theorem partitionCapacity_eq_incidenceCapacity (J : PairPinGraph B E)
    {t : ℕ} (π : B → Fin t) :
    partitionCapacity J π = J.toBodyPinIncidence.partitionCapacity π := by
  classical
  let H := J.toBodyPinIncidence
  have htop : (⊤ : SimpleGraph (Fin t)).edgeFinset =
      (Finset.univ.sym2.filter fun b => ¬ b.IsDiag) := by
    ext b
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet, Finset.mem_filter, Finset.sym2_univ, Finset.mem_univ, true_and]
  have hfilter : (Finset.univ : Finset (Fin t)).offDiag.filter (fun a => a.1 < a.2) =
      (Finset.univ ×ˢ Finset.univ).filter (fun a : Fin t × Fin t => a.1 < a.2) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ,
      true_and, Finset.mem_product]
    exact and_iff_right_of_imp ne_of_lt
  have hmult (i j : Fin t) : H.unorderedBundleMultiplicity π s(i,j) = multiplicity J π i j := by
    exact (H.unorderedBundleMultiplicity_mk π i j).trans rfl
  change _ = ∑ b ∈ (⊤ : SimpleGraph (Fin t)).edgeFinset,
    RB31E2E.pinCapacity (H.unorderedBundleMultiplicity π b)
  rw [htop, Finset.sum_sym2_filter_not_isDiag, hfilter, Finset.sum_filter, Finset.sum_product]
  simp only [partitionCapacity, Finset.sum_filter, hmult] <;> rfl

theorem partitionCapacity_comp_injective (J : PairPinGraph B E)
    {t n : ℕ} (f : Fin t → Fin n) (hf : Function.Injective f) (π : B → Fin t) :
    partitionCapacity J (f ∘ π) = partitionCapacity J π := by
  rw [partitionCapacity_eq_incidenceCapacity, partitionCapacity_eq_incidenceCapacity]
  exact J.toBodyPinIncidence.capacityOn_comp_injective f hf π

/-- Every labelling can be normalized to exactly its used labels, without
changing the capacity sum. -/
theorem normalize_partition_labelling (J : PairPinGraph B E)
    {n : ℕ} (π : B → Fin n) :
    ∃ σ : B → Fin ((Finset.univ.image π).card), Function.Surjective σ ∧
      partitionCapacity J σ = partitionCapacity J π := by
  classical
  let S := Finset.univ.image π
  let τ : B → S := fun b => ⟨π b, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
  have hτ : Function.Surjective τ := by
    intro a
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp a.2
    exact ⟨b, Subtype.ext hb⟩
  let e : S ≃ Fin S.card := S.equivFin
  let σ : B → Fin S.card := e ∘ τ
  let f : Fin S.card → Fin n := fun i => (e.symm i).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have heq : f ∘ σ = π := by
    funext b
    simp [f, σ, τ]
  refine ⟨σ, e.surjective.comp hτ, ?_⟩
  calc
    partitionCapacity J σ = partitionCapacity J (f ∘ σ) :=
      (partitionCapacity_comp_injective J f hf σ).symm
    _ = partitionCapacity J π := congrArg (fun q : B → Fin n => partitionCapacity J q) heq

theorem labelledPartitionDefect_le_natMaximum [Nonempty B]
    (J : PairPinGraph B E) {n : ℕ} (π : B → Fin n) :
    labelledPartitionDefect J π ≤ (partitionDefectMaximum J.toBodyPinIncidence : ℤ) := by
  classical
  obtain ⟨σ, hσ, hcap⟩ := normalize_partition_labelling J π
  have hb := partitionDefectMaximum_is_bound J.toBodyPinIncidence _ σ hσ
  rw [← partitionCapacity_eq_incidenceCapacity, hcap] at hb
  have hpos : 0 < (Finset.univ.image π).card := by
    exact Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  unfold labelledPartitionDefect
  omega

theorem natDefect_le_paperMaximum [Nonempty B]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) (hπ : Function.Surjective π) :
    (6 * (t - 1) - J.toBodyPinIncidence.partitionCapacity π : ℕ) ≤
      (maxPartitionDefect J).toNat := by
  classical
  have ht : t ≤ Fintype.card B := by simpa using Fintype.card_le_of_surjective π hπ
  let f : Fin t → Fin (Fintype.card B) := Fin.castLE ht
  have hf : Function.Injective f := Fin.castLE_injective ht
  have hused : (Finset.univ.image (f ∘ π)).card = t := by
    rw [show Finset.univ.image (f ∘ π) = (Finset.univ : Finset (Fin t)).image f by
      rw [← Finset.image_image, Finset.image_univ_of_surjective hπ]]
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hle : labelledPartitionDefect J (f ∘ π) ≤ maxPartitionDefect J := by
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨f ∘ π, Finset.mem_univ _, rfl⟩)
  have hn := maxPartitionDefect_nonneg J
  have htpos : 0 < t := by
    obtain ⟨b⟩ := ‹Nonempty B›
    exact lt_of_le_of_lt (Nat.zero_le _) (π b).isLt
  rw [labelledPartitionDefect, hused, partitionCapacity_comp_injective J f hf π,
    partitionCapacity_eq_incidenceCapacity] at hle
  omega

/-- The natural maximum is exactly the integer maximum in the paper-facing
statement; truncation changes no result because the one-block defect is zero. -/
theorem maxPartitionDefect_eq_natMaximum [Nonempty B] (J : PairPinGraph B E) :
    maxPartitionDefect J = (partitionDefectMaximum J.toBodyPinIncidence : ℤ) := by
  classical
  apply le_antisymm
  · obtain ⟨π, hπ⟩ := maxPartitionDefect_attained J
    rw [← hπ]
    exact labelledPartitionDefect_le_natMaximum J π
  · obtain ⟨root⟩ := ‹Nonempty B›
    obtain ⟨t, π, hπ, hmax⟩ := partitionDefectMaximum_attained J.toBodyPinIncidence root
    have h := natDefect_le_paperMaximum J π hπ
    have hn := maxPartitionDefect_nonneg J
    rw [← hmax] at h
    omega

end Papers.Rigidity.PairPinGraph

end

end
end BundleSource0066

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0066/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0066.json"

section BundleSource0067
/- Source: Papers/RigidityPairPinDefect.lean -/





@[expose] public section

/-!
# The exact generic pair-pin dimension formula

The conclusion uses the original real compatibility operator and the
original integer maximum over all body partitions. The rational-function
proof and both directions of the statement correspondence are explicit
imports; no desired rank statement is stored in an input structure.
-/

namespace Papers.Rigidity

noncomputable section

/-- The dimension formula of Theorem 5.1 for every finite nonempty body set
and every finite loopless pin multigraph, with no restriction on the
numbers of bodies, pins, parallel occurrences or rigid clusters. -/
theorem pairPin_defect_dimension
    {B E : Type} [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) :
    (J.genericRelativeDof : ℤ) = J.maxPartitionDefect := by
  classical
  obtain ⟨root⟩ := ‹Nonempty B›
  rw [PairPinGraph.maxPartitionDefect_eq_natMaximum]
  apply congrArg (fun n : ℕ => (n : ℤ))
  rw [PairPinGraph.genericRelativeDof_eq_genericGroundedKernel_finrank J root]
  exact GenericPinIdeal.genericGroundedKernel_finrank_eq_partitionDefectMaximum
    J.toBodyPinIncidence root

end

end Papers.Rigidity

end
end BundleSource0067

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0067/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0067.json"

section BundleSource0068
/- Source: Papers/RigidityPairPinRows.lean -/




@[expose] public section

/-!
# Actual pin rows and the rank statement in Theorem 5.1

This identifies the numerical full-row-rank conclusion with linear
independence of the literal three coordinate constraints at every pin.
-/

namespace Papers.Rigidity.PairPinGraph

variable {B E : Type}

def flattenPinCoordinates : (E → Vec3) ≃ₗ[ℝ] (E × Fin 3 → ℝ) where
  toFun y a := y a.1 a.2
  invFun y e i := y (e, i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- One literal coordinate row of a pin compatibility equation. -/
def pinRow (J : PairPinGraph B E) (p : E → Vec3) (a : E × Fin 3) :
    (B → Twist) →ₗ[ℝ] ℝ :=
  (LinearMap.proj a.2).comp ((LinearMap.proj a.1).comp (compatibilityOperator J p))

@[simp] theorem pinRow_apply (J : PairPinGraph B E) (p : E → Vec3)
    (a : E × Fin 3) (X : B → Twist) :
    pinRow J p a X =
      evaluateTwist (p a.1) (X (J.left a.1)) a.2 -
        evaluateTwist (p a.1) (X (J.right a.1)) a.2 := by
  simp [pinRow]

theorem linearIndependent_pinRows_iff_surjective [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) :
    LinearIndependent ℝ (pinRow J p) ↔ Function.Surjective (compatibilityOperator J p) := by
  classical
  let F := flattenPinCoordinates.toLinearMap.comp (compatibilityOperator J p)
  let b := (Pi.basisFun ℝ (E × Fin 3)).dualBasis
  have he : (fun a => F.dualMap (b a)) = pinRow J p := by
    funext a
    apply LinearMap.ext
    intro X
    simp [F, b, Module.Basis.dualBasis_apply, pinRow, flattenPinCoordinates]
  have hi : LinearIndependent ℝ (pinRow J p) ↔ Function.Injective F.dualMap := by
    rw [← he]
    constructor
    · exact LinearMap.injective_of_linearIndependent b.span_eq
    · intro h
      exact b.linearIndependent.map' F.dualMap (LinearMap.ker_eq_bot.mpr h)
  rw [hi, LinearMap.dualMap_injective_iff]
  constructor
  · intro h y
    obtain ⟨X, hX⟩ := h (flattenPinCoordinates y)
    exact ⟨X, flattenPinCoordinates.injective hX⟩
  · intro h y
    obtain ⟨X, hX⟩ := h (flattenPinCoordinates.symm y)
    exact ⟨X, by simpa [F] using congrArg flattenPinCoordinates hX⟩

theorem linearIndependent_pinRows_iff_pinRank [Fintype B] [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) :
    LinearIndependent ℝ (pinRow J p) ↔ pinRank J p = 3 * Fintype.card E := by
  rw [linearIndependent_pinRows_iff_surjective, ← LinearMap.range_eq_top]
  constructor
  · intro h
    unfold pinRank
    rw [h]
    simp [Vec3, Module.finrank_pi_fintype, Nat.mul_comm]
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa [pinRank, Vec3, Module.finrank_pi_fintype, Nat.mul_comm] using h

/-- Full generic row rank is equivalent to independence of the actual pin
rows at every placement attaining that rank. -/
theorem genericPinRank_eq_iff_pinRows_independent [Fintype B] [Fintype E]
    (J : PairPinGraph B E) :
    genericPinRank J = 3 * Fintype.card E ↔
      ∀ p : E → Vec3, pinRank J p = genericPinRank J →
        LinearIndependent ℝ (pinRow J p) := by
  constructor
  · intro h p hp
    exact (linearIndependent_pinRows_iff_pinRank J p).mpr (hp.trans h)
  · intro h
    obtain ⟨p, hp⟩ := genericPinRank_attained J
    exact hp.symm.trans ((linearIndependent_pinRows_iff_pinRank J p).mp (h p hp))

end Papers.Rigidity.PairPinGraph

end
end BundleSource0068

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0068/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0068.json"

section BundleSource0069
/- Source: Papers/RigidityPairPinOptimal.lean -/




@[expose] public section

/-!
# Optimal singleton partitions and independence of every pin row

An optimal block-constant kernel has the dimension of the whole actual
motion kernel. The inclusion is therefore onto. This proves that an
optimal partition can only identify bodies already in one rigid cluster;
when no bodies merge, its blocks are singletons. The simple-graph case
then has all three rows at every pin independent.
-/

namespace Papers.Rigidity.PairPinGraph

noncomputable section

open GenericPinIdeal
open MotionQuotient

variable {B E : Type} [Fintype B] [Fintype E] [Nonempty B]

/-- The no-merged-bodies hypothesis forces every optimal partition to be
injective, using actual maximum-rank real motions as its witnesses. -/
theorem optimal_partition_injective (J : PairPinGraph B E) (hNo : NoMergedBodies J)
    {t : ℕ} (π : B → Fin t) (hπ : Function.Surjective π)
    (hopt : 6 * (t - 1) - J.toBodyPinIncidence.partitionCapacity π = genericRelativeDof J) :
    Function.Injective π := by
  classical
  obtain ⟨root⟩ := ‹Nonempty B›
  intro u v huv
  by_contra hne
  obtain ⟨p, hp, X, hX, hXne⟩ := hNo u v hne
  have hfull := realGroundedKernel_finrank_eq_genericRelativeDof J root p hp
  have hlower := J.toBodyPinIncidence.partitionDefect_le_groundedBlockKernel_finrank π p (π root)
  change 6 * (t - 1) - J.toBodyPinIncidence.partitionCapacity π ≤
    Module.finrank ℝ
      (RB31E2E.groundedPinOperator (π root) (π ∘ J.left) (π ∘ J.right) p).ker at hlower
  rw [hopt] at hlower
  have hupper := groundedKernel_finrank_le_of_surjective π hπ root J.left J.right p
  have hdim : Module.finrank ℝ
      (RB31E2E.groundedPinOperator (π root) (π ∘ J.left) (π ∘ J.right) p).ker =
        Module.finrank ℝ (RB31E2E.groundedPinOperator root J.left J.right p).ker := by
    omega
  have hMotion : RB31E2E.IsTwistMotion J.left J.right p X := by
    apply (mem_motionSpace_iff J.left J.right p X).mp
    change X ∈ (motionOperator J.left J.right p).ker
    rwa [zheng_motionOperator_eq]
  exact hXne (equal_twists_of_groundedKernel_finrank_eq
    π hπ root J.left J.right p hdim u v huv X hMotion)

/-- The singleton partition attains the integer defect maximum whenever
no pair of distinct bodies belongs to one generic rigid cluster. -/
theorem maxPartitionDefect_eq_singleton_of_noMerged
    (J : PairPinGraph B E) (hNo : NoMergedBodies J) :
    maxPartitionDefect J = singletonPartitionDefect J := by
  classical
  obtain ⟨π, hmax⟩ := maxPartitionDefect_attained J
  let t := (Finset.univ.image π).card
  obtain ⟨σ, hσ, hcap⟩ := normalize_partition_labelling J π
  have htpos : 0 < t := by
    exact Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hdimension := pairPin_defect_dimension J
  have hopt : 6 * (t - 1) - J.toBodyPinIncidence.partitionCapacity σ = genericRelativeDof J := by
    have hm := hmax
    rw [labelledPartitionDefect, ← hcap, partitionCapacity_eq_incidenceCapacity] at hm
    change 6 * ((t : ℤ) - 1) -
      (J.toBodyPinIncidence.partitionCapacity σ : ℤ) = maxPartitionDefect J at hm
    omega
  have hσinj := optimal_partition_injective J hNo σ hσ hopt
  let e : B ≃ Fin t := Equiv.ofBijective σ ⟨hσinj, hσ⟩
  have ht : t = Fintype.card B := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
  have hcapSingleton : partitionCapacity J σ =
      partitionCapacity J (Fintype.equivFin B) := by
    rw [partitionCapacity_eq_incidenceCapacity, partitionCapacity_eq_incidenceCapacity]
    change J.toBodyPinIncidence.capacityOn (e ∘ (id : B → B)) =
      J.toBodyPinIncidence.capacityOn ((Fintype.equivFin B) ∘ (id : B → B))
    exact (J.toBodyPinIncidence.capacityOn_comp_equiv e (id : B → B)).trans
      (J.toBodyPinIncidence.capacityOn_comp_equiv (Fintype.equivFin B) (id : B → B)).symm
  have hm : maxPartitionDefect J = 6 * ((t : ℤ) - 1) -
      (partitionCapacity J σ : ℤ) := by
    rw [← hmax, labelledPartitionDefect, hcap]
  rw [ht, hcapSingleton] at hm
  rw [hm, singletonPartitionDefect, labelledPartitionDefect]
  simp only [Finset.image_univ_of_surjective (Fintype.equivFin B).surjective,
    Finset.card_univ, Fintype.card_fin]

/-- In a simple loopless pin graph each actual unordered body pair carries
one occurrence, whose literal capacity is three. -/
theorem singletonCapacity_eq_three_card_of_simple
    (J : PairPinGraph B E) (hSimple : IsSimple J) :
    partitionCapacity J (Fintype.equivFin B) = 3 * Fintype.card E := by
  classical
  let H := J.toBodyPinIncidence
  rw [partitionCapacity_eq_incidenceCapacity]
  change H.capacityOn ((Fintype.equivFin B) ∘ (id : B → B)) = _
  have hcap : H.capacityOn ((Fintype.equivFin B) ∘ (id : B → B)) =
      H.capacityOn (id : B → B) :=
    H.capacityOn_comp_equiv (Fintype.equivFin B) (id : B → B)
  rw [hcap, H.capacityOn_eq_sum_actualPairs]
  have hpairs : H.actualPairs (id : B → B) =
      Finset.univ.image (fun e : E => s(J.left e, J.right e)) := by
    apply Finset.filter_eq_self.mpr
    intro b hb
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hb
    change ¬ (s(J.left e, J.right e)).IsDiag
    simpa only [Sym2.mk_isDiag_iff] using J.loopless e
  rw [hpairs, Finset.sum_image]
  · have hmult (e : E) : H.bundleMultiplicityOn (id : B → B) s(J.left e, J.right e) = 1 := by
      unfold RB31E2E.BodyPinIncidence.bundleMultiplicityOn
      change (Finset.univ.filter fun a : E => s(J.left a, J.right a) =
        s(J.left e, J.right e)).card = 1
      have hset : (Finset.univ.filter fun a : E => s(J.left a, J.right a) =
          s(J.left e, J.right e)) = {e} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          hSimple.eq_iff, Finset.mem_singleton]
      rw [hset]
      simp
    simp only [hmult, RB31E2E.pinCapacity_one, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.mul_comm]
  · intro a ha b hb hab
    exact hSimple hab

end

end Papers.Rigidity.PairPinGraph

namespace Papers.Rigidity

noncomputable section

/-- The singleton-optimality clause of Theorem 5.1, with the original
integer expression and generic real motion dimension. -/
theorem pairPin_singleton_partition_optimal
    {B E : Type} [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (hNo : J.NoMergedBodies) :
    (J.genericRelativeDof : ℤ) = J.singletonPartitionDefect :=
  (pairPin_defect_dimension J).trans
    (PairPinGraph.maxPartitionDefect_eq_singleton_of_noMerged J hNo)

/-- Every pin contributes all three independent coordinate rows in the
simple, unmerged case. -/
theorem pairPin_simple_genericPinRank
    {B E : Type} [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (hNo : J.NoMergedBodies) (hSimple : J.IsSimple) :
    J.genericPinRank = 3 * Fintype.card E := by
  have h := pairPin_singleton_partition_optimal J hNo
  have hcap := PairPinGraph.singletonCapacity_eq_three_card_of_simple J hSimple
  have hrank := PairPinGraph.genericPinRank_add_six_le J
  simp only [PairPinGraph.singletonPartitionDefect, PairPinGraph.labelledPartitionDefect,
    Finset.image_univ_of_surjective (Fintype.equivFin B).surjective,
    Finset.card_univ, Fintype.card_fin, hcap, PairPinGraph.genericRelativeDof] at h
  omega

/-- Literal linear independence, rather than a numerical substitute, of
the three occurrence-level rows at every maximum-rank real placement. -/
theorem pairPin_simple_pinRows_independent
    {B E : Type} [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (hNo : J.NoMergedBodies) (hSimple : J.IsSimple)
    (p : E → Vec3) (hp : J.pinRank p = J.genericPinRank) :
    LinearIndependent ℝ (J.pinRow p) := by
  apply (PairPinGraph.linearIndependent_pinRows_iff_pinRank J p).mpr
  exact hp.trans (pairPin_simple_genericPinRank J hNo hSimple)

/-- All three clauses of Theorem 5.1 in the original paper-facing target. -/
theorem pairPin_defect_theorem : PairPinDefectClaim := by
  intro B E _ _ _ J
  exact ⟨pairPin_defect_dimension J, fun hNo =>
    ⟨pairPin_singleton_partition_optimal J hNo, fun hs => pairPin_simple_genericPinRank J hNo hs⟩⟩

end

end Papers.Rigidity

end
end BundleSource0069

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0069/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0069.json"

section BundleSource0070
/- Source: Papers/RigidityPairPinAlgebraicGeneric.lean -/




@[expose] public section

/-!
# The defect theorem at ordinary algebraically generic real pins

The numerical generic rank was defined as an attained maximum. This
module connects it directly to the conventional meaning of generic
coordinates: algebraic independence of all three coordinates of every
original pin occurrence over the rationals. The conclusion concerns the
actual quotient of the actual real compatibility kernel by common
Euclidean twists.
-/

namespace Papers.Rigidity.PairPinGraph

noncomputable section

open RB31E2E.GroundedTwistPolynomial
open GenericPinIdeal

variable {B E : Type} [Fintype B] [Fintype E] [Nonempty B]

/-- Algebraically independent pin coordinates attain the maximum real
rank of the original occurrence-level compatibility operator. -/
theorem pinRank_eq_generic_of_algebraicIndependent
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) :
    pinRank J p = genericPinRank J := by
  classical
  obtain ⟨root⟩ := ‹Nonempty B›
  have hinj : Function.Injective
      (MvPolynomial.eval₂Hom (Rat.castHom ℝ) (assignmentOfPins p)) := by
    intro a b hab
    apply hp
    exact hab
  have h := PolynomialRank.realMatrix_rank_eq_generic_of_eval_injective
    (rationalMotionMatrix root J.left J.right) (assignmentOfPins p) hinj
  rw [realMatrix_rationalMotionMatrix, genericMatrix_rationalMotionMatrix,
    pinsOfAssignment_assignmentOfPins] at h
  rw [pinRank_eq_groundedMatrix_rank J root p,
    genericPinRank_eq_genericMotionMatrix_rank J root]
  exact h

/-- Theorem 5.1 in the conventional algebraically generic real-coordinate
form, with its quotient space and integer maximum both retained. -/
theorem relativeMotionSpace_finrank_eq_defect_of_algebraicIndependent
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) :
    (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = maxPartitionDefect J := by
  rw [← genericRelativeDof_eq_finrank_quotient J p
    (pinRank_eq_generic_of_algebraicIndependent J p hp)]
  exact pairPin_defect_dimension J

/-- In the simple, unmerged case the actual three coordinate rows per
pin are independent at every algebraically generic real placement. -/
theorem pinRows_independent_of_algebraicIndependent
    (J : PairPinGraph B E) (hNo : J.NoMergedBodies) (hSimple : J.IsSimple)
    (p : E → Vec3) (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) :
    LinearIndependent ℝ (J.pinRow p) :=
  pairPin_simple_pinRows_independent J hNo hSimple p
    (pinRank_eq_generic_of_algebraicIndependent J p hp)

/-- At the specified placement, no pair of distinct bodies has identical
twists in every actual compatible motion. This is the direct
configuration-level meaning of the paper's rigid-cluster hypothesis. -/
def NoMergedAt (J : PairPinGraph B E) (p : E → Vec3) : Prop :=
  ∀ u v : B, u ≠ v → ∃ X : B → Twist,
    X ∈ (compatibilityOperator J p).ker ∧ X u ≠ X v

theorem noMergedBodies_of_algebraicIndependent
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) (hNo : NoMergedAt J p) :
    NoMergedBodies J := by
  intro u v huv
  exact ⟨p, pinRank_eq_generic_of_algebraicIndependent J p hp, hNo u v huv⟩

/-- All three assertions of Theorem 5.1 stated directly at an ordinary
algebraically generic real pin configuration. The first dimension is
that of the literal quotient by common twists; the last conclusion is
linear independence of the literal occurrence-level rows. -/
theorem defect_theorem_at_algebraicallyGeneric_pins
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) :
    (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = maxPartitionDefect J ∧
      (NoMergedAt J p →
        (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = singletonPartitionDefect J ∧
          (IsSimple J → LinearIndependent ℝ (pinRow J p))) := by
  refine ⟨relativeMotionSpace_finrank_eq_defect_of_algebraicIndependent J p hp, ?_⟩
  intro hNo
  have hglobal := noMergedBodies_of_algebraicIndependent J p hp hNo
  constructor
  · rw [← genericRelativeDof_eq_finrank_quotient J p
      (pinRank_eq_generic_of_algebraicIndependent J p hp)]
    exact pairPin_singleton_partition_optimal J hglobal
  · intro hSimple
    exact pinRows_independent_of_algebraicIndependent J hglobal hSimple p hp

end

end Papers.Rigidity.PairPinGraph

end
end BundleSource0070

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0070/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0070.json"

section BundleSource0071
/- Source: Papers/RigidityAuditPairPin.lean -/



/-!
# Final pair-pin theorem statement and axiom audit

This file is a verification gate. It must finish under the pinned ordinary
Lean compiler before any of the displayed terms is reported as verified.
The source audit is complementary and is not a substitute for this gate.
-/

#check Papers.Rigidity.pairPin_defect_theorem
#check Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins

#print axioms Papers.Rigidity.pairPin_defect_theorem
#print axioms Papers.Rigidity.pairPin_defect_dimension
#print axioms Papers.Rigidity.pairPin_singleton_partition_optimal
#print axioms Papers.Rigidity.pairPin_simple_pinRows_independent
#print axioms Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins
#print axioms Papers.Rigidity.GenericPinIdeal.genericGroundedKernel_finrank_eq_partitionDefectMaximum
#print axioms Papers.Rigidity.QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse
#print axioms Papers.Rigidity.NullHeight.coefficientMinimalPrime_height_eq_edgeCard
#print axioms Papers.Rigidity.PairPinGraph.genericPinRank_eq_genericMotionMatrix_rank

end BundleSource0071

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0071/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0071.json"

section BundleSource0072
/- Source: Papers/RigidityPairPinMaximalRank.lean -/



@[expose] public section

/-!
# The pair-pin defect theorem at every maximum-rank real placement

The numerical generic rank is the attained maximum of the actual real
compatibility operator. Therefore its dimension formula applies to every
placement attaining that rank, without an algebraic-independence premise.
The optional no-merger hypothesis below is tested in the actual compatible
motion kernel at the specified placement.

-/

namespace Papers.Rigidity.PairPinGraph

noncomputable section

variable {B E : Type} [Fintype B] [Fintype E] [Nonempty B]

/-- Literal separation at any maximum-rank placement supplies the witnesses
in the placement-independent generic no-merger hypothesis. -/
theorem noMergedBodies_of_maximalRank
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : pinRank J p = genericPinRank J) (hNo : NoMergedAt J p) :
    NoMergedBodies J := by
  intro u v huv
  exact ⟨p, hp, hNo u v huv⟩

/-- Every maximum-rank real pin placement has the full integer partition
defect. Under literal no-merger at that placement, the singleton partition
is optimal and every coordinate pin row is independent when the graph is
simple. No algebraic-independence hypothesis is needed. -/
theorem defect_at_maximal_rank_pins
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : pinRank J p = genericPinRank J) :
    (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = maxPartitionDefect J ∧
      (NoMergedAt J p →
        (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = singletonPartitionDefect J ∧
          (IsSimple J → LinearIndependent ℝ (pinRow J p))) := by
  constructor
  · rw [← genericRelativeDof_eq_finrank_quotient J p hp]
    exact pairPin_defect_dimension J
  · intro hNo
    have hglobal := noMergedBodies_of_maximalRank J p hp hNo
    constructor
    · rw [← genericRelativeDof_eq_finrank_quotient J p hp]
      exact pairPin_singleton_partition_optimal J hglobal
    · intro hSimple
      exact pairPin_simple_pinRows_independent J hglobal hSimple p hp

end

end Papers.Rigidity.PairPinGraph

end
end BundleSource0072

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0072/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0072.json"

section BundleSource0073
/- Source: Papers/RigidityAuditMaximalRank.lean -/




/-!
This audit entry point is intended for the complete consolidated clean-build
closure, where all project proof bodies are present. It is not evidence of
verification until that build and the emitted audit both succeed.
-/

#check Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins
#print axioms Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins

#export_proof_audit Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins to ".lake/reports/audit/compiled_Papers_Rigidity_PairPinGraph_defect_at_maximal_rank_pins.json"

end BundleSource0073

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0073/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0073.json"

