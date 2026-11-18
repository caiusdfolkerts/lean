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

