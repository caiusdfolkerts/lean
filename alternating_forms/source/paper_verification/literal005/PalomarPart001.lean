module

public import paper_verification.literal005.PalomarPart000
import all paper_verification.literal005.PalomarPart000
public import paper_verification.literal004
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import paper_verification.literal000
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import paper_verification.literal001
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Lean.Elab.Tactic.Omega
public import paper_verification.literal003
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Sym.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Sym.Card
public import Mathlib.Order.Fin.Basic
import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Order.Zorn
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Sym
import paper_verification.literal000

set_option Elab.async false

section TAF_LiteralSource_0338
/- Original module: PaperVerification.AlternatingFormsSectionPrincipal -/


/-!
# Theorem 1.3 with the actual complete Plucker section rings

The older coordinate-ring statement is retained in full. The additional
clauses identify its literal original Proj with the actual common-isotropic
normalized atlas, identify the original graded coordinate ring with the
direct sum of its actual global twisting-sheaf sections, and state the
degeneration and Koszul clauses for that actual section algebra.

The section-ring multiplication was defined independently by multiplying
actual local sections. The displayed polynomial maps use the corresponding
actual coordinate sections. Their kernels are proved to be exactly the
previous original coordinate ideals. Ordinary Tor here is genuinely Tor
over these complete section algebras, computed by their actual bar or
projective resolutions with the original homogeneous degrees.

This is a full-scope assembly candidate, not a verification certificate.
Its complete canonical module closure and actual proof bodies remain to be
checked. Every positive plane dimension, the one-plane boundary, and the
maximal singleton interval are included.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial AlgebraicGeometry CategoryTheory
open PaperVerification.ProjectiveSectionRing
open PaperVerification.WeightedInitialFiber

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Flatness and both fibers, with the original nonzero fiber identified
with the separately defined actual complete section algebra. -/
def WeightedFlatDegenerationTo {σ τ : Type*}
    (Q : Ideal (MvPolynomial σ K)) (w : σ → ℕ)
    (J : Ideal (MvPolynomial τ K))
    (S : Type*) [CommRing S] [Algebra K S] : Prop :=
  Module.Flat (Polynomial K) (reesAlgebra Q w) ∧
  Nonempty (ZeroFiber Q w ≃ₐ[K] (MvPolynomial τ K⧸J)) ∧
  ∀ c : K,c≠0 → Nonempty (ParameterFiber Q w c ≃ₐ[K] S)

/-- The original good coordinates, as actual degree-one global sections. -/
def oddSectionGoodMap (k t : ℕ) (hs : t+2≤k+1) :
    MvPolynomial (Hibi.IntervalIndex (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs)) K →ₐ[K]
      SectionRing (oddProjectiveGrading (K := K) k t) :=
  (oddCompleteSectionRingEquiv (K := K) k t hs).toAlgHom.comp (oddGoodMap (K := K) k t hs)

theorem oddSectionGoodMap_surjective (k t : ℕ) (hs : t+2≤k+1) :
    Function.Surjective (oddSectionGoodMap (K := K) k t hs) :=
  (oddCompleteSectionRingEquiv (K := K) k t hs).surjective.comp (oddGoodMap_surjective k t hs)

theorem oddSectionGoodMap_kernel (k t : ℕ) (hs : t+2≤k+1) :
    RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom=
      oddGoodIdeal (K := K) k t hs := by
  ext p
  change oddCompleteSectionRingEquiv (K := K) k t hs (oddGoodMap (K := K) k t hs p)=0 ↔
    oddGoodMap (K := K) k t hs p=0
  exact (oddCompleteSectionRingEquiv (K := K) k t hs).map_eq_zero_iff

theorem oddSectionGoodMap_coordinate (k t : ℕ) (hs : t+2≤k+1)
    (I : Hibi.IntervalIndex (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs)) :
    oddSectionGoodMap (K := K) k t hs (X I)=
      DirectSum.of (fun d ↦ ↥(sectionPiece (oddProjectiveGrading (K := K) k t) d)) 1
        (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
          (rfl : (1 : ℤ)=1) ⊤
          ⟨oddGoodMap (K := K) k t hs (X I),odd_goodCoordinate_degree_one k t hs I⟩) :=
  oddCompleteSectionRingEquiv_homogeneous k t hs 1
    ⟨oddGoodMap (K := K) k t hs (X I),odd_goodCoordinate_degree_one k t hs I⟩

theorem oddSectionGoodMap_quadratic (k t : ℕ) (hs : t+2≤k+1) :
    HasQuadraticGroebnerBasis
      (RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom) := by
  rw [oddSectionGoodMap_kernel]
  exact (odd_higherPlane_conclusions k t hs).quadratic

theorem odd_section_richardson_flat (k t : ℕ) (hs : t+2≤k+1) :
    WeightedFlatDegenerationTo
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (intervalPluckerIdeal (oddIntervalLower k (t+2) hs)
        (oddIntervalUpper k (t+2) hs))
      (SectionRing (oddProjectiveGrading (K := K) k t)) :=
  ⟨(odd_richardson_flat_family k t hs).1,
    (odd_richardson_flat_family k t hs).2.1,
    fun c hc ↦ ⟨(oddRichardsonNonzeroFiberEquiv k t c hc).trans
      (oddCompleteSectionRingEquiv (K := K) k t hs)⟩⟩

/-- The actual one-plane coordinate sections. -/
def onePlaneSectionCoordinateMap (k : ℕ) :
    MvPolynomial (PluckerIndex 1 (2*k+1)) K →ₐ[K]
      SectionRing (onePlaneProjectiveGrading (K := K) k) :=
  (onePlaneCompleteSectionRingEquiv (K := K) k).toAlgHom.comp
    (Ideal.Quotient.mkₐ K matrixPluckerIdeal)

theorem onePlaneSectionCoordinateMap_surjective (k : ℕ) :
    Function.Surjective (onePlaneSectionCoordinateMap (K := K) k) :=
  (onePlaneCompleteSectionRingEquiv (K := K) k).surjective.comp Ideal.Quotient.mk_surjective

set_option maxHeartbeats 800000 in
theorem onePlaneSectionCoordinateMap_kernel (k : ℕ) :
    RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom=
      matrixPluckerIdeal := by
  change RingHom.ker
    ((onePlaneCompleteSectionRingEquiv (K := K) k).toRingHom.comp
      (Ideal.Quotient.mk matrixPluckerIdeal))=matrixPluckerIdeal
  exact (RingHom.ker_comp_of_injective (Ideal.Quotient.mk matrixPluckerIdeal)
    (onePlaneCompleteSectionRingEquiv (K := K) k).injective).trans Ideal.mk_ker

theorem onePlaneSectionCoordinateMap_quadratic (k : ℕ) :
    HasQuadraticGroebnerBasis
      (RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom) := by
  rw [onePlaneSectionCoordinateMap_kernel]
  exact (odd_onePlane_conclusions k).quadratic

theorem onePlane_section_richardson_flat (k : ℕ) :
    WeightedFlatDegenerationTo
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega)))
      (SectionRing (onePlaneProjectiveGrading (K := K) k)) :=
  ⟨(odd_onePlane_conclusions k).richardson.1,
    (odd_onePlane_conclusions k).richardson.2.1,
    fun c hc ↦ ⟨(nonzeroFiberEquiv _ _ c hc).trans
      (onePlaneCompleteSectionRingEquiv (K := K) k)⟩⟩

/-- The one-plane boundary, now including the actual complete section
algebra and its actual ordinary Tor in every internal degree. -/
structure OddOnePlaneSectionConclusions (k : ℕ) : Prop where
  original : OddOnePlaneConclusions (K := K) k
  complete : Nonempty
    (OnePlaneKoszul.Ring K (2*k+1) ≃ₐ[K]
      SectionRing (onePlaneProjectiveGrading (K := K) k))
  degree_comparison : ∀ d (r : onePlaneProjectiveGrading (K := K) k d),
    onePlaneCompleteSectionRingEquiv (K := K) k r=
      DirectSum.of (fun j ↦ ↥(sectionPiece (onePlaneProjectiveGrading (K := K) k) j)) d
        (Proj.toTwistingSheaf (onePlaneProjectiveGrading (K := K) k)
          (rfl : (d : ℤ)=d) ⊤ r)
  charts : ∀ p : PluckerIndex 1 (2*k+1),Nonempty
    ((Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
      (Ideal.Quotient.mk matrixPluckerIdeal (X p))).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K)))
  cover : (⨆ p : PluckerIndex 1 (2*k+1),
    Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
      (Ideal.Quotient.mk matrixPluckerIdeal (X p)))=⊤
  coordinates : Function.Surjective (onePlaneSectionCoordinateMap (K := K) k)
  coordinate_kernel : RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom=
    matrixPluckerIdeal
  quadratic : HasQuadraticGroebnerBasis
    (RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom)
  richardson : WeightedFlatDegenerationTo
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
    (SectionRing (onePlaneProjectiveGrading (K := K) k))
  tor_exhaustive : ∀ r,(⨆ N,OnePlaneSectionKoszul.torInternalPiece (K := K) k r N)=⊤
  koszul : ∀ r N,OnePlaneSectionKoszul.torInternalPiece (K := K) k r N=
    if N=r then ⊤ else ⊥

theorem odd_onePlane_section_conclusions (k : ℕ) :
    OddOnePlaneSectionConclusions (K := K) k :=
  ⟨odd_onePlane_conclusions k,⟨onePlaneCompleteSectionRingEquiv (K := K) k⟩,
    onePlaneCompleteSectionRingEquiv_homogeneous k,
    fun p ↦ ⟨onePlaneProjBasicOpenIso k p⟩,onePlaneProjBasicOpen_cover k,
    onePlaneSectionCoordinateMap_surjective k,onePlaneSectionCoordinateMap_kernel k,
    onePlaneSectionCoordinateMap_quadratic k,onePlane_section_richardson_flat k,
    OnePlaneSectionKoszul.torInternalPieces_iSup k,
    OnePlaneSectionKoszul.actual_section_Tor_internal_degree k⟩

/-- Every higher positive plane dimension, including the maximal singleton
interval, with the actual original scheme and actual complete section algebra. -/
structure OddHigherPlaneSectionConclusions (k t : ℕ) (hs : t+2≤k+1) : Prop where
  original : OddHigherPlaneConclusions (K := K) k t hs
  exact_equations : NormalizedHomogeneousProjOverlap.equationIdeal
    (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k))=
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
  same_scheme : Proj (NormalizedHomogeneousProjOverlap.grading
    (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k)))=
      Proj (oddProjectiveGrading (K := K) k t)
  charts : ∀ p : PluckerIndex (t+2) (2*k+1),Nonempty
    ((Proj.basicOpen (oddProjectiveGrading (K := K) k t)
      (Ideal.Quotient.mk (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) (X p))).toScheme ≅
      Spec (CommRingCat.of (IsotropicChartRing p (oddPluckerForms (K := K) k))))
  cover : (⨆ p : PluckerIndex (t+2) (2*k+1),
    Proj.basicOpen (oddProjectiveGrading (K := K) k t)
      (Ideal.Quotient.mk (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) (X p)))=⊤
  genuine_transitions : ∀ p q : PluckerIndex (t+2) (2*k+1),
    NormalizedHomogeneousProjOverlap.actualTransition
        (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k)) p q=
      (NormalizedHomogeneousChart.transitionHom
        (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k)) p q).toRingHom
  complete : Nonempty
    ((MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) ≃ₐ[K]
      SectionRing (oddProjectiveGrading (K := K) k t))
  degree_comparison : ∀ d (r : oddProjectiveGrading (K := K) k t d),
    oddCompleteSectionRingEquiv (K := K) k t hs r=
      DirectSum.of (fun j ↦ ↥(sectionPiece (oddProjectiveGrading (K := K) k t) j)) d
        (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
          (rfl : (d : ℤ)=d) ⊤ r)
  coordinates : Function.Surjective (oddSectionGoodMap (K := K) k t hs)
  coordinate_kernel : RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom=
    oddGoodIdeal (K := K) k t hs
  quadratic : HasQuadraticGroebnerBasis
    (RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom)
  richardson : WeightedFlatDegenerationTo
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms (K := K) k))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs))
    (SectionRing (oddProjectiveGrading (K := K) k t))
  residue_field : Nonempty
    (BarFree.Residue (oddSectionAugmentation (K := K) k t hs) ≃ₐ[K] K)
  tor_exhaustive : ∀ r,(⨆ N,oddSectionTorInternalPiece (K := K) k t hs r N)=⊤
  koszul : ∀ r N,oddSectionTorInternalPiece (K := K) k t hs r N=
    if N=r then ⊤ else ⊥

theorem odd_higherPlane_section_conclusions (k t : ℕ) (hs : t+2≤k+1) :
    OddHigherPlaneSectionConclusions (K := K) k t hs :=
  ⟨odd_higherPlane_conclusions k t hs,
    isotropicHomogeneousSystem_ideal_eq (oddPluckerForms (K := K) k),
    isotropicHomogeneousSystem_projectiveScheme_eq (oddPluckerForms (K := K) k),
    fun p ↦ ⟨isotropicProjBasicOpenIso p (oddPluckerForms (K := K) k)⟩,
    isotropicProjBasicOpen_cover (oddPluckerForms (K := K) k),
    NormalizedHomogeneousProjOverlap.actualTransition_eq_transitionHom _,
    ⟨oddCompleteSectionRingEquiv (K := K) k t hs⟩,
    oddCompleteSectionRingEquiv_homogeneous k t hs,
    oddSectionGoodMap_surjective k t hs,oddSectionGoodMap_kernel k t hs,
    oddSectionGoodMap_quadratic k t hs,odd_section_richardson_flat k t hs,
    ⟨oddSectionResidueEquivField k t hs⟩,
    oddSectionTorInternalPieces_iSup k t hs,oddSection_actual_Tor_internal_degree k t hs⟩

/-- The literal full positive plane range. The excluded zero-plane case
is false and is never used by the positive-range theorem. -/
def OddCompleteSectionConclusions (k s : ℕ) (hs : s≤k+1) : Prop :=
  match s,hs with
  | 0,_ => False
  | 1,_ => OddOnePlaneSectionConclusions (K := K) k
  | t+2,h => OddHigherPlaneSectionConclusions (K := K) k t h

theorem odd_all_positive_section_conclusions (k s : ℕ)
    (hpos : 0<s) (hs : s≤k+1) : OddCompleteSectionConclusions (K := K) k s hs := by
  cases s with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ s =>
    cases s with
    | zero => exact odd_onePlane_section_conclusions k
    | succ t => exact odd_higherPlane_section_conclusions k t hs

/-- The complete all-degree exterior-basis and all-positive-plane theorem,
with the literal complete section-ring form of every algebraic clause. -/
theorem paper_theorem_1_3_complete_section_ring (k : ℕ) :
    (∀ s,∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s
          (fun i ↦ Pi.basisFun K (Fin (2*k+1)) (I.val.val i)))) ∧
    (∀ s (hpos : 0<s) (hs : s≤k+1),OddCompleteSectionConclusions (K := K) k s hs) :=
  ⟨paper_theorem_1_3_exterior_basis k,odd_all_positive_section_conclusions k⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0338

section TAF_LiteralSource_0339
/- Original module: TauCeti.Data.Sym.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic lemmas for symmetric powers

This file records small API extensions for Mathlib's symmetric powers, and the map
`TauCeti.Sym.ofFn` reading an ordered `n`-tuple `f : Fin n → α` as an unordered one.

`ofFn` presents `Sym α n` as a quotient of `Fin n → α`: it is surjective, and its fibres are the
orbits of the permutation action, by `TauCeti.Sym.ofFn_eq_ofFn_iff`. Nothing here is topological;
`TauCeti/Topology/Sym/Basic.lean` uses this to give `Sym α n` the quotient topology coinduced along
`ofFn`.

## Main declarations

* `TauCeti.Sym.ofFn`: the ordered tuple `f : Fin n → α` read as a point of `Sym α n`, and
  `TauCeti.Sym.ofFn_surjective`, that every unordered tuple arises this way.
* `TauCeti.Sym.map_ofFn`, `TauCeti.Sym.map_comp_ofFn` and `TauCeti.Sym.ofFn_fin_append`: `ofFn`
  intertwines postcomposition with `Sym.map`, and concatenation of ordered tuples with
  `Sym.append`.
* `TauCeti.Sym.ofFn_eq_ofFn_iff`: two ordered tuples have the same underlying unordered tuple
  exactly when one is a reindexing of the other by a permutation.
* `TauCeti.Sym.count_coe_ofFn`: the multiplicity of a value in an unordered tuple is the number
  of entries of the ordered tuple taking that value.
* `TauCeti.Sym.basepointDivisor` is the set of unordered tuples containing a fixed point;
  `TauCeti.Sym.range_cons` identifies it with the range of adjoining that point.
* `TauCeti.symFinTwoEquiv`: an unordered `d`-tuple over `Fin 2` is determined by how many of its
  entries are `0`, so there are `d + 1` of them.
-/

public section

namespace Sym

variable {X Y : Type*} {d e : ℕ}

/-- Mapping a function over an appended symmetric-power point is the append of the mapped
symmetric-power points. -/
@[simp]
theorem map_append (f : X → Y) (s : Sym X d) (t : Sym X e) :
    Sym.map f (s.append t) = (Sym.map f s).append (Sym.map f t) :=
  Subtype.ext <| by simp [Multiset.map_add]

end Sym

namespace TauCeti

namespace Sym

variable {α β : Type*} {m n : ℕ}

/-! ### Ordered tuples as unordered ones -/

/-- The ordered `n`-tuple `f : Fin n → α` read as an unordered `n`-tuple.

This is Mathlib's quotient map `Sym.ofVector` precomposed with `List.Vector.ofFn`; the `Fin n → α`
form is the one that carries a product topology, so it is the map that `Sym α n` carries the
quotient topology along in `TauCeti/Topology/Sym/Basic.lean`. -/
def ofFn (f : Fin n → α) : Sym α n :=
  Sym.ofVector (List.Vector.ofFn f)

/-- The multiset underlying `ofFn f` is the list of values of `f`. -/
@[simp]
theorem coe_ofFn (f : Fin n → α) : (ofFn f : Multiset α) = ↑(List.ofFn f) :=
  congrArg _ (List.Vector.toList_ofFn f)

/-- The multiplicity of a value in `ofFn f` is the number of entries of `f` equal to it. -/
theorem count_coe_ofFn [DecidableEq α] (f : Fin n → α) (a : α) :
    Multiset.count a (ofFn f : Multiset α) = (Finset.univ.filter fun i => f i = a).card := by
  have hmap : (ofFn f : Multiset α) = Multiset.map f Finset.univ.val := by
    simp [List.ofFn_eq_map, Finset.val_univ_fin]
  rw [hmap, Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  simp only [eq_comm]

/-- The points of `ofFn f` are exactly the values of `f`. -/
@[simp]
theorem mem_ofFn {a : α} {f : Fin n → α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  rw [← _root_.Sym.mem_coe, coe_ofFn]
  simp

/-- Every unordered `n`-tuple is the image of an ordered one: `ofFn` is the quotient map
presenting `Sym α n` as a quotient of `Fin n → α`. -/
theorem ofFn_surjective : Function.Surjective (ofFn : (Fin n → α) → Sym α n) := by
  rintro ⟨s, hs⟩
  obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, s.coe_toList⟩
  have hlen : l.length = n := by simpa using hs
  subst hlen
  exact ⟨l.get, Subtype.ext (by simp)⟩

/-- Prepending a point to an ordered tuple adjoins it to the unordered one. -/
@[simp]
theorem ofFn_cons (a : α) (f : Fin n → α) : ofFn (Fin.cons a f) = a ::ₛ ofFn f :=
  Subtype.ext <| by simp [Sym.coe_cons, List.ofFn_succ]

/-- Applying a function to every entry of an ordered tuple applies it to every point of the
unordered one. -/
@[simp]
theorem map_ofFn (f : α → β) (g : Fin n → α) : Sym.map f (ofFn g) = ofFn (f ∘ g) :=
  Sym.coe_injective <| by simp [Sym.coe_map]

/-- The compatibility of `Sym.map` with `ofFn`, as an equality of maps out of ordered tuples. -/
theorem map_comp_ofFn (f : α → β) :
    (Sym.map f : Sym α n → Sym β n) ∘ ofFn = ofFn ∘ Pi.map fun _ : Fin n => f := by
  funext g
  simp only [Function.comp_apply, map_ofFn]
  exact congrArg ofFn (funext fun _ => rfl)

/-- The range of the map on symmetric powers consists of the unordered tuples whose every point
lies in the range of the original map. -/
theorem mem_range_map (f : α → β) {w : Sym β n} :
    w ∈ Set.range (Sym.map f) ↔ ∀ b ∈ w, b ∈ Set.range f := by
  constructor
  · rintro ⟨s, rfl⟩ b hb
    rw [← _root_.Sym.mem_coe, Sym.coe_map] at hb
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hb
    exact Set.mem_range_self a
  · intro hw
    let g : {b // b ∈ w} → α := fun b => (hw b b.2).choose
    have hg : ∀ b : {b // b ∈ w}, f (g b) = b := fun b => (hw b b.2).choose_spec
    refine ⟨Sym.map g w.attach, ?_⟩
    rw [Sym.map_map]
    convert w.attach_map_coe using 1
    exact congrArg (fun h => Sym.map h w.attach) (funext hg)

/-- Concatenating two ordered tuples adjoins the two unordered ones. -/
@[simp]
theorem ofFn_fin_append (f : Fin m → α) (g : Fin n → α) :
    ofFn (Fin.append f g) = (ofFn f).append (ofFn g) :=
  Sym.coe_injective <| by simp [Sym.coe_append, List.ofFn_fin_append]

/-! ### The fibres of the quotient map -/

/-- Reindexing an ordered tuple by a permutation leaves the underlying unordered tuple unchanged. -/
theorem ofFn_comp_perm (σ : Equiv.Perm (Fin n)) (f : Fin n → α) : ofFn (f ∘ σ) = ofFn f :=
  Sym.coe_injective <| by simpa using Multiset.coe_eq_coe.2 (σ.ofFn_comp_perm f)

/-- Two ordered tuples have the same underlying unordered tuple exactly when one is a reindexing
of the other: the fibres of `ofFn` are the orbits of the permutation action. -/
theorem ofFn_eq_ofFn_iff {f g : Fin n → α} :
    ofFn f = ofFn g ↔ ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · -- the two tuples take each value the same number of times, so their fibres are equinumerous
    have hcard : ∀ c : α, Fintype.card {i // g i = c} = Fintype.card {i // f i = c} := fun c => by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← count_coe_ofFn g c, ← count_coe_ofFn f c, h]
    exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
      funext fun i => Equiv.ofFiberEquiv_map _ i⟩
  · rintro ⟨σ, rfl⟩
    exact (ofFn_comp_perm σ f).symm

/-! ### Adjoining a fixed point -/

/-- The divisor of unordered tuples containing the fixed point `a`. -/
def basepointDivisor (a : α) : Set (Sym α n) := {s | a ∈ s}

@[simp]
theorem mem_basepointDivisor {a : α} {s : Sym α n} :
    s ∈ basepointDivisor a ↔ a ∈ s := Iff.rfl

/-- No unordered tuple of length zero contains a point. -/
@[simp]
theorem basepointDivisor_zero (a : α) : (basepointDivisor a : Set (Sym α 0)) = ∅ :=
  Set.eq_empty_of_forall_notMem fun s => by simp [_root_.Sym.eq_nil_of_card_zero s]

/-- The unordered `(n + 1)`-tuples obtained by adjoining the point `a` are exactly those that
contain `a`. -/
@[simp]
theorem range_cons (a : α) :
    Set.range (Sym.cons a : Sym α n → Sym α (n + 1)) = basepointDivisor a := by
  ext s
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨t, rfl⟩
    exact Sym.mem_cons_self a t
  · obtain ⟨t, rfl⟩ := Sym.exists_cons_of_mem hs
    exact ⟨t, rfl⟩

end Sym

/-! ### Unordered tuples over a two-element type -/

/-- **A multiset of size `d` over `Fin 2` is determined by how many of its entries are `0`**, and
that count can be anything from `0` to `d`: the two counts sum to `d`, so the pair of them runs
over the antidiagonal of `d`.  This is the rank-two instance of the count
`#(Sym α d) = (#α + d - 1).choose d`. -/
noncomputable def symFinTwoEquiv (d : ℕ) : Sym (Fin 2) d ≃ Fin (d + 1) :=
  (Sym.equivNatSumOfFintype (Fin 2) d).trans <|
    ((finTwoArrowEquiv ℕ).subtypeEquiv fun _ => by
      simp [Fin.sum_univ_two, Finset.mem_antidiagonal]).trans
        (Finset.Nat.antidiagonalEquivFin d)

/-- `TauCeti.symFinTwoEquiv` is the number of entries equal to `0`. -/
@[simp]
theorem coe_symFinTwoEquiv_apply (d : ℕ) (s : Sym (Fin 2) d) :
    (symFinTwoEquiv d s : ℕ) = Multiset.count 0 (s : Multiset (Fin 2)) := (rfl)

/-- The inverse of `TauCeti.symFinTwoEquiv` spelled out: `i` many `0`s and `d - i` many `1`s. -/
@[simp]
theorem coe_symFinTwoEquiv_symm_apply (d : ℕ) (i : Fin (d + 1)) :
    (((symFinTwoEquiv d).symm i : Sym (Fin 2) d) : Multiset (Fin 2))
      = Multiset.replicate (i : ℕ) 0 + Multiset.replicate (d - (i : ℕ)) 1 := by
  simp [symFinTwoEquiv, Fin.sum_univ_two, Multiset.nsmul_singleton]

end TauCeti
end
end TAF_LiteralSource_0339

section TAF_LiteralSource_0340
/- Original module: PaperVerification.AlternatingFormsTopInterlacing -/


/-!
# Interlacing and the symmetric-power indexing set in Corollary 5.2

The selected `a` indices are zero based.  If `c` enumerates the omitted
`b` indices, the inequalities are `cᵢ ≤ aᵢ < cᵢ₊₁`.  Subtracting `i`
from both kinds of entries gives the literal weak list in the paper.
The construction is an equivalence with unordered tuples, not a cardinality
assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TopInterlacing

def abIndex (k : ℕ) : Fin k ⊕ Fin (k+1) ≃ Fin (2*k+1) where
  toFun
    | .inl i => ⟨2*i.val+1, by have := i.isLt; omega⟩
    | .inr j => ⟨2*j.val, by have := j.isLt; omega⟩
  invFun j := if h : j.val%2=0 then .inr ⟨j.val/2, by have := j.isLt; omega⟩
    else .inl ⟨j.val/2, by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have h : ¬(2*i.val+1)%2=0 := by omega
        simp only [h, dite_false, Sum.inl.injEq]
        apply Fin.ext
        dsimp only
        omega
    | inr i =>
        have h : (2*i.val)%2=0 := by omega
        simp only [h, dite_true, Sum.inr.injEq]
        apply Fin.ext
        dsimp only
        omega
  right_inv i := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> dsimp only <;> omega

theorem strictMonoFin_lower {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f)
    (i : Fin m) : i.val ≤ (f i).val := by
  have h : ∀ r : ℕ, ∀ hr : r<m, r ≤ (f ⟨r,hr⟩).val := by
    intro r
    induction r with
    | zero => intro hr; exact Nat.zero_le _
    | succ r ih =>
        intro hr
        have hr' : r<m := by omega
        have hp := ih hr'
        have hs := hf (show (⟨r,hr'⟩ : Fin m) < ⟨r+1,hr⟩ from Nat.lt_succ_self r)
        change (f ⟨r,hr'⟩).val < (f ⟨r+1,hr⟩).val at hs
        omega
  exact h i.val i.isLt

theorem strictMonoFin_upper {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f)
    (i : Fin m) : (f i).val + m ≤ n+i.val := by
  have hr : StrictMono (fun j : Fin m => (f j.rev).rev) := by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (hf (Fin.rev_lt_rev.mpr hab))
  have h := strictMonoFin_lower _ hr i.rev
  simp only [Fin.val_rev, Fin.rev_rev] at h
  have hi := i.isLt
  have hf' := (f i).isLt
  omega

def Interlacing (p q : ℕ) :=
  {ac : (Fin p → Fin (p+q)) × (Fin (p+1) → Fin (p+q+1)) //
    StrictMono ac.1 ∧ StrictMono ac.2 ∧
      ∀ i : Fin p, (ac.2 i.castSucc).val ≤ (ac.1 i).val ∧
        (ac.1 i).val < (ac.2 i.succ).val}

def WeakWord (r q : ℕ) := {z : Fin r → Fin (q+1) // Monotone z}

instance (p q : ℕ) : Fintype (Interlacing p q) := by
  unfold Interlacing
  infer_instance
instance (r q : ℕ) : Fintype (WeakWord r q) := by
  unfold WeakWord
  infer_instance

def weakValue {p q : ℕ} (I : Interlacing p q) (j : Fin (2*p+1)) : ℕ :=
  if h : j.val%2=0 then
    (I.val.2 ⟨j.val/2, by have := j.isLt; omega⟩).val-j.val/2
  else (I.val.1 ⟨j.val/2, by have := j.isLt; omega⟩).val-j.val/2

theorem weakValue_le {p q : ℕ} (I : Interlacing p q) (j : Fin (2*p+1)) :
    weakValue I j ≤ q := by
  unfold weakValue
  split_ifs with hj
  · have h := strictMonoFin_upper I.val.2 I.property.2.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    have hl := strictMonoFin_lower I.val.2 I.property.2.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    dsimp only at h hl
    omega
  · have h := strictMonoFin_upper I.val.1 I.property.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    have hl := strictMonoFin_lower I.val.1 I.property.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    dsimp only at h hl
    omega

theorem weakValue_a {p q : ℕ} (I : Interlacing p q) (i : Fin p) :
    weakValue I (abIndex p (.inl i)) = (I.val.1 i).val-i.val := by
  have h : ¬(2*i.val+1)%2=0 := by omega
  have hd : (2*i.val+1)/2=i.val := by omega
  change weakValue I (⟨2*i.val+1, by have := i.isLt; omega⟩ : Fin (2*p+1)) = _
  simp only [weakValue, h, dite_false, hd]

theorem weakValue_c {p q : ℕ} (I : Interlacing p q) (i : Fin (p+1)) :
    weakValue I (abIndex p (.inr i)) = (I.val.2 i).val-i.val := by
  have h : (2*i.val)%2=0 := by omega
  have hd : (2*i.val)/2=i.val := by omega
  change weakValue I (⟨2*i.val, by have := i.isLt; omega⟩ : Fin (2*p+1)) = _
  simp only [weakValue, h, dite_true, hd]

theorem weakValue_monotone {p q : ℕ} (I : Interlacing p q) :
    Monotone (weakValue I) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  by_cases hj : j.val%2=0
  · let i : Fin p := ⟨j.val/2, by have := j.isLt; omega⟩
    have he : j.castSucc=abIndex p (.inr i.castSucc) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    have ho : j.succ=abIndex p (.inl i) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    rw [he, ho, weakValue_c, weakValue_a]
    exact Nat.sub_le_sub_right (I.property.2.2 i).1 _
  · let i : Fin p := ⟨j.val/2, by have := j.isLt; omega⟩
    have ho : j.castSucc=abIndex p (.inl i) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    have he : j.succ=abIndex p (.inr i.succ) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    rw [ho, he, weakValue_a, weakValue_c]
    have hi := (I.property.2.2 i).2
    have ha := strictMonoFin_lower I.val.1 I.property.1 i
    have hc := strictMonoFin_lower I.val.2 I.property.2.1 i.succ
    simp only [Fin.val_succ] at *
    omega

def toWeakWord {p q : ℕ} (I : Interlacing p q) : WeakWord (2*p+1) q :=
  ⟨fun j => ⟨weakValue I j, Nat.lt_succ_of_le (weakValue_le I j)⟩,
    fun i j hij => weakValue_monotone I hij⟩

def ofWeakWord {p q : ℕ} (z : WeakWord (2*p+1) q) : Interlacing p q :=
  ⟨(fun i => ⟨(z.val (abIndex p (.inl i))).val+i.val,
      by have := (z.val (abIndex p (.inl i))).isLt; have := i.isLt; omega⟩,
    fun i => ⟨(z.val (abIndex p (.inr i))).val+i.val,
      by have := (z.val (abIndex p (.inr i))).isLt; have := i.isLt; omega⟩), by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      have hz := z.property (show abIndex p (.inl i) ≤ abIndex p (.inl j) from by
        change 2*i.val+1≤2*j.val+1
        change i.val<j.val at hij
        omega)
      change (z.val (abIndex p (.inl i))).val ≤ (z.val (abIndex p (.inl j))).val at hz
      change i.val<j.val at hij
      change (z.val (abIndex p (.inl i))).val+i.val <
        (z.val (abIndex p (.inl j))).val+j.val
      omega
    · intro i j hij
      have hz := z.property (show abIndex p (.inr i) ≤ abIndex p (.inr j) from by
        change 2*i.val≤2*j.val
        change i.val<j.val at hij
        omega)
      change (z.val (abIndex p (.inr i))).val ≤ (z.val (abIndex p (.inr j))).val at hz
      change i.val<j.val at hij
      change (z.val (abIndex p (.inr i))).val+i.val <
        (z.val (abIndex p (.inr j))).val+j.val
      omega
    · intro i
      have hl := z.property (show abIndex p (.inr i.castSucc) ≤ abIndex p (.inl i) from by
        change 2*i.val≤2*i.val+1
        omega)
      have hr := z.property (show abIndex p (.inl i) ≤ abIndex p (.inr i.succ) from by
        change 2*i.val+1≤2*(i.val+1)
        omega)
      change (z.val (abIndex p (.inr i.castSucc))).val ≤
        (z.val (abIndex p (.inl i))).val at hl
      change (z.val (abIndex p (.inl i))).val ≤
        (z.val (abIndex p (.inr i.succ))).val at hr
      dsimp only
      simp only [Fin.val_castSucc, Fin.val_succ]
      constructor <;> omega⟩

def interlacingWeakEquiv (p q : ℕ) : Interlacing p q ≃ WeakWord (2*p+1) q where
  toFun := toWeakWord
  invFun := ofWeakWord
  left_inv I := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply Fin.ext
      change weakValue I (abIndex p (.inl i))+i.val=(I.val.1 i).val
      rw [weakValue_a, Nat.sub_add_cancel (strictMonoFin_lower _ I.property.1 i)]
    · funext i
      apply Fin.ext
      change weakValue I (abIndex p (.inr i))+i.val=(I.val.2 i).val
      rw [weakValue_c, Nat.sub_add_cancel (strictMonoFin_lower _ I.property.2.1 i)]
  right_inv z := by
    apply Subtype.ext
    funext j
    obtain ⟨j,rfl⟩ := (abIndex p).surjective j
    apply Fin.ext
    cases j with
    | inl i =>
        change weakValue (ofWeakWord z) (abIndex p (.inl i)) = _
        rw [weakValue_a]
        exact Nat.add_sub_cancel _ _
    | inr i =>
        change weakValue (ofWeakWord z) (abIndex p (.inr i)) = _
        rw [weakValue_c]
        exact Nat.add_sub_cancel _ _

theorem weakToSym_injective (r q : ℕ) :
    Function.Injective (fun z : WeakWord r q => TauCeti.Sym.ofFn z.val) := by
  intro z w h
  apply Subtype.ext
  apply List.ofFn_injective
  have hp : (List.ofFn z.val).Perm (List.ofFn w.val) := by
    apply Multiset.coe_eq_coe.mp
    simpa only [TauCeti.Sym.coe_ofFn] using
      congrArg (fun x : Sym (Fin (q+1)) r => (x : Multiset (Fin (q+1)))) h
  exact hp.eq_of_pairwise' z.property.sortedLE_ofFn.pairwise w.property.sortedLE_ofFn.pairwise

theorem weakToSym_surjective (r q : ℕ) :
    Function.Surjective (fun z : WeakWord r q => TauCeti.Sym.ofFn z.val) := by
  intro s
  let L := (s : Multiset (Fin (q+1))).sort
  have hl : L.length=r := by simp [L, s.property]
  let f : Fin r → Fin (q+1) := fun i => L[i.val]'(by rw [hl]; exact i.isLt)
  have hf : List.ofFn f=L := by
    apply List.ext_getElem
    · simp [hl]
    · intro i hi hi'
      simp [f]
  have hmono : Monotone f := by
    apply List.sortedLE_ofFn_iff.mp
    rw [hf]
    exact (Multiset.pairwise_sort _ _).sortedLE
  refine ⟨⟨f,hmono⟩, ?_⟩
  change TauCeti.Sym.ofFn f=s
  apply Sym.coe_injective
  rw [TauCeti.Sym.coe_ofFn, hf]
  exact Multiset.sort_eq _ _

def weakSymEquiv (r q : ℕ) : WeakWord r q ≃ Sym (Fin (q+1)) r :=
  Equiv.ofBijective (fun z => TauCeti.Sym.ofFn z.val)
    ⟨weakToSym_injective r q, weakToSym_surjective r q⟩

/-- The actual indexing equivalence underlying the plethysm in Corollary 5.2. -/
def interlacingSymEquiv (p q : ℕ) : Interlacing p q ≃ Sym (Fin (q+1)) (2*p+1) :=
  (interlacingWeakEquiv p q).trans (weakSymEquiv (2*p+1) q)

theorem interlacing_card (p q : ℕ) :
    Fintype.card (Interlacing p q) = (2*p+q+1).choose q := by
  rw [Fintype.card_congr (interlacingSymEquiv p q), Sym.card_sym_eq_multichoose,
    Fintype.card_fin, Nat.multichoose_eq]
  rw [show q+1+(2*p+1)-1=2*p+q+1 by omega]
  simpa only [show 2*p+q+1-q=2*p+1 by omega] using
    (Nat.choose_symm (show q≤2*p+q+1 by omega))

end PaperVerification.AlternatingForms.TopInterlacing
end
end
end TAF_LiteralSource_0340

section TAF_LiteralSource_0341
/- Original module: TauCeti.LinearAlgebra.SymmetricPower.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Functoriality of symmetric tensor powers, and the symmetrization back into the tensor power

This file equips Mathlib's symmetric tensor power with the linear map induced by a linear map of
the underlying modules. It proves the expected action on pure tensors, identity law, and composition
law. It also records that a symmetric power indexed by a finite type is finitely generated when its
underlying module is.

It then builds the map back, `SymmetricPower.toTensorPower : Sym[R] ι M →ₗ[R] ⨂[R] (_ : ι), M`,
for a finite index type. The **symmetrization** `∑_σ σ` of the tensor power is constant on the
fibres of the quotient map `SymmetricPower.mk`, because reindexing a pure tensor only permutes the
terms of that sum, so it descends to the symmetric power; `toTensorPower` is that descent. It is
the exact counterpart of Mathlib's `exteriorPower.toTensorPower`, and it takes a pure symmetric
tensor to the sum of the pure tensors over all orderings of its factors.

Composing back the other way multiplies by the order of the permutation group: `mk ∘ toTensorPower`
is `(card ι)!`, because each of the `(card ι)!` reorderings becomes the same symmetric tensor
again. So as soon as `(card ι)!` is a unit -- for instance over a `ℚ`-algebra -- the symmetrization
is injective, and it identifies the symmetric power with the image of the symmetrization operator
inside the tensor power. That is the statement a Young symmetrizer of a one-row shape consumes.

## Main definitions

* `SymmetricPower.map` is the map induced on a symmetric tensor power.
* `SymmetricPower.toTensorPower` is the symmetrization, from the symmetric power back into the
  tensor power.

## Main results

* `SymmetricPower.ext`: linear maps out of a symmetric power are determined by pure tensors.
* `LinearMap.apply_mem_of_forall_symmetricPower_tprod`: a linear map out of a symmetric power
  lands in a submodule once every pure tensor does.
* `SymmetricPower.toTensorPower_tprod`: the symmetrization of a pure symmetric tensor is the sum
  of the pure tensors over all orderings of its factors.
* `SymmetricPower.mk_comp_toTensorPower`: composing the symmetrization with the quotient map is
  multiplication by `(card ι)!`.
* `SymmetricPower.toTensorPower_injective`: the symmetrization is injective once `(card ι)!` is a
  unit.
* `SymmetricPower.range_toTensorPower`: its image is the image of the symmetrization operator on
  the tensor power.
* `SymmetricPower.toTensorPower_comp_map`: the symmetrization is natural in the module.

## References

The quotient construction of `SymmetricPower`, including `SymmetricPower.mk` and
`SymmetricPower.tprod`, is from Kenny Lau's
`Mathlib.LinearAlgebra.TensorPower.Symmetric`.
-/

public section

open scoped TensorProduct

universe u v

variable {R ι : Type u} {M : Type v}

namespace SymmetricPower

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]

/-- A linear map out of a symmetric power is determined by its values on pure symmetric
tensors. -/
@[ext]
theorem ext {N : Type*} [AddCommMonoid N] [Module R N] {g h : Sym[R] ι M →ₗ[R] N}
    (hgh : ∀ m : ι → M, g (⨂ₛ[R] i, m i) = h (⨂ₛ[R] i, m i)) : g = h := by
  refine LinearMap.ext_on (span_tprod_eq_top R ι M) ?_
  rintro _ ⟨m, rfl⟩
  exact hgh m

/-- A linear map sends every symmetric tensor into a submodule if it does so on pure tensors. -/
theorem _root_.LinearMap.apply_mem_of_forall_symmetricPower_tprod {N : Type*} [AddCommMonoid N]
    [Module R N] (f : Sym[R] ι M →ₗ[R] N) (p : Submodule R N)
    (h : ∀ m : ι → M, f (⨂ₛ[R] i, m i) ∈ p) (x : Sym[R] ι M) : f x ∈ p := by
  have hle : (⊤ : Submodule R (Sym[R] ι M)) ≤ p.comap f := by
    rw [← span_tprod_eq_top R ι M, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact h m
  exact hle Submodule.mem_top

theorem map_rel {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    addConGen (Rel R ι M) ≤
      AddCon.ker ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom) := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      apply (AddCon.ker_rel _).2
      simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        PiTensorProduct.map_tprod, tprod, LinearMap.compMultilinearMap_apply,
        Function.comp_apply] using (tprod_equiv (R := R) e (f ∘ m)).symm

/-- A linear map induces a linear map on every symmetric tensor power. -/
noncomputable def map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    Sym[R] ι M →ₗ[R] Sym[R] ι N where
  toFun :=
    (addConGen (Rel R ι M)).lift
      ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom)
      (map_rel f)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => by
    exact congrArg (mk R ι N) ((PiTensorProduct.map fun _ : ι => f).map_smul r x)

/-- The map on symmetric powers commutes with the quotient map from the tensor power. -/
@[simp]
theorem map_mk {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (x : ⨂[R] (_ : ι), M) :
    map f (mk R ι M x) = mk R ι N (PiTensorProduct.map (fun _ : ι => f) x) :=
  AddCon.lift_mk' (map_rel f) x

/-- The map induced on symmetric powers sends a pure tensor to the tensor of the images. -/
@[simp]
theorem map_tprod {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (m : ι → M) :
    map f (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, f (m i) := by
  simp only [tprod, LinearMap.compMultilinearMap_apply, map_mk,
    PiTensorProduct.map_tprod]

/-- The map induced by the identity is the identity on the symmetric power. -/
@[simp]
theorem map_id :
    map (ι := ι) (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  ext m
  simp

/-- Symmetric powers preserve composition of linear maps. -/
@[simp]
theorem map_comp {N : Type*} {P : Type*}
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map (ι := ι) (g.comp f) = (map (ι := ι) g).comp (map (ι := ι) f) := by
  ext m
  simp

/-- A symmetric power indexed by a finite type is finitely generated when the underlying module
is finitely generated. -/
noncomputable instance finite [Finite ι] [Module.Finite R M] : Module.Finite R (Sym[R] ι M) :=
  Module.Finite.of_surjective (mk R ι M)
    (LinearMap.range_eq_top.mp (range_mk R ι M))

end CommSemiring

/-! ### The symmetrization back into the tensor power -/

section Symmetrization

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

variable (R ι M) in
/-- The symmetrization operator `∑_σ σ` on the tensor power, permuting the tensor factors. -/
private noncomputable def symmetrizer : (⨂[R] (_ : ι), M) →ₗ[R] ⨂[R] (_ : ι), M :=
  ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap

private theorem symmetrizer_tprod (m : ι → M) :
    symmetrizer R ι M (⨂ₜ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [symmetrizer, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm ι)) _ _ fun σ => ?_
  simp

private theorem symmetrizer_rel :
    addConGen (Rel R ι M) ≤ AddCon.ker (symmetrizer R ι M).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, symmetrizer_tprod]
      refine Fintype.sum_bijective (e⁻¹ * ·) (Group.mulLeft_bijective _) _ _ fun σ => ?_
      congr 1
      funext i
      simp

variable (R ι M) in
/-- **The symmetrization**, from the symmetric power back into the tensor power: the descent of
the symmetrization operator `∑_σ σ` through the quotient map `SymmetricPower.mk`.

This is the counterpart of Mathlib's `exteriorPower.toTensorPower`. -/
noncomputable def toTensorPower : Sym[R] ι M →ₗ[R] ⨂[R] (_ : ι), M where
  toFun := (addConGen (Rel R ι M)).lift (symmetrizer R ι M).toAddMonoidHom symmetrizer_rel
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (symmetrizer R ι M).map_smul r x

private theorem toTensorPower_mk' (x : ⨂[R] (_ : ι), M) :
    toTensorPower R ι M (mk R ι M x) = (symmetrizer R ι M).toAddMonoidHom x :=
  (rfl)

@[simp]
theorem toTensorPower_mk (x : ⨂[R] (_ : ι), M) :
    toTensorPower R ι M (mk R ι M x) =
      ∑ σ : Equiv.Perm ι, PiTensorProduct.reindex R (fun _ : ι => M) σ x := by
  rw [toTensorPower_mk', LinearMap.toAddMonoidHom_coe, symmetrizer, LinearMap.sum_apply]
  rfl

/-- The symmetrization of a pure symmetric tensor is the sum of the pure tensors over all
orderings of its factors. -/
@[simp]
theorem toTensorPower_tprod (m : ι → M) :
    toTensorPower R ι M (⨂ₛ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [tprod, LinearMap.compMultilinearMap_apply, toTensorPower_mk']
  exact symmetrizer_tprod m

private theorem toTensorPower_comp_mk :
    (toTensorPower R ι M) ∘ₗ mk R ι M =
      ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, toTensorPower_mk, LinearMap.sum_apply]
    simp only [LinearEquiv.coe_coe]

/-- The image of the symmetrization is the image of the symmetrization operator `∑_σ σ` on the
tensor power. -/
theorem range_toTensorPower :
    LinearMap.range (toTensorPower R ι M) =
      LinearMap.range (∑ σ : Equiv.Perm ι,
        ((PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap)) := by
  rw [← toTensorPower_comp_mk, LinearMap.range_comp, range_mk, Submodule.map_top]

/-- Symmetrizing and then projecting back to the symmetric power multiplies by `(card ι)!`: the
`(card ι)!` reorderings of a pure tensor all become the same symmetric tensor. -/
@[simp]
theorem mk_comp_toTensorPower :
    (mk R ι M) ∘ₗ (toTensorPower R ι M) =
      (Fintype.card ι).factorial • LinearMap.id (R := R) (M := Sym[R] ι M) := by
  ext m
  have h (σ : Equiv.Perm ι) : mk R ι M (⨂ₜ[R] i, m (σ i)) = ⨂ₛ[R] i, m i :=
    tprod_equiv σ m
  simp [h, Fintype.card_perm]

/-- The symmetrization is injective as soon as `(card ι)!` is a unit in the base ring, for
instance over a `ℚ`-algebra. -/
theorem toTensorPower_injective (h : IsUnit ((Fintype.card ι).factorial : R)) :
    Function.Injective (toTensorPower R ι M) := by
  obtain ⟨u, hu⟩ := h
  -- Rescaling the quotient map by `u⁻¹` makes it a left inverse of the symmetrization.
  refine LinearMap.injective_of_comp_eq_id _ (((u⁻¹ : Rˣ) : R) • mk R ι M) ?_
  rw [LinearMap.smul_comp, mk_comp_toTensorPower, ← Nat.cast_smul_eq_nsmul R, smul_smul, ← hu,
    u.inv_mul, one_smul]

/-- The symmetrization is natural in the module. -/
theorem toTensorPower_comp_map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (toTensorPower R ι N) ∘ₗ (map (ι := ι) f) =
      (PiTensorProduct.map fun _ : ι => f) ∘ₗ (toTensorPower R ι M) := by
  ext m
  simp

end Symmetrization

end SymmetricPower
end
end TAF_LiteralSource_0341

section TAF_LiteralSource_0342
/- Original module: TauCeti.LinearAlgebra.SymmetricPower.Lift -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The universal property of the symmetric tensor power

A multilinear map `f : Mⁱ → N` that is unchanged by permuting its arguments factors uniquely
through the symmetric tensor power. This file builds that factorization,
`SymmetricPower.lift`, as the descent of `PiTensorProduct.lift f` through the quotient map
`SymmetricPower.mk`: the defining relation of the quotient identifies a pure tensor with each of
its reorderings, and `f` takes the same value on all of them.

Together with `SymmetricPower.ext`, which says that a linear map out of the symmetric power is
determined by its values on pure symmetric tensors, this says that composing with the pure
symmetric tensor `⨂ₛ` is a bijection from the linear maps `Sym[R] ι M →ₗ[R] N` onto the
permutation-invariant multilinear maps `Mⁱ → N`, for every `N`.

As a first use, prepending a fixed factor to a pure tensor is permutation-invariant in the remaining
factors, so it lifts to `SymmetricPower.consMul : M →ₗ[R] Sym[R]^k M →ₗ[R] Sym[R]^(k + 1) M`.
Since `Sym[R]^k M` is indexed by `Fin k`, this part takes the scalars in `Type`.

## Main definitions

* `SymmetricPower.lift`: the linear map on the symmetric power induced by a permutation-invariant
  multilinear map.
* `SymmetricPower.consMul`: multiplication of a symmetric tensor of degree `k` by one more
  factor, the lift of the pure tensor with that factor prepended.

## Main results

* `SymmetricPower.lift_tprod`: `lift f` agrees with `f` on pure symmetric tensors.
* `SymmetricPower.consMul_tprod` and `SymmetricPower.consMul_comm`: `consMul` prepends a factor
  to a pure tensor, and multiplications by two factors commute.
-/

public section

open scoped TensorProduct

universe u v w

variable {R ι : Type u} {M : Type v} {N : Type w}

namespace SymmetricPower

section Lift

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (f : MultilinearMap R (fun _ : ι ↦ M) N)

/-- A permutation-invariant multilinear map takes the same value on a pure tensor and on each of
its reorderings, so it is constant on the classes of the defining relation of the symmetric
power. -/
theorem lift_rel (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) :
    addConGen (Rel R ι M) ≤ AddCon.ker (PiTensorProduct.lift f).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.lift.tprod]
      exact (congrFun (congrArg DFunLike.coe (hf e)) m).symm

/-- **The universal property of the symmetric tensor power**: a multilinear map that is unchanged
by permuting its arguments descends to a linear map on the symmetric power. -/
noncomputable def lift (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) : Sym[R] ι M →ₗ[R] N where
  toFun := (addConGen (Rel R ι M)).lift (PiTensorProduct.lift f).toAddMonoidHom (lift_rel f hf)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (PiTensorProduct.lift f).map_smul r x

/-- The descent of a multilinear map commutes with the quotient map from the tensor power. -/
@[simp]
theorem lift_mk (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (x : ⨂[R] (_ : ι), M) :
    lift f hf (mk R ι M x) = PiTensorProduct.lift f x :=
  AddCon.lift_mk' (lift_rel f hf) x

/-- The descent of a multilinear map agrees with it on pure symmetric tensors. -/
@[simp]
theorem lift_tprod (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (m : ι → M) :
    lift f hf (⨂ₛ[R] i, m i) = f m := by
  rw [tprod, LinearMap.compMultilinearMap_apply, lift_mk, PiTensorProduct.lift.tprod]

end Lift

/-! ### Multiplication by one more factor -/

section ConsMul

variable {R : Type} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Prepending a fixed factor to a pure tensor is invariant under permutations of the remaining
factors. -/
theorem tprod_cons_perm_invariant (k : ℕ) (m : M) (e : Equiv.Perm (Fin k)) :
    ((tprod R (ι := Fin (k + 1)) (M := M)).curryLeft m).domDomCongr e =
      (tprod R).curryLeft m := by
  ext v
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.curryLeft_apply]
  rw [← tprod_equiv (Equiv.Perm.decomposeFin.symm (0, e)) (Fin.cons m v)]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp [Equiv.Perm.decomposeFin_symm_apply_zero]
  | succ i => simp [Equiv.Perm.decomposeFin_symm_apply_succ]

variable (R M) in
/-- Multiplying a symmetric tensor of degree `k` by one more factor, prepended to every pure
tensor. -/
noncomputable def consMul (k : ℕ) : M →ₗ[R] Sym[R]^k M →ₗ[R] Sym[R]^(k + 1) M where
  toFun m := lift ((tprod R).curryLeft m) (tprod_cons_perm_invariant k m)
  map_add' m m' := SymmetricPower.ext fun v ↦ by
    simp [lift_tprod]
  map_smul' c m := SymmetricPower.ext fun v ↦ by
    simp [lift_tprod]

/-- Multiplying a pure symmetric tensor by one more factor prepends that factor. -/
@[simp]
theorem consMul_tprod (k : ℕ) (m : M) (v : Fin k → M) :
    consMul R M k m (⨂ₛ[R] i, v i) = ⨂ₛ[R] i, (Fin.cons m v : Fin (k + 1) → M) i := by
  simp [consMul, lift_tprod]

/-- Multiplications of a symmetric tensor by two factors commute. -/
theorem consMul_comm (k : ℕ) (m m' : M) (x : Sym[R]^k M) :
    consMul R M (k + 1) m (consMul R M k m' x) = consMul R M (k + 1) m' (consMul R M k m x) := by
  suffices h : consMul R M (k + 1) m ∘ₗ consMul R M k m' =
      consMul R M (k + 1) m' ∘ₗ consMul R M k m from LinearMap.congr_fun h x
  refine SymmetricPower.ext fun v ↦ ?_
  simp only [LinearMap.comp_apply, consMul_tprod]
  rw [← tprod_equiv (Equiv.swap 0 1) (Fin.cons m (Fin.cons m' v))]
  exact congrArg (fun f : Fin (k + 2) → M ↦ ⨂ₛ[R] i, f i)
    (Matrix.cons_cons_comp_swap_zero_one m m' v)

end ConsMul

end SymmetricPower
end
end TAF_LiteralSource_0342

section TAF_LiteralSource_0343
/- Original module: TauCeti.LinearAlgebra.SymmetricPower.Basis -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# A basis of a symmetric tensor power

A basis `b : Basis κ R M` induces a basis of every symmetric tensor power `Sym[R]^n M`, indexed by
the **unordered** `n`-tuples `Sym κ n` of basis indices: the basis vector at `s` is the pure
symmetric tensor of the basis vectors listed by `s`. This is the symmetric counterpart of
`Basis.piTensorProduct`, whose index type is the ordered tuples `Fin n → κ`, and of
`Module.Basis.exteriorPower`, whose index type is the `n`-element subsets.

The coordinate map is built from the tensor-power basis: reading a pure tensor of basis vectors as
the unordered tuple of its indices is invariant under permuting the factors, so it descends to the
symmetric power by `SymmetricPower.lift`. Its inverse sends an unordered tuple to the pure
symmetric tensor of the corresponding basis vectors, which is well defined because any two
orderings of an unordered tuple differ by a permutation.

## Main definitions

* `SymmetricPower.tprodOfSym`: the pure symmetric tensor whose factors are listed, without order,
  by a point of `Sym κ n`.
* `Module.Basis.symmetricPower`: the induced basis of `Sym[R]^n M`.

## Main results

* `Module.Basis.map_symmetricPower_of_apply`: an endomorphism diagonal in a basis is
  diagonal in the induced basis of the symmetric power, with eigenvalue the product of the
  eigenvalues listed by the index.
* `SymmetricPower.finrank_eq`: the rank of `Sym[R]^n M` is `Nat.multichoose (finrank R M) n`.
* `Module.Basis.trace_map_symmetricPower_of_apply`: the trace on `Sym[R]^n M` of an endomorphism
  that is diagonal in a basis is the sum, over the unordered `n`-tuples of basis indices, of the
  product of the corresponding eigenvalues. This is the complete homogeneous symmetric polynomial
  in the eigenvalues, and is the symmetric counterpart of
  `Module.Basis.trace_map_exteriorPower_of_apply`.
-/

public section

open Module
open scoped TensorProduct

universe v w

variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}

namespace SymmetricPower

/-- A choice of ordering of an unordered tuple: an arbitrary section of `TauCeti.Sym.ofFn`, used
only to write down a pure symmetric tensor with prescribed factors. Any two orderings of the same
unordered tuple differ by a permutation, by `TauCeti.Sym.ofFn_eq_ofFn_iff`, so the choice never
escapes into the API below. -/
noncomputable def orderOfSym (s : Sym κ n) : Fin n → κ :=
  Function.surjInv TauCeti.Sym.ofFn_surjective s

theorem ofFn_orderOfSym (s : Sym κ n) : TauCeti.Sym.ofFn (orderOfSym s) = s :=
  Function.surjInv_eq TauCeti.Sym.ofFn_surjective s

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-! ### Pure symmetric tensors indexed by unordered tuples -/

variable (R) in
/-- The pure symmetric tensor whose factors are the members of a family `v : κ → M` listed, with
multiplicity but without order, by a point of `Sym κ n`. -/
noncomputable def tprodOfSym (v : κ → M) (s : Sym κ n) : Sym[R]^n M :=
  ⨂ₛ[R] i, v (orderOfSym s i)

/-- Reading off an ordered tuple of factors gives the pure symmetric tensor of those factors: the
choice of ordering hidden in the definition of `tprodOfSym` does not matter. -/
@[simp]
theorem tprodOfSym_ofFn (v : κ → M) (f : Fin n → κ) :
    tprodOfSym R v (TauCeti.Sym.ofFn f) = ⨂ₛ[R] i, v (f i) := by
  obtain ⟨σ, hσ⟩ := TauCeti.Sym.ofFn_eq_ofFn_iff.1 (ofFn_orderOfSym (TauCeti.Sym.ofFn f))
  conv_rhs => rw [← hσ]
  exact (tprod_equiv (R := R) σ fun i => v (orderOfSym (TauCeti.Sym.ofFn f) i)).symm

/-! ### The coordinate map in a basis -/

variable (b : Basis κ R M)

/-- Reading a pure tensor of basis vectors as the unordered tuple of its indices, on the tensor
power. -/
noncomputable def toFinsuppAux : (⨂[R] (_ : Fin n), M) →ₗ[R] (Sym κ n →₀ R) :=
  (Basis.piTensorProduct fun _ : Fin n => b).constr R
    fun f => Finsupp.single (TauCeti.Sym.ofFn f) 1

private theorem toFinsuppAux_tprod_basis (f : Fin n → κ) :
    toFinsuppAux b (⨂ₜ[R] i, b (f i)) = Finsupp.single (TauCeti.Sym.ofFn f) 1 := by
  rw [toFinsuppAux, ← Basis.piTensorProduct_apply, Basis.constr_basis]

/-- Permuting the factors of a pure tensor does not change the unordered tuple of its indices. -/
private theorem toFinsuppAux_reindex (e : Equiv.Perm (Fin n)) :
    (toFinsuppAux b) ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin n => M) e).toLinearMap =
      toFinsuppAux b := by
  refine (Basis.piTensorProduct fun _ : Fin n => b).ext fun f => ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.piTensorProduct_apply,
    PiTensorProduct.reindex_tprod, toFinsuppAux_tprod_basis b fun i => f (e.symm i),
    toFinsuppAux_tprod_basis b f]
  exact congrArg (Finsupp.single · (1 : R)) (TauCeti.Sym.ofFn_comp_perm e.symm f)

/-- The multilinear form of the coordinate map, before descending to the symmetric power. -/
noncomputable def toFinsuppMultilinear :
    MultilinearMap R (fun _ : Fin n ↦ M) (Sym κ n →₀ R) :=
  (toFinsuppAux b).compMultilinearMap (PiTensorProduct.tprod R)

theorem toFinsuppMultilinear_domDomCongr (e : Equiv.Perm (Fin n)) :
    (toFinsuppMultilinear b).domDomCongr e = toFinsuppMultilinear b := by
  refine MultilinearMap.ext fun m => ?_
  have h := congrFun (congrArg DFunLike.coe (toFinsuppAux_reindex b e.symm)) (⨂ₜ[R] i, m i)
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod] at h
  simpa [toFinsuppMultilinear] using h

variable (n) in
/-- The coordinates of a symmetric tensor in the basis induced by `b`: a pure tensor of basis
vectors is sent to the unordered tuple of its indices. -/
noncomputable def toFinsupp : Sym[R]^n M →ₗ[R] (Sym κ n →₀ R) :=
  lift (toFinsuppMultilinear b) (toFinsuppMultilinear_domDomCongr b)

theorem toFinsupp_tprod_basis (f : Fin n → κ) :
    toFinsupp n b (⨂ₛ[R] i, b (f i)) = Finsupp.single (TauCeti.Sym.ofFn f) 1 := by
  rw [toFinsupp, lift_tprod, toFinsuppMultilinear, LinearMap.compMultilinearMap_apply,
    toFinsuppAux_tprod_basis]

variable (n) in
/-- The symmetric power of a free module is free on the unordered `n`-tuples of basis indices. -/
noncomputable def linearEquivFinsupp : Sym[R]^n M ≃ₗ[R] (Sym κ n →₀ R) :=
  LinearEquiv.ofLinearMap (toFinsupp n b) (Finsupp.linearCombination R (tprodOfSym R b))
    (by
      refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply]
      rw [Finsupp.linearCombination_single, one_smul, ← ofFn_orderOfSym s, tprodOfSym_ofFn,
        toFinsupp_tprod_basis, ofFn_orderOfSym])
    (by
      apply (LinearMap.cancel_right (LinearMap.range_eq_top.1 (range_mk R (Fin n) M))).1
      refine (Basis.piTensorProduct fun _ : Fin n => b).ext fun f => ?_
      -- `⨂ₛ` is the quotient map applied to `⨂ₜ`.
      have hmk : mk R (Fin n) M (⨂ₜ[R] i, b (f i)) = ⨂ₛ[R] i, b (f i) := by
        rw [tprod, LinearMap.compMultilinearMap_apply]
      simp [hmk, toFinsupp_tprod_basis, tprodOfSym_ofFn])

private theorem linearEquivFinsupp_symm_single (s : Sym κ n) :
    (linearEquivFinsupp n b).symm (Finsupp.single s 1) = tprodOfSym R b s := by
  rw [linearEquivFinsupp, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    Finsupp.linearCombination_single, one_smul]

variable (n) in
/-- **A basis of the symmetric tensor power**: a basis of `M` induces a basis of `Sym[R]^n M`
indexed by the unordered `n`-tuples of basis indices. -/
noncomputable def _root_.Module.Basis.symmetricPower : Basis (Sym κ n) R (Sym[R]^n M) :=
  Basis.ofRepr (linearEquivFinsupp n b)

/-- The basis vector of `Sym[R]^n M` indexed by an unordered tuple `s : Sym κ n` of basis indices
is the pure symmetric tensor `SymmetricPower.tprodOfSym R b s` of the corresponding basis
vectors. -/
@[simp]
theorem _root_.Module.Basis.symmetricPower_apply (s : Sym κ n) :
    b.symmetricPower n s = tprodOfSym R b s :=
  linearEquivFinsupp_symm_single b s

/-- **An endomorphism diagonal in a basis is diagonal in the induced basis of the symmetric
power**: the basis vector indexed by `s` is an eigenvector, with eigenvalue the product of the
eigenvalues listed by `s`.  Summing these eigenvalues gives the trace,
`Module.Basis.trace_map_symmetricPower_of_apply`. -/
theorem _root_.Module.Basis.map_symmetricPower_of_apply (f : M →ₗ[R] M) (a : κ → R)
    (hf : ∀ i, f (b i) = a i • b i) (s : Sym κ n) :
    map (ι := Fin n) f (b.symmetricPower n s) =
      ((s : Multiset κ).map a).prod • b.symmetricPower n s := by
  obtain ⟨p, rfl⟩ := TauCeti.Sym.ofFn_surjective s
  simp [hf, (tprod R).map_smul_univ, List.prod_ofFn]

/-! ### Freeness and rank -/

/-- A symmetric power of a free module is free, on the unordered tuples of basis indices. -/
instance free [Module.Free R M] : Module.Free R (Sym[R]^n M) :=
  Module.Free.of_basis ((Module.Free.chooseBasis R M).symmetricPower n)

/-- The rank of a symmetric power of a finite free module: the number of unordered `n`-tuples of
basis indices, `Nat.multichoose (finrank R M) n`. -/
theorem finrank_eq [StrongRankCondition R] [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (Sym[R]^n M) = Nat.multichoose (Module.finrank R M) n := by
  classical
  rw [Module.finrank_eq_card_basis ((Module.Free.chooseBasis R M).symmetricPower n),
    Sym.card_sym_eq_multichoose, Module.finrank_eq_card_chooseBasisIndex]

/-! ### Traces -/

/-- If an endomorphism of a semimodule over a commutative semiring is diagonal in a finite basis,
then its trace on the `n`th symmetric power is the sum, over the unordered `n`-tuples of basis
indices, of the product of the corresponding eigenvalues. -/
theorem _root_.Module.Basis.trace_map_symmetricPower_of_apply [Fintype κ] [DecidableEq κ]
    (b : Basis κ R M) (f : M →ₗ[R] M) (a : κ → R) (n : ℕ) (hf : ∀ i, f (b i) = a i • b i) :
    LinearMap.trace R (Sym[R]^n M) (map (ι := Fin n) f) =
      ∑ s : Sym κ n, ((s : Multiset κ).map a).prod := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (b.symmetricPower n), Matrix.trace]
  simp_rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    Basis.map_symmetricPower_of_apply b f a hf]
  simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

end CommSemiring

end SymmetricPower
end
end TAF_LiteralSource_0343

section TAF_LiteralSource_0344
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.Standard -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The standard representation of the general linear group

This file defines the tautological representation of `GL n k` on column vectors, together with
its finite-dimensional and dual forms.  Its action and character are identified with matrix-vector
multiplication and the matrix trace.

## Main definitions

* `TauCeti.stdRep`: the standard representation of `GL n k`.
* `TauCeti.stdFDRep`: the standard representation as a finite-dimensional representation.
* `TauCeti.stdDualRep`: the contragredient of the standard representation.
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The standard representation of `GL n k` on column vectors. -/
def stdRep : Representation k (GL (Fin n) k) (Fin n → k) :=
  (Units.coeHom ((Fin n → k) →ₗ[k] (Fin n → k))).comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

/-- The standard representation acts by matrix-vector multiplication. -/
@[simp]
theorem stdRep_apply (g : GL (Fin n) k) :
    stdRep k n g = Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k) :=
  Matrix.GeneralLinearGroup.coe_toLin g

/-- Evaluation of the standard action is matrix-vector multiplication. -/
theorem stdRep_apply_apply (g : GL (Fin n) k) (v : Fin n → k) :
    stdRep k n g v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := by
  rw [stdRep_apply, Matrix.mulVecLin_apply]

/-- The standard representation is faithful. -/
theorem stdRep_injective : Function.Injective (stdRep k n) := by
  simpa [stdRep] using
    Units.coeHom_injective.comp Matrix.GeneralLinearGroup.toLin.injective

/-- The standard representation of `GL n k`, bundled as an object of `FDRep`. -/
noncomputable abbrev stdFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (stdRep k n)

end CommRing

section Field

variable [Field k]

/-- The character of the standard representation is the matrix trace. -/
@[simp]
theorem char_stdRep (g : GL (Fin n) k) :
    (stdRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  rw [Representation.character, stdRep_apply, ← Matrix.toLin'_apply']
  exact Matrix.trace_toLin'_eq (g : Matrix (Fin n) (Fin n) k)

/-- The character of the bundled standard representation is the matrix trace. -/
@[simp]
theorem char_stdFDRep (g : GL (Fin n) k) :
    (stdFDRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdRep k n g

end Field

section CommRing

variable [CommRing k]

/-- The dual, or contragredient, of the standard representation. -/
noncomputable def stdDualRep :
    Representation k (GL (Fin n) k) (Module.Dual k (Fin n → k)) :=
  (stdRep k n).dual

/-- The dual standard action is the transpose of the inverse standard action. -/
@[simp]
theorem stdDualRep_apply (g : GL (Fin n) k) :
    stdDualRep k n g =
      Module.Dual.transpose (R := k)
        (Matrix.mulVecLin ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
  rw [stdDualRep, Representation.dual_apply, stdRep_apply]

/-- The dual standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev stdDualFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (stdDualRep k n)

end CommRing

section Field

variable [Field k]

/-- The character of the dual standard representation is the trace at the inverse matrix. -/
@[simp]
theorem char_stdDualRep (g : GL (Fin n) k) : (stdDualRep k n).character g =
      Matrix.trace ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [stdDualRep, Representation.char_dual, char_stdRep]

/-- The character of the bundled dual standard representation is the inverse matrix trace. -/
@[simp]
theorem char_stdDualFDRep (g : GL (Fin n) k) : (stdDualFDRep k n).character g =
      Matrix.trace ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdDualRep k n g

end Field

end TauCeti
end
end TAF_LiteralSource_0344

section TAF_LiteralSource_0345
/- Original module: TauCeti.Algebra.Group.Torsion -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Commuting with nonzero powers in groups with unique roots

Commuting with a nonzero integer or natural power is equivalent to commuting with its base.
-/

public section

namespace Commute

variable {G : Type*} [Group G] [HasUniqueRoots G] {x y : G}

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_left_iff {n : ℤ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  constructor
  · intro h
    have hconj : y⁻¹ * x * y = x := by
      apply zpow_left_injective hn
      calc
        (y⁻¹ * x * y) ^ n = y⁻¹ * x ^ n * y := by
          simpa only [inv_inv] using (conj_zpow (a := y⁻¹) (b := x) (i := n))
        _ = x ^ n := h.symm.inv_mul_cancel
    exact calc
      x * y = y * (y⁻¹ * x * y) := by group
      _ = y * x := by rw [hconj]
  · intro h
    exact h.zpow_left n

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_right_iff {n : ℤ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x :=
  Commute.symm_iff.trans ((zpow_left_iff hn).trans Commute.symm_iff)

/-- In a group with unique roots, an element commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_left_iff {n : ℕ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using (zpow_left_iff (x := x) (y := y) hn')

/-- In a group with unique roots, an element commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_right_iff {n : ℕ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using (zpow_right_iff (x := x) (y := y) hn')

end Commute
end
end TAF_LiteralSource_0345

section TAF_LiteralSource_0346
/- Original module: TauCeti.Algebra.Group.Subgroup.Centralizer -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `Subgroup.centralizer` occurs in the statement below.
-- `Commute.units_val_iff` transports commutation between units and their values.
-- `Subgroup.zpowers` occurs in `Subgroup.zpowers_le_centralizer_singleton`.

/-!
# Centralizers and maximal commutative subgroups

Centralizers of a group of units are computed on the underlying monoid: a unit centralizes another
exactly when their values commute. Mathlib has both halves —
`Subgroup.mem_centralizer_singleton_iff` turns membership into an equation, and
`Commute.units_val_iff` transports that equation between `Mˣ` and `M` — but not their combination,
which is the form every concrete centralizer computation in a matrix group starts from.

## Main results

* `TauCeti.mem_centralizer_singleton_iff_commute_val`: a unit lies in the centralizer of a unit `g`
  exactly when the two commute as elements of the monoid.
* `Subgroup.zpowers_le_centralizer_singleton`: an element's cyclic subgroup lies in its
  centralizer.
* `Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative`: a self-centralizing subgroup is
  maximal among commutative subgroups.
* `Subgroup.exists_maximal_isMulCommutative`: every commutative subgroup lies in a maximal one.
* `Subgroup.centralizer_zpow_eq` and `Subgroup.centralizer_pow_eq`: nonzero powers have the same
  centralizer as their base in groups with unique roots.
-/

public section

namespace TauCeti

/-- Membership in the centralizer of a unit `g`, read on the underlying monoid. -/
theorem mem_centralizer_singleton_iff_commute_val {M : Type*} [Monoid M] {g h : Mˣ} :
    h ∈ Subgroup.centralizer {g} ↔ Commute (g : M) (h : M) :=
  ⟨fun hh => Commute.units_val_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hh).symm,
    fun hh => Subgroup.mem_centralizer_singleton_iff.mpr (Commute.units_val_iff.mp hh).symm⟩

end TauCeti

namespace Subgroup

/-- Every abelian subgroup is contained in a maximal abelian subgroup. -/
theorem exists_maximal_isMulCommutative {G : Type*} [Group G] (H : Subgroup G)
    (hH : IsMulCommutative H) :
    ∃ M : Subgroup G, H ≤ M ∧ Maximal (fun K : Subgroup G => IsMulCommutative K) M := by
  classical
  apply zorn_le_nonempty₀ {K : Subgroup G | IsMulCommutative K} ?_ H hH
  intro c hc hcc y hy
  have : ∀ K : c, IsMulCommutative (K : Subgroup G) := fun K => hc K.2
  have hcomm : IsMulCommutative (sSup c : Subgroup G) := by
    rw [sSup_eq_iSup']
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    exact Subgroup.isMulCommutative_iSup hcc.directedOn.directed_val
  exact ⟨sSup c, hcomm, fun K hK => le_sSup hK⟩

/-- The cyclic subgroup generated by an element lies in the centralizer of that element. -/
theorem zpowers_le_centralizer_singleton {G : Type*} [Group G] (x : G) :
    zpowers x ≤ centralizer {x} :=
  zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)

/-- A self-centralizing subgroup is maximal among commutative subgroups. -/
theorem eq_of_centralizer_eq_self_of_le_of_isMulCommutative {G : Type*} [Group G]
    {S H : Subgroup G} (hS : Subgroup.centralizer (S : Set G) = S) [IsMulCommutative H]
    (hle : S ≤ H) :
    H = S :=
  le_antisymm
    (by
      rw [← hS]
      exact (Subgroup.le_centralizer (H := H)).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)))
    hle

end Subgroup

namespace Subgroup

variable {G : Type*} [Group G] [HasUniqueRoots G] (x : G)

/-- Taking a nonzero integer power does not change the centralizer of an element in a group
with unique roots. -/
@[simp]
theorem centralizer_zpow_eq {n : ℤ} (hn : n ≠ 0) :
    centralizer {x ^ n} = centralizer {x} := by
  ext y
  simp only [mem_centralizer_singleton_iff, ← commute_iff_eq, Commute.zpow_right_iff hn]

/-- Taking a nonzero natural power does not change the centralizer of an element in a group
with unique roots. -/
@[simp]
theorem centralizer_pow_eq {n : ℕ} (hn : n ≠ 0) :
    centralizer {x ^ n} = centralizer {x} := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using centralizer_zpow_eq x hn'

end Subgroup
end
end TAF_LiteralSource_0346

section TAF_LiteralSource_0347
/- Original module: TauCeti.LinearAlgebra.Matrix.Diagonal -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Diagonal matrices: products with matrix units, and commutation

This file records generic identities about diagonal matrices. Multiplying a rectangular matrix
unit on both sides by diagonal matrices of the corresponding row and column sizes rescales its one
nonzero entry. And a matrix commuting with a diagonal matrix has no entry away from the diagonal
wherever that diagonal matrix separates two coordinates, so a matrix commuting with a diagonal
matrix of pairwise distinct entries is itself diagonal.

Neither statement needs a unit or an associative multiplication in the entries: the first holds
over a `NonUnitalNonAssocSemiring`, and the second adds commutativity and cancellation by nonzero
elements, which is what forces the off-diagonal entries to vanish.

For linear maps between based modules, the coordinate matrix is diagonal exactly when each source
basis vector maps to the corresponding scalar multiple of the target basis vector.

## Main results

* `TauCeti.diagonal_mul_single_mul_diagonal`: multiplying `Eᵢⱼ(c)` on the left and right by
  diagonal matrices rescales its entry by the corresponding diagonal coefficients.
* `TauCeti.isUnit_diagonal_iff`: a diagonal matrix over a possibly noncommutative semiring is a
  unit exactly when its diagonal is.
* `TauCeti.isUnit_diagonal_snoc_one_iff`: `diagonal (1, …, 1, x)` is a unit exactly when `x` is.
* `TauCeti.apply_eq_zero_of_commute_diagonal`: a matrix commuting with a diagonal matrix has
  vanishing `(i, j)` entry wherever that diagonal matrix separates `i` from `j`.
* `TauCeti.isDiag_of_commute_diagonal`: a matrix commuting with a diagonal matrix of pairwise
  distinct entries is itself diagonal.
* `Module.Basis.toMatrix_eq_diagonal_iff`: a linear map has a specified diagonal matrix in two
  bases exactly when it scales the corresponding basis vectors by the diagonal entries.
-/

public section

open Matrix

namespace TauCeti

variable {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
variable {A : Type*} [NonUnitalNonAssocSemiring A] {i : m} {j : n}

/-- Multiplying a matrix unit on the left and right by diagonal matrices rescales its nonzero
entry by the corresponding diagonal entries. -/
@[simp]
theorem diagonal_mul_single_mul_diagonal {v : m → A} {w : n → A} (c : A) :
    diagonal v * single i j c * diagonal w = single i j (v i * c * w j) := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

/-- A diagonal matrix is a unit exactly when its family of diagonal entries is. Unlike Mathlib's
`Matrix.isUnit_diagonal`, the entries need not commute. -/
theorem isUnit_diagonal_iff {R : Type*} [Semiring R] {v : n → R} :
    IsUnit (diagonal v) ↔ IsUnit v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map (diagonalRingHom n R)⟩
  obtain ⟨M, h₁, h₂⟩ := isUnit_iff_exists.1 h
  refine isUnit_iff_exists.2 ⟨fun i ↦ M i i, funext fun i ↦ ?_, funext fun i ↦ ?_⟩
  · simpa [diagonal_mul] using congr_fun₂ h₁ i i
  · simpa [mul_diagonal] using congr_fun₂ h₂ i i

/-- `diagonal (1, …, 1, x)` is a unit exactly when `x` is. -/
theorem isUnit_diagonal_snoc_one_iff {R : Type*} [Semiring R] {d : ℕ} (x : R) :
    IsUnit (diagonal (Fin.snoc (α := fun _ ↦ R) (1 : Fin d → R) x)) ↔ IsUnit x := by
  simp [isUnit_diagonal_iff, Pi.isUnit_iff, Fin.forall_fin_succ']

section Commute

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k : Type*} [NonUnitalNonAssocCommSemiring k] [IsLeftCancelMulZero k]

/-- A matrix commuting with a diagonal matrix has vanishing `(i, j)` entry whenever the diagonal
matrix separates the coordinates `i` and `j`. -/
theorem apply_eq_zero_of_commute_diagonal {t : ι → k} {g : Matrix ι ι k}
    (hg : Commute (Matrix.diagonal t) g) {i j : ι} (hij : t i ≠ t j) : g i j = 0 := by
  have hentry : (Matrix.diagonal t * g) i j = (g * Matrix.diagonal t) i j := by rw [hg.eq]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  -- `hentry : t i * g i j = g i j * t j`; cancelling `g i j` on the left would give `t i = t j`.
  by_contra h
  exact hij (mul_left_cancel₀ h (by rw [mul_comm (g i j) (t i)]; exact hentry))

/-- **A matrix commuting with a diagonal matrix of pairwise distinct entries is diagonal.** -/
theorem isDiag_of_commute_diagonal {t : ι → k} (ht : Function.Injective t)
    {g : Matrix ι ι k} (hg : Commute (Matrix.diagonal t) g) : g.IsDiag :=
  fun _ _ hij => apply_eq_zero_of_commute_diagonal hg (ht.ne hij)

end Commute

end TauCeti

namespace Module.Basis

/-- A linear map has a specified diagonal matrix in two bases exactly when it scales the
corresponding basis vectors by the diagonal entries. -/
@[simp]
theorem toMatrix_eq_diagonal_iff
    {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (f : M →ₗ[R] N) (c : ι → R) :
    LinearMap.toMatrix b b' f = Matrix.diagonal c ↔ ∀ i, f (b i) = c i • b' i := by
  rw [← (Matrix.toLin b b').injective.eq_iff, Matrix.toLin_toMatrix]
  constructor
  · intro h i
    simpa only [Matrix.toLin_self, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using congrArg (fun g : M →ₗ[R] N => g (b i)) h
  · intro hf
    apply b.ext
    intro i
    simpa only [Matrix.toLin_self, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hf i

end Module.Basis
end
end TAF_LiteralSource_0347

section TAF_LiteralSource_0348
/- Original module: TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `GL` and `Matrix.GeneralLinearGroup.det` occur in the statements below.
-- Permutation matrices provide the canonical normalizer action on diagonal matrices.
-- `MulEquiv.piUnits` identifies the units of a product with the product of the units, and is what
-- makes the diagonal embedding a homomorphism.
-- `Subgroup.centralizer` and its maximal-commutative-subgroup API occur below.
-- `Matrix.IsDiag` occurs in the statements below.
-- `Nat.card` occurs in the statement of `TauCeti.natCard_diagonalTorus`.
-- `Nat.card_units`, the number of units of a `GroupWithZero`.

/-!
# Diagonal elements of the general linear group, and the diagonal torus

A family of units indexed by a finite type `ι` is the diagonal of an invertible diagonal matrix,
and this assignment is an injective group homomorphism `TauCeti.diagGL : (ι → kˣ) →* GL ι k`.
Its entries, trace and determinant are recorded here, together with the fact that the diagonal
entries of an invertible diagonal matrix are units.

The image of `diagGL` is the **diagonal torus**

`TauCeti.diagonalTorus k n = (TauCeti.diagGL : (Fin n → kˣ) →* GL (Fin n) k).range`

of `GL n k`, for which three descriptions are given. As the range of an injective homomorphism
it is isomorphic to the coordinatewise units `Fin n → kˣ` (`TauCeti.diagonalTorusEquiv`), whence
its order `(q - 1)ⁿ` over a division semiring with `q` elements
(`TauCeti.natCard_diagonalTorus`). An invertible matrix lies in it exactly when it is diagonal
(`TauCeti.mem_diagonalTorus_iff`). And over a commutative semiring with cancellation by nonzero
elements and at least two units it is its own centralizer (`TauCeti.centralizer_diagonalTorus`),
hence a maximal abelian subgroup of `GL n k`.

The hypothesis that `kˣ` is nontrivial cannot be dropped: over a semiring with a single unit,
such as `𝔽₂`, the torus is trivial (`TauCeti.diagonalTorus_eq_bot`) while its centralizer is the
whole of `GL n k` (`TauCeti.centralizer_diagonalTorus_eq_top`).

A scalar matrix is central in `GL ι k` over any commutative semiring
(`TauCeti.scalar_mem_center`), and `diagGL` sends a constant family to the corresponding scalar
element (`TauCeti.diagGL_const`).

## Main definitions

* `TauCeti.diagGL` embeds a family of units as an invertible diagonal matrix.
* `TauCeti.diagonalTorus`: the subgroup of invertible diagonal matrices in `GL n k`.
* `TauCeti.diagonalTorusEquiv`: the identification `(Fin n → kˣ) ≃* diagonalTorus k n`.
* `TauCeti.detOneRescale`: the explicit rescaling of the first column of an invertible matrix
  that makes its determinant one.

## Main statements

* `TauCeti.isUnit_apply_of_isDiag`: the diagonal entries of an invertible diagonal matrix are
  units.
* `TauCeti.coe_inv_of_coe_eq_diagonal`: over a division ring, the inverse of an invertible
  diagonal matrix is the diagonal matrix of the inverse entries.
* `TauCeti.exists_det_eq_one_mul_map_eq_map_mul_diagGL`: a matrix intertwining another matrix with
  a diagonal matrix can be normalized to have determinant one while preserving the equation.
* `TauCeti.mem_diagonalTorus_iff`: membership in the torus is diagonality of the matrix.
* `TauCeti.mul_diagGL_of_coe_eq_permMatrix`: a permutation matrix moves past a diagonal by
  relabelling its entries.
* `TauCeti.natCard_diagonalTorus`: the torus has `(q - 1)ⁿ` elements over a division semiring
  with `q` elements.
* `TauCeti.centralizer_diagonalTorus`: the diagonal torus is its own centralizer.
* `TauCeti.mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL` and
  `TauCeti.mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL`: inside any subgroup, an element
  centralizes a family of diagonal elements exactly when its entries vanish between the
  coordinates the family separates; for a family separating all coordinates, exactly when it is
  diagonal.
* `TauCeti.centralizer_diagonalTorus_eq_top`: over a semiring with a single unit the centralizer
  is instead the whole group.
* `TauCeti.scalar_mem_center` and `TauCeti.centralizer_scalar`: a scalar matrix is central, so its
  centralizer is the whole group.
* `TauCeti.diagGL_const` and `TauCeti.notMem_range_scalar_diagGL`: the diagonal embedding sends a
  constant family to the corresponding scalar element, and it is scalar *only* there.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

section Semiring

variable [Semiring k]

/-- Coordinatewise units embed in a general linear group as diagonal matrices. -/
def diagGL : (ι → kˣ) →* GL ι k :=
  (Units.map (Matrix.diagonalRingHom ι k).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

/-- The matrix underlying `diagGL t` is the diagonal matrix with entries `t i`. -/
@[simp]
theorem diagGL_coe (t : ι → kˣ) :
    (diagGL t : Matrix ι ι k) = Matrix.diagonal fun i => (t i : k) := by
  rfl

/-- The entries of `diagGL t` vanish off the diagonal and equal `t i` on it. -/
@[simp]
theorem diagGL_apply (t : ι → kˣ) (i j : ι) :
    diagGL t i j = if i = j then (t i : k) else 0 := by
  rw [diagGL_coe, Matrix.diagonal_apply]

/-- The trace of a diagonal element of the general linear group is the sum of its diagonal
entries. -/
theorem trace_diagGL (t : ι → kˣ) :
    (diagGL t : Matrix ι ι k).trace = ∑ i, (t i : k) := by
  rw [diagGL_coe, Matrix.trace_diagonal]

/-- The diagonal embedding is injective. -/
theorem diagGL_injective : Function.Injective (diagGL (k := k) (ι := ι)) := fun t s h =>
  funext fun i => Units.ext <| by
    simpa using congrArg (fun g : GL ι k ↦ (g : Matrix ι ι k) i i) h

/-- **A constant family of units embeds as the corresponding scalar element** of the general linear
group. Together with `TauCeti.notMem_range_scalar_diagGL` this says that the diagonal embedding is
scalar exactly on the constant families. -/
@[simp]
theorem diagGL_const (a : kˣ) :
    diagGL (fun _ : ι => a) = Matrix.GeneralLinearGroup.scalar ι a :=
  Units.ext <| by rw [diagGL_coe, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

/-- An invertible diagonal matrix with two distinct diagonal entries is not scalar. -/
theorem notMem_range_scalar_diagGL {t : ι → kˣ} {i j : ι} (ht : t i ≠ t j) :
    (diagGL t : Matrix ι ι k) ∉ Set.range (Matrix.scalar ι) := by
  rintro ⟨c, hc⟩
  refine ht (Units.ext ?_)
  have hi : c = (t i : k) := by simpa using congrFun (congrFun hc i) i
  have hj : c = (t j : k) := by simpa using congrFun (congrFun hc j) j
  rw [← hi, ← hj]

/-- A general-linear element whose underlying matrix is the permutation matrix of `π` moves
past a diagonal matrix by relabelling its diagonal entries along `π`. -/
theorem mul_diagGL_of_coe_eq_permMatrix
    (g : GL ι k) (π : Equiv.Perm ι) (hg : (g : Matrix ι ι k) = π.permMatrix k)
    (d : ι → kˣ) :
    g * diagGL d = diagGL (d ∘ π) * g := by
  ext i j
  simp only [Units.val_mul, diagGL_coe, hg, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, Matrix.diagonal_apply]
  grind

/-- The diagonal entries of an invertible diagonal matrix are units. Unlike Mathlib's
`Matrix.isUnit_diagonal`, this assumes no commutativity of `k`. -/
theorem isUnit_apply_of_isDiag {g : GL ι k} (hg : (g : Matrix ι ι k).IsDiag) (i : ι) :
    IsUnit ((g : Matrix ι ι k) i i) := by
  have h₁ := congrFun (congrFun g.mul_inv i) i
  have h₂ := congrFun (congrFun g.inv_mul i) i
  rw [← hg.diagonal_diag, Matrix.diagonal_mul, Matrix.one_apply_eq] at h₁
  rw [← hg.diagonal_diag, Matrix.mul_diagonal, Matrix.one_apply_eq] at h₂
  exact ⟨⟨_, _, h₁, h₂⟩, rfl⟩

/-- The **diagonal torus** of `GL n k`: the image of the coordinatewise units under `diagGL`. -/
def diagonalTorus (k : Type u) [Semiring k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  MonoidHom.range (diagGL (k := k) (ι := Fin n))

/-- Membership in the diagonal torus, read off its definition as a range: an element lies in it
exactly when it is `diagGL t` for a family of units `t`. -/
theorem mem_diagonalTorus_iff_exists_diagGL {g : GL (Fin n) k} :
    g ∈ diagonalTorus k n ↔ ∃ t : Fin n → kˣ, diagGL t = g :=
  MonoidHom.mem_range

/-- An invertible matrix lies in the diagonal torus exactly when it is a diagonal matrix. -/
@[simp]
theorem mem_diagonalTorus_iff {g : GL (Fin n) k} :
    g ∈ diagonalTorus k n ↔ (g : Matrix (Fin n) (Fin n) k).IsDiag := by
  refine ⟨?_, fun hg => ⟨fun i => (isUnit_apply_of_isDiag hg i).unit, Units.ext ?_⟩⟩
  · rintro ⟨t, rfl⟩
    rw [diagGL_coe]
    exact Matrix.isDiag_diagonal _
  · rw [diagGL_coe]
    simp only [IsUnit.unit_spec]
    exact hg.diagonal_diag

/-- The diagonal torus is the group of coordinatewise units. -/
noncomputable def diagonalTorusEquiv (k : Type u) [Semiring k] (n : ℕ) :
    (Fin n → kˣ) ≃* diagonalTorus k n :=
  MonoidHom.ofInjective diagGL_injective

/-- The torus element attached to a family of units is `diagGL t`. -/
@[simp]
theorem coe_diagonalTorusEquiv_apply (t : Fin n → kˣ) :
    ((diagonalTorusEquiv k n t : diagonalTorus k n) : GL (Fin n) k) = diagGL t :=
  MonoidHom.ofInjective_apply diagGL_injective

/-- The `i`-th coordinate character of a torus element is its `(i, i)` matrix entry. -/
@[simp]
theorem coe_diagonalTorusEquiv_symm_apply (g : diagonalTorus k n) (i : Fin n) :
    (((diagonalTorusEquiv k n).symm g i : kˣ) : k) =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i := by
  have h : diagGL ((diagonalTorusEquiv k n).symm g) = (g : GL (Fin n) k) :=
    MonoidHom.apply_ofInjective_symm diagGL_injective g
  conv_rhs => rw [← h, diagGL_coe]
  rw [Matrix.diagonal_apply_eq]

/-- **The order of the diagonal torus**: over a division semiring with `q` elements it has
`(q - 1)ⁿ` elements, one invertible scalar per diagonal entry. Over an infinite division semiring
both sides vanish when `n > 0`. -/
theorem natCard_diagonalTorus (k : Type u) [DivisionSemiring k] (n : ℕ) :
    Nat.card (diagonalTorus k n) = (Nat.card k - 1) ^ n := by
  rw [← Nat.card_congr (diagonalTorusEquiv k n).toEquiv, Nat.card_fun, Nat.card_units,
    Nat.card_fin]

/-- An element centralizing the diagonal torus commutes, as a matrix, with every diagonal matrix
of units. -/
theorem commute_diagonal_of_mem_centralizer {g : GL (Fin n) k}
    (hg : g ∈ Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k))) (t : Fin n → kˣ) :
    Commute (Matrix.diagonal fun i => (t i : k)) (g : Matrix (Fin n) (Fin n) k) := by
  have h := congrArg Units.val <|
    Subgroup.mem_centralizer_iff.mp hg _ (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨t, rfl⟩)
  rwa [Units.val_mul, Units.val_mul, diagGL_coe] at h

section Subsingleton

variable [Subsingleton kˣ]

/-- Over a semiring with only one unit, such as `𝔽₂`, the diagonal torus is trivial. -/
theorem diagonalTorus_eq_bot : diagonalTorus k n = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro - ⟨t, rfl⟩
  rw [Subgroup.mem_bot, Subsingleton.elim t 1, map_one]

/-- Over a semiring with only one unit the centralizer of the diagonal torus is the whole group,
while the torus itself is trivial by `TauCeti.diagonalTorus_eq_bot`. So the hypothesis
`Nontrivial kˣ` of `TauCeti.centralizer_diagonalTorus` cannot simply be dropped: the two
subgroups differ as soon as `GL n k` is nontrivial, as it is over `𝔽₂` for `n ≥ 2`. -/
theorem centralizer_diagonalTorus_eq_top :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = ⊤ := by
  simp [diagonalTorus_eq_bot, Subgroup.centralizer_eq_top_iff_subset]

end Subsingleton

end Semiring

section CommSemiring

variable [CommSemiring k]

/-- The diagonal torus is commutative. -/
instance instIsMulCommutativeDiagonalTorus : IsMulCommutative (diagonalTorus k n) :=
  Subgroup.range_isMulCommutative _

section Scalar

/-- **A scalar matrix is central in `GL ι k`**. Mathlib's
`Matrix.GeneralLinearGroup.scalar_commute` asks for a commutative ring. -/
theorem scalar_mem_center (u : kˣ) :
    Matrix.GeneralLinearGroup.scalar ι u ∈ Subgroup.center (GL ι k) :=
  Subgroup.mem_center_iff.mpr fun g => Units.ext
    ((Matrix.scalar_commute (u : k) (fun _ => Commute.all _ _) (g : Matrix ι ι k)).symm.eq)

/-- **The centralizer of a scalar matrix is everything**, scalar matrices being central. The size of
its conjugacy class is `TauCeti.ncard_carrier_mk_scalar`, in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer`. -/
@[simp]
theorem centralizer_scalar (u : kˣ) :
    Subgroup.centralizer {Matrix.GeneralLinearGroup.scalar ι u} = ⊤ :=
  Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr (scalar_mem_center u))

end Scalar

section IsLeftCancelMulZero

variable [IsLeftCancelMulZero k] [Nontrivial kˣ]

/-- **The diagonal torus is its own centralizer**, hence a maximal abelian subgroup of `GL n k`. -/
theorem centralizer_diagonalTorus :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = diagonalTorus k n := by
  refine le_antisymm (fun g hg => mem_diagonalTorus_iff.mpr fun i j hij => ?_)
    (Subgroup.le_centralizer _)
  obtain ⟨u, v, huv⟩ := exists_pair_ne kˣ
  refine apply_eq_zero_of_commute_diagonal
    (commute_diagonal_of_mem_centralizer hg fun m => if m = i then u else v) ?_
  rw [ite_eq_left rfl, ite_eq_right (Ne.symm hij)]
  exact fun h => huv (Units.ext h)

/-- A commutative subgroup of `GL n k` containing the diagonal torus equals it: this is the
maximality of the torus among abelian subgroups. -/
theorem eq_diagonalTorus_of_le_of_isMulCommutative (H : Subgroup (GL (Fin n) k))
    [IsMulCommutative H] (hle : diagonalTorus k n ≤ H) :
    H = diagonalTorus k n :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative centralizer_diagonalTorus hle

end IsLeftCancelMulZero

section FamilyCentralizer

variable [IsLeftCancelMulZero k] {X : Type*} {P : Subgroup (GL ι k)} {T : X → P}
  {f : X → ι → kˣ}

/-- **The centralizer of a family of diagonal elements.** Suppose `T` sends each `x` to an element
of a subgroup `P` of `GL ι k` whose matrix is diagonal with entries `f x`. An element of `P`
commutes with every `T x` exactly when its `(i, j)` entry vanishes whenever some `f x` takes
different values at `i` and `j`. -/
theorem mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL
    (hT : ∀ x, (T x : GL ι k) = diagGL (f x)) (g : P) :
    g ∈ Subgroup.centralizer (Set.range T) ↔
      ∀ i j, (∃ x, f x i ≠ f x j) → ((g : GL ι k) : Matrix ι ι k) i j = 0 := by
  constructor
  · rintro hg i j ⟨x, hx⟩
    have hcomm := congrArg (fun y : P ↦ ((y : GL ι k) : Matrix ι ι k))
      (Subgroup.mem_centralizer_iff.mp hg (T x) ⟨x, rfl⟩)
    simp only [Subgroup.coe_mul, Units.val_mul, hT, diagGL_coe] at hcomm
    exact apply_eq_zero_of_commute_diagonal hcomm fun h ↦ hx (Units.ext h)
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hT, diagGL_coe]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : f x i = f x j
    · rw [hij, mul_comm]
    · rw [hg i j ⟨x, hij⟩, mul_zero, zero_mul]

/-- **An element centralizing a separating family of diagonal elements is diagonal.** If every
pair of distinct coordinates is separated by some `f x`, an element of `P` commutes with every
`T x` exactly when its matrix is diagonal. -/
theorem mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL
    (hT : ∀ x, (T x : GL ι k) = diagGL (f x))
    (hf : Pairwise fun i j ↦ ∃ x, f x i ≠ f x j) (g : P) :
    g ∈ Subgroup.centralizer (Set.range T) ↔ ((g : GL ι k) : Matrix ι ι k).IsDiag := by
  rw [mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL hT]
  refine ⟨fun h i j hij ↦ h i j (hf hij), fun h i j ⟨x, hx⟩ ↦ h ?_⟩
  rintro rfl
  exact hx rfl

end FamilyCentralizer

end CommSemiring

section DivisionRing

variable [DivisionRing k]

/-- The inverse of an invertible matrix that is the diagonal matrix of a family of scalars is the
diagonal matrix of their inverses. The scalars are automatically nonzero, by invertibility. -/
theorem coe_inv_of_coe_eq_diagonal {g : GL ι k} {d : ι → k}
    (hg : (g : Matrix ι ι k) = diagonal d) : ((g⁻¹ : GL ι k) : Matrix ι ι k) = diagonal d⁻¹ := by
  have hd (i : ι) : d i ≠ 0 := by
    have h := congrFun (congrFun g.mul_inv i) i
    rw [hg, diagonal_mul, one_apply_eq] at h
    exact left_ne_zero_of_mul_eq_one h
  refine Units.inv_eq_of_mul_eq_one_left ?_
  rw [hg, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (hd i))

end DivisionRing

variable [CommRing k]

/-- The determinant of a diagonal matrix is the product of its diagonal entries. -/
@[simp]
theorem det_diagGL (t : ι → kˣ) :
    Matrix.GeneralLinearGroup.det (diagGL t) = ∏ i, t i := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]

/-- Mapping the entries of `diagGL t` along a ring homomorphism gives the diagonal matrix of the
mapped units. -/
@[simp]
theorem map_diagGL {S : Type*} [CommRing S] (f : k →+* S) (t : ι → kˣ) :
    Matrix.GeneralLinearGroup.map f (diagGL t) = diagGL fun i ↦ Units.map (f : k →* S) (t i) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, diagGL_apply, Units.coe_map,
    MonoidHom.coe_ofClass]
  split_ifs <;> simp

/-- Rescaling one column makes an invertible matrix have determinant one. For an empty index
type, every invertible matrix already has determinant one. -/
theorem exists_det_mul_diagGL_eq_one (P : GL ι k) :
    ∃ u : ι → kˣ, Matrix.GeneralLinearGroup.det (P * diagGL u) = 1 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · exact ⟨1, Units.ext <| by simp [Matrix.GeneralLinearGroup.val_det_apply]⟩
  refine ⟨Pi.mulSingle i (Matrix.GeneralLinearGroup.det P)⁻¹, ?_⟩
  rw [map_mul, det_diagGL, Fintype.prod_pi_mulSingle' i, mul_inv_cancel]

/-- Rescale the first column of an invertible matrix by the inverse of its determinant. The
result has determinant one (`TauCeti.det_detOneRescale`), and the operation is the identity on
determinant-one matrices (`TauCeti.detOneRescale_of_det_eq_one`).

Unlike `TauCeti.exists_det_mul_diagGL_eq_one`, the rescaling is an explicit formula, so it
commutes with entrywise ring homomorphisms (`TauCeti.map_detOneRescale`): it is a morphism of
schemes `GLₙ → SLₙ`. In rank zero it is the identity. -/
def detOneRescale (g : GL (Fin n) k) : GL (Fin n) k :=
  g * diagGL fun i : Fin n ↦ if (i : ℕ) = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1

/-- The determinant-one rescaling multiplies on the right by the diagonal matrix
`diag((det g)⁻¹, 1, …, 1)`. -/
theorem detOneRescale_def (g : GL (Fin n) k) :
    detOneRescale g =
      g * diagGL fun i : Fin n ↦ if (i : ℕ) = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1 :=
  (rfl)

/-- The determinant-one rescaling has determinant one. -/
@[simp]
theorem det_detOneRescale (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (detOneRescale g) = 1 := by
  rw [detOneRescale, map_mul, det_diagGL]
  cases n with
  | zero =>
    rw [Fin.prod_univ_zero, mul_one]
    exact Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply])
  | succ m =>
    rw [Fin.prod_univ_succ]
    simp

/-- The determinant-one rescaling fixes matrices of determinant one. -/
theorem detOneRescale_of_det_eq_one {g : GL (Fin n) k}
    (hg : Matrix.GeneralLinearGroup.det g = 1) : detOneRescale g = g := by
  rw [detOneRescale, hg, inv_one]
  simp

/-- The determinant-one rescaling commutes with mapping the entries along a ring
homomorphism. -/
theorem map_detOneRescale {S : Type*} [CommRing S] (f : k →+* S) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.map f (detOneRescale g) =
      detOneRescale (Matrix.GeneralLinearGroup.map f g) := by
  rw [detOneRescale, detOneRescale, map_mul, map_diagGL, Matrix.GeneralLinearGroup.map_det]
  congr 2
  funext i
  split_ifs <;> simp

/-- If `P` intertwines `M` with a diagonal matrix, there is an intertwining matrix of determinant
one, obtained in the nonempty case by rescaling one of the columns of `P`. -/
theorem exists_det_eq_one_mul_map_eq_map_mul_diagGL {Q : Type*} [CommRing Q]
    (f : k →+* Q) (M : GL ι Q) (P : GL ι k) (t : ι → Qˣ)
    (h : M * Matrix.GeneralLinearGroup.map f P =
      Matrix.GeneralLinearGroup.map f P * diagGL t) :
    ∃ P' : GL ι k, Matrix.GeneralLinearGroup.det P' = 1 ∧
      M * Matrix.GeneralLinearGroup.map f P' =
        Matrix.GeneralLinearGroup.map f P' * diagGL t := by
  obtain ⟨u, hu⟩ := exists_det_mul_diagGL_eq_one P
  have hcomm : Commute (diagGL t) (Matrix.GeneralLinearGroup.map f (diagGL u)) := by
    rw [map_diagGL]
    exact (Commute.all _ _).map diagGL
  refine ⟨P * diagGL u, hu, ?_⟩
  rw [map_mul, ← mul_assoc, h, mul_assoc, hcomm.eq, ← mul_assoc]

/-- The determinant of an element of the diagonal torus is the product of its diagonal entries. -/
theorem det_of_mem_diagonalTorus {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n) :
    (Matrix.GeneralLinearGroup.det g : k) = ∏ i, (g : Matrix (Fin n) (Fin n) k) i i := by
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    ← (mem_diagonalTorus_iff.mp hg).diagonal_diag, Matrix.det_diagonal]
  simp [Matrix.diag]

end TauCeti
end
end TAF_LiteralSource_0348

section TAF_LiteralSource_0349
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.Diagonal -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Diagonal elements in the standard representation

This file describes the action of the invertible diagonal matrices `TauCeti.diagGL t` in the
standard representation. These elements are the concrete points of the diagonal torus used to
compute characters and weight spaces; the matrices themselves, and the torus they form, are in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic`.

## Main statements

* `TauCeti.stdRep_diagGL_apply_basisFun`: every standard basis vector is an eigenvector of a
  diagonal matrix.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {n : ℕ}

/-- The standard representation acts at `diagGL t` by coordinatewise multiplication. -/
@[simp↓]
theorem stdRep_diagGL_apply (t : Fin n → kˣ) (v : Fin n → k) (i : Fin n) :
    stdRep k n (diagGL t) v i = (t i : k) * v i := by
  rw [stdRep_apply_apply, diagGL_coe]
  exact Matrix.mulVec_diagonal _ _ _

/-- Every standard basis vector is an eigenvector for a diagonal matrix. -/
@[simp↓]
theorem stdRep_diagGL_apply_basisFun (t : Fin n → kˣ) (i : Fin n) :
    stdRep k n (diagGL t) (Pi.basisFun k (Fin n) i) =
      (t i : k) • Pi.basisFun k (Fin n) i := by
  ext j
  rw [stdRep_diagGL_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [Pi.basisFun_apply, hji]

end TauCeti
end
end TAF_LiteralSource_0349

section TAF_LiteralSource_0350
/- Original module: TauCeti.RepresentationTheory.SymmetricPower -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Symmetric powers of representations

This file equips each symmetric power of a representation with the induced diagonal action.
Intertwining maps and equivalences pass functorially to symmetric powers.

## Main definitions

* `Representation.symmetricPower` is the induced action on `Sym[R]^d M`.
* `IntertwiningMap.symmetricPower` is the induced map between symmetric-power representations.
* `Representation.Equiv.symmetricPower` is the induced equivalence.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.
* The representation and equivariance constructions are adapted from the formal template in
  `TauCeti.RepresentationTheory.ExteriorPower`.
-/

public section

open scoped TensorProduct

universe v w w'

variable {R : Type} {G : Type v} {M : Type w} {N : Type w'}

namespace Representation

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M]

/-- The action induced by a representation on its `d`th symmetric power. -/
noncomputable def symmetricPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (Sym[R]^d M) where
  toFun g := SymmetricPower.map (ι := Fin d) (ρ g)
  map_one' := by
    rw [ρ.map_one, Module.End.one_eq_id, SymmetricPower.map_id,
      Module.End.one_eq_id]
  map_mul' g h := by
    simpa only [map_mul, Module.End.mul_eq_comp] using
      (SymmetricPower.map_comp (ι := Fin d) (ρ h) (ρ g))

/-- The action on a symmetric power is induced by the action on the original representation. -/
@[simp]
theorem symmetricPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.symmetricPower d g = SymmetricPower.map (ι := Fin d) (ρ g) :=
  (rfl)

/-- The symmetric-power action applies the original action to every factor of a pure tensor.

This is intentionally not a simp lemma: `symmetricPower_apply` followed by
`SymmetricPower.map_tprod` already performs this simplification. -/
theorem symmetricPower_apply_tprod (ρ : Representation R G M) (d : ℕ) (g : G) (m : Fin d → M) :
    ρ.symmetricPower d g (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, ρ g (m i) := by
  rw [symmetricPower_apply, SymmetricPower.map_tprod]

end CommSemiring

end Representation

namespace Representation.IntertwiningMap

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- An intertwining map induces an intertwining map on every symmetric power. -/
noncomputable def symmetricPower (f : IntertwiningMap ρ σ) (d : ℕ) :
    IntertwiningMap (ρ.symmetricPower d) (σ.symmetricPower d) where
  toLinearMap := SymmetricPower.map (ι := Fin d) f.toLinearMap
  isIntertwining' g := by
    rw [Representation.symmetricPower_apply, Representation.symmetricPower_apply,
      ← SymmetricPower.map_comp, ← SymmetricPower.map_comp, f.isIntertwining']

/-- The underlying linear map is the usual map induced on symmetric powers. -/
@[simp]
theorem symmetricPower_toLinearMap (f : IntertwiningMap ρ σ) (d : ℕ) :
    (f.symmetricPower d).toLinearMap =
      SymmetricPower.map (ι := Fin d) f.toLinearMap :=
  (rfl)

/-- The induced map sends a pure symmetric tensor to the tensor of the images. -/
@[simp]
theorem symmetricPower_apply_tprod (f : IntertwiningMap ρ σ) (d : ℕ) (m : Fin d → M) :
    f.symmetricPower d (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, f (m i) :=
  SymmetricPower.map_tprod f.toLinearMap m

/-- Symmetric powers preserve identity intertwining maps. -/
@[simp]
theorem symmetricPower_id (d : ℕ) : (IntertwiningMap.id ρ).symmetricPower d =
      IntertwiningMap.id (ρ.symmetricPower d) := by
  apply IntertwiningMap.ext
  simp

/-- Symmetric powers preserve composition of intertwining maps. -/
@[simp]
theorem symmetricPower_comp {P : Type*} [AddCommMonoid P] [Module R P]
    {τ : Representation R G P} (f : IntertwiningMap ρ σ) (g : IntertwiningMap σ τ) (d : ℕ) :
    (g.comp f).symmetricPower d = (g.symmetricPower d).comp (f.symmetricPower d) := by
  apply IntertwiningMap.ext
  exact SymmetricPower.map_comp f.toLinearMap g.toLinearMap

end CommSemiring

end Representation.IntertwiningMap

namespace Representation.Equiv

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- The linear equivalence induced on `d`th symmetric powers by an equivalence of
representations. -/
private noncomputable def symmetricPowerLinearEquiv (e : ρ.Equiv σ) (d : ℕ) :
    (Sym[R]^d M) ≃ₗ[R] (Sym[R]^d N) :=
  LinearEquiv.ofLinearMap
    (SymmetricPower.map (ι := Fin d) e.toLinearMap)
    (SymmetricPower.map (ι := Fin d) e.symm.toLinearMap)
    (by
      rw [← SymmetricPower.map_comp, Representation.Equiv.toLinearMap_symm,
        e.toLinearEquiv.comp_symm, SymmetricPower.map_id])
    (by
      rw [← SymmetricPower.map_comp, Representation.Equiv.toLinearMap_symm,
        e.toLinearEquiv.symm_comp, SymmetricPower.map_id])

private theorem symmetricPowerLinearEquiv_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (symmetricPowerLinearEquiv e d).toLinearMap =
      SymmetricPower.map (ι := Fin d) e.toLinearMap :=
  rfl

private theorem symmetricPowerLinearEquiv_symm_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (symmetricPowerLinearEquiv e d).symm.toLinearMap =
      SymmetricPower.map (ι := Fin d) e.symm.toLinearMap :=
  rfl

/-- An equivalence of representations induces an equivalence of every symmetric power. -/
noncomputable def symmetricPower (e : ρ.Equiv σ) (d : ℕ) :
    (ρ.symmetricPower d).Equiv (σ.symmetricPower d) :=
  .mk (symmetricPowerLinearEquiv e d) fun g => by
    rw [symmetricPowerLinearEquiv_toLinearMap]
    exact (e.toIntertwiningMap.symmetricPower d).isIntertwining' g

private theorem symmetricPower_toLinearEquiv (e : ρ.Equiv σ) (d : ℕ) :
    (e.symmetricPower d).toLinearEquiv = symmetricPowerLinearEquiv e d :=
  toLinearEquiv_mk' _

/-- The underlying linear map is the usual map induced on symmetric powers. -/
@[simp]
theorem symmetricPower_toLinearMap (e : ρ.Equiv σ) (d : ℕ) : (e.symmetricPower d).toLinearMap =
      SymmetricPower.map (ι := Fin d) e.toLinearMap :=
  (rfl)

/-- The induced equivalence sends a pure symmetric tensor to the tensor of the images. -/
@[simp]
theorem symmetricPower_apply_tprod (e : ρ.Equiv σ) (d : ℕ) (m : Fin d → M) :
    e.symmetricPower d (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, e (m i) :=
  SymmetricPower.map_tprod e.toLinearMap m

/-- Symmetric powers preserve identity equivalences. -/
@[simp]
theorem symmetricPower_refl (d : ℕ) :
    (Equiv.refl ρ).symmetricPower d = .refl (ρ.symmetricPower d) := by
  have h : ((Equiv.refl ρ).symmetricPower d).toLinearMap =
      (Equiv.refl (ρ.symmetricPower d)).toLinearMap := by
    simp
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

/-- Symmetric powers preserve inverses of equivalences. -/
@[simp]
theorem symmetricPower_symm (e : ρ.Equiv σ) (d : ℕ) :
    e.symm.symmetricPower d = (e.symmetricPower d).symm := by
  have h : (e.symm.symmetricPower d).toLinearMap =
      ((e.symmetricPower d).symm).toLinearMap := by
    rw [symmetricPower_toLinearMap, toLinearMap_symm (e.symmetricPower d),
      symmetricPower_toLinearEquiv, symmetricPowerLinearEquiv_symm_toLinearMap]
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

/-- Symmetric powers preserve composition of equivalences. -/
@[simp]
theorem symmetricPower_trans {P : Type*} [AddCommMonoid P] [Module R P]
    {τ : Representation R G P} (e : ρ.Equiv σ) (f : σ.Equiv τ) (d : ℕ) :
    (e.trans f).symmetricPower d = (e.symmetricPower d).trans (f.symmetricPower d) := by
  have h : ((e.trans f).symmetricPower d).toLinearMap =
      ((e.symmetricPower d).trans (f.symmetricPower d)).toLinearMap := by
    simp
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

end CommSemiring

end Representation.Equiv
end
end TAF_LiteralSource_0350

section TAF_LiteralSource_0351
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The symmetric homogeneous polynomials of a fixed degree

The symmetric polynomials of `Mathlib.RingTheory.MvPolynomial.Symmetric.Defs` are graded by total
degree, each graded piece being the intersection of `MvPolynomial.symmetricSubalgebra` with the
homogeneous polynomials `MvPolynomial.homogeneousSubmodule` of that degree.  This file names that
intersection, `TauCeti.symmetricHomogeneousSubmodule`; it is the module the classical families of
symmetric polynomials are bases of, one degree at a time: the monomial symmetric polynomials over
any commutative semiring, and the Schur polynomials over a commutative ring.

## Main definitions

* `TauCeti.symmetricHomogeneousSubmodule σ R n`: the polynomials in `σ` over `R` that are both
  symmetric and homogeneous of degree `n`.

## Main results

* `TauCeti.prod_map_mem_symmetricHomogeneousSubmodule`: a multiset product of symmetric
  homogeneous factors has degree the sum of their degrees.

* `MvPolynomial.isHomogeneous_esymm`: the elementary symmetric polynomial `eₖ` is homogeneous of
  degree `k`.
* `MvPolynomial.isHomogeneous_hsymm`: the complete homogeneous symmetric polynomial `hₖ` is
  homogeneous of degree `k`.
-/

public section

namespace TauCeti

open MvPolynomial

variable (σ : Type*) (R : Type*) [CommSemiring R] (n : ℕ)

/-- **The symmetric polynomials of degree `n`**: those polynomials in the alphabet `σ` over `R`
that are both symmetric and homogeneous of degree `n`.  The monomial symmetric polynomials of the
partitions of `n` are a basis of this module over any commutative semiring; the Schur polynomials
of those partitions are a basis of it over a commutative ring. -/
noncomputable def symmetricHomogeneousSubmodule : Submodule R (MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).toSubmodule ⊓ homogeneousSubmodule σ R n

variable {σ R n}

/-- Membership in `TauCeti.symmetricHomogeneousSubmodule` is the conjunction of the two
conditions defining it. -/
@[simp]
theorem mem_symmetricHomogeneousSubmodule {p : MvPolynomial σ R} :
    p ∈ symmetricHomogeneousSubmodule σ R n ↔ p.IsSymmetric ∧ p.IsHomogeneous n :=
  Iff.rfl

/-- A multiset product of symmetric polynomials, with the factor indexed by `k` homogeneous
of degree `k`, is symmetric and homogeneous of degree the sum of the indices. -/
theorem prod_map_mem_symmetricHomogeneousSubmodule (f : ℕ → MvPolynomial σ R)
    (hf : ∀ k, f k ∈ symmetricHomogeneousSubmodule σ R k) (s : Multiset ℕ) :
    (s.map f).prod ∈ symmetricHomogeneousSubmodule σ R s.sum := by
  apply mem_symmetricHomogeneousSubmodule.mpr
  induction s using Multiset.induction_on with
  | empty => exact ⟨IsSymmetric.one, isHomogeneous_one σ R⟩
  | cons k s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have hk := mem_symmetricHomogeneousSubmodule.mp (hf k)
    exact ⟨hk.1.mul ih.1, hk.2.mul ih.2⟩

end TauCeti

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The elementary symmetric polynomial `eₖ` is homogeneous of degree `k`. -/
theorem isHomogeneous_esymm [Fintype σ] (k : ℕ) : (esymm σ R k).IsHomogeneous k := by
  rw [esymm_eq_sum_subtype]
  refine IsHomogeneous.sum _ _ _ fun t _ => ?_
  have h := IsHomogeneous.prod (t : Finset σ) (fun i => (X i : MvPolynomial σ R)) (fun _ => 1)
    fun i _ => isHomogeneous_X R i
  rwa [Finset.sum_const, smul_eq_mul, mul_one, t.2] at h

/-- The complete homogeneous symmetric polynomial `hₖ` is homogeneous of degree `k`. -/
theorem isHomogeneous_hsymm [Fintype σ] [DecidableEq σ] (k : ℕ) :
    (hsymm σ R k).IsHomogeneous k := by
  have h (t : Multiset σ) : ((t.map X).prod : MvPolynomial σ R).IsHomogeneous t.card := by
    induction t using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one σ R
    | cons a t ih => simpa [add_comm] using (isHomogeneous_X R a).mul ih
  exact IsHomogeneous.sum _ _ _ fun s _ => by simpa [s.2] using h s.1

end MvPolynomial
end
end TAF_LiteralSource_0351

section TAF_LiteralSource_0352
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Evaluating the complete homogeneous symmetric polynomial

The complete homogeneous symmetric polynomial `h_d` in variables indexed by a finite type `σ` is
the sum of all monomials of degree `d`, one for each unordered `d`-tuple of indices.  Evaluating it
at a family `f : σ → R` therefore sums, over those unordered tuples, the product of the values `f`
takes on the tuple: `TauCeti.eval_hsymm`.

In two variables the unordered `d`-tuples are the `d + 1` splittings counted by
`TauCeti.symFinTwoEquiv`, and the evaluation reads `h_d(x, y) = ∑_{i ≤ d} xⁱ y^{d-i}`:
`TauCeti.eval_hsymm_fin_two`.

Reading the unordered tuples as their multiplicity functions instead writes `h_d` as the sum of the
monomials of degree `d`, indexed by `Finset.piAntidiag`: `TauCeti.hsymm_eq_sum_piAntidiag`.  Summed
over all degrees, this is the generating function `∑ₙ hₙ tⁿ = ∏ᵢ ∑ₙ xᵢⁿ tⁿ`, the product over the
variables of the geometric series `(1 - xᵢ t)⁻¹`: `TauCeti.mk_hsymm_eq_prod_mk_pow`, and
`TauCeti.mk_aeval_hsymm_eq_prod_mk_pow` at an arbitrary family of values.  On the alphabet
`σ × τ`, evaluated at products `fᵢ gⱼ`, the factors with a fixed first index multiply to
`∑ₘ fᵢᵐ hₘ(g) tᵐ`, so `hₙ(fᵢ gⱼ)` is the sum of `∏ᵢ fᵢ^{lᵢ} h_{lᵢ}(g)` over the exponent vectors
`l` on `σ` of total degree `n`: `TauCeti.aeval_hsymm_prod_eq_sum_finsuppAntidiag`.  This is the
first step of the Cauchy identity for Schur polynomials.

Determinantal formulas such as Jacobi--Trudi index `h` by integers, `h_m` being `0` for `m < 0`;
reading a negative index as `0` through a truncated subtraction of natural numbers would silently
give the wrong formula.  `TauCeti.hsymmInt` is this integer-indexed complete homogeneous symmetric
polynomial.

## Main results

* `TauCeti.eval_hsymm` evaluates the complete homogeneous symmetric polynomial as a sum over the
  unordered `d`-tuples of indices.
* `TauCeti.eval_hsymm_fin_two` reads that off in two variables: `h_d(x, y) = ∑_{i ≤ d} xⁱ y^{d-i}`.
* `TauCeti.hsymm_eq_sum_piAntidiag` writes `h_d` as the sum of the monomials of degree `d`.
* `TauCeti.mk_hsymm_eq_prod_mk_pow`: the generating function of the `h_d`, and
  `TauCeti.mk_aeval_hsymm_eq_prod_mk_pow`, the same evaluated at an arbitrary family.
* `TauCeti.aeval_hsymm_prod_eq_sum_finsuppAntidiag`: `hₙ(fᵢ gⱼ) = ∑_l ∏ᵢ fᵢ^{lᵢ} h_{lᵢ}(g)`.
* `TauCeti.hsymmPart_mem_symmetricHomogeneousSubmodule`: a product `h_ν` of complete homogeneous
  symmetric polynomials is symmetric and homogeneous of degree `n` for a partition `ν` of `n`.
* `TauCeti.hsymmInt`: the complete homogeneous symmetric polynomial `h_m` of an integer degree `m`,
  which is `0` for `m < 0`.
-/

public section

namespace TauCeti

/-- **The complete homogeneous symmetric polynomial evaluated**: `h_d(f)` is the sum, over the
unordered `d`-tuples of indices, of the product of the values `f` takes on the tuple. -/
theorem eval_hsymm {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R] (f : σ → R)
    (d : ℕ) : MvPolynomial.eval f (MvPolynomial.hsymm σ R d)
      = ∑ s : Sym σ d, ((s : Multiset σ).map f).prod := by
  rw [MvPolynomial.hsymm, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  simp [Function.comp_def]

/-- **The complete homogeneous symmetric polynomial in two variables**: `h_d(x, y)` is the sum of
all `d + 1` monomials `xⁱ y^{d-i}` of degree `d`. -/
theorem eval_hsymm_fin_two {R : Type*} [CommSemiring R] (f : Fin 2 → R) (d : ℕ) :
    MvPolynomial.eval f (MvPolynomial.hsymm (Fin 2) R d)
      = ∑ i ∈ Finset.range (d + 1), f 0 ^ i * f 1 ^ (d - i) := by
  rw [eval_hsymm, ← Fin.sum_univ_eq_sum_range _ (d + 1),
    ← Equiv.sum_comp (symFinTwoEquiv d).symm]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [coe_symFinTwoEquiv_symm_apply]
  simp

/-- **The monomial expansion of the complete homogeneous symmetric polynomial**: `h_d` is the sum of
the monomials `∏ᵢ X_i ^ γ_i` over the exponent vectors `γ` of total degree `d`.  This is the
multiplicity-function form of `MvPolynomial.hsymm`, whose summands are indexed by the unordered
`d`-tuples of variables. -/
theorem hsymm_eq_sum_piAntidiag {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] (d : ℕ) :
    MvPolynomial.hsymm σ R d =
      ∑ γ ∈ Finset.piAntidiag (Finset.univ : Finset σ) d,
        ∏ i, (MvPolynomial.X i : MvPolynomial σ R) ^ γ i := by
  rw [← Finset.map_sym_eq_piAntidiag, Finset.sum_map, Finset.sym_univ, MvPolynomial.hsymm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hi), pow_zero]

/-- **The generating function of the complete homogeneous symmetric polynomials**:
`∑ₙ hₙ tⁿ = ∏ᵢ ∑ₙ xᵢⁿ tⁿ`, as power series over `MvPolynomial σ R`.  Each factor is the geometric
series `(1 - xᵢ t)⁻¹`, so the coefficient of `tⁿ` collects one monomial of degree `n` for every
exponent vector. -/
theorem mk_hsymm_eq_prod_mk_pow {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] :
    PowerSeries.mk (fun n => MvPolynomial.hsymm σ R n) =
      ∏ i, PowerSeries.mk fun n => (MvPolynomial.X i : MvPolynomial σ R) ^ n := by
  ext d
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_prod, hsymm_eq_sum_piAntidiag, Finset.finsuppAntidiag,
    Finset.sum_map, ← Finset.sum_attach (Finset.piAntidiag Finset.univ d)]
  simp

/-- **The generating function of the complete homogeneous symmetric polynomials, evaluated**:
`∑ₙ hₙ(ψ) tⁿ = ∏ᵢ ∑ₙ ψᵢⁿ tⁿ` for a family `ψ` in a commutative `R`-algebra `S`, as power series
over `S`.  This is `TauCeti.mk_hsymm_eq_prod_mk_pow` with the variables evaluated at `ψ`. -/
theorem mk_aeval_hsymm_eq_prod_mk_pow {σ R S : Type*} [Fintype σ] [DecidableEq σ]
    [CommSemiring R] [CommSemiring S] [Algebra R S] (ψ : σ → S) :
    PowerSeries.mk (fun n => MvPolynomial.aeval ψ (MvPolynomial.hsymm σ R n)) =
      ∏ i, PowerSeries.mk fun n => ψ i ^ n := by
  ext d
  have h := congrArg (fun F => MvPolynomial.aeval ψ (PowerSeries.coeff d F))
    (mk_hsymm_eq_prod_mk_pow (σ := σ) R)
  simpa only [PowerSeries.coeff_mk, PowerSeries.coeff_prod, map_sum, map_prod, map_pow,
    MvPolynomial.aeval_X] using h

/-- **`hₙ` of the products `fᵢ gⱼ`, grouped by the first index**: substituting `fᵢ gⱼ` for the
variable indexed by `(i, j)` in `hₙ` on the alphabet `σ × τ` gives `∑_l ∏ᵢ fᵢ^{lᵢ} h_{lᵢ}(g)`,
the sum running over the exponent vectors `l` on `σ` of total degree `n`.  In generating-function
form, the product of the geometric series `(1 - fᵢ gⱼ t)⁻¹` over all pairs is computed one `i` at a
time, the factors with a fixed `i` multiplying to `∑ₘ fᵢᵐ hₘ(g) tᵐ`. -/
theorem aeval_hsymm_prod_eq_sum_finsuppAntidiag {σ τ R S : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] [CommSemiring R] [CommSemiring S] [Algebra R S] (f : σ → S)
    (g : τ → S) (n : ℕ) :
    MvPolynomial.aeval (fun p : σ × τ => f p.1 * g p.2) (MvPolynomial.hsymm (σ × τ) R n) =
      ∑ l ∈ Finset.finsuppAntidiag Finset.univ n,
        ∏ i, f i ^ l i * MvPolynomial.aeval g (MvPolynomial.hsymm τ R (l i)) := by
  have hscale (i : σ) (m : ℕ) : f i ^ m * MvPolynomial.aeval g (MvPolynomial.hsymm τ R m) =
      MvPolynomial.aeval (fun j => f i * g j) (MvPolynomial.hsymm τ R m) := by
    simpa only [MvPolynomial.aeval_def] using
      ((MvPolynomial.isHomogeneous_hsymm m).eval₂_const_mul (algebraMap R S) g (f i)).symm
  have h : PowerSeries.mk (fun m => MvPolynomial.aeval (fun p : σ × τ => f p.1 * g p.2)
      (MvPolynomial.hsymm (σ × τ) R m)) =
      ∏ i, PowerSeries.mk fun m => f i ^ m * MvPolynomial.aeval g (MvPolynomial.hsymm τ R m) := by
    simp only [hscale, mk_aeval_hsymm_eq_prod_mk_pow, Fintype.prod_prod_type]
  simpa only [PowerSeries.coeff_mk, PowerSeries.coeff_prod] using
    congrArg (PowerSeries.coeff n) h

/-- **A product of complete homogeneous symmetric polynomials is symmetric and homogeneous**: for
a partition `ν` of `n`, `h_ν = ∏ᵢ h_{νᵢ}` lies in `TauCeti.symmetricHomogeneousSubmodule σ R n`,
each factor `h_{νᵢ}` being symmetric and homogeneous of degree `νᵢ`. -/
theorem hsymmPart_mem_symmetricHomogeneousSubmodule {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommSemiring R] {n : ℕ} (ν : n.Partition) :
    MvPolynomial.hsymmPart σ R ν ∈ symmetricHomogeneousSubmodule σ R n := by
  rw [MvPolynomial.hsymmPart]
  simpa only [ν.parts_sum] using
    prod_map_mem_symmetricHomogeneousSubmodule (MvPolynomial.hsymm σ R)
      (fun k => mem_symmetricHomogeneousSubmodule.mpr
        ⟨MvPolynomial.hsymm_isSymmetric σ R k, MvPolynomial.isHomogeneous_hsymm k⟩) ν.parts

section hsymmInt

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommSemiring R]

/-- The **complete homogeneous symmetric polynomial of integer degree** `m`: `h_m` for `m ≥ 0`
and `0` for `m < 0`.  This is the indexing determinantal formulas such as Jacobi--Trudi use. -/
noncomputable def hsymmInt (m : ℤ) : MvPolynomial σ R :=
  if 0 ≤ m then MvPolynomial.hsymm σ R m.toNat else 0

variable {σ R}

/-- In a nonnegative degree, `TauCeti.hsymmInt` is `MvPolynomial.hsymm`. -/
@[simp]
theorem hsymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    hsymmInt σ R m = MvPolynomial.hsymm σ R m.toNat := by
  simp [hsymmInt, hm]

/-- In a negative degree, `TauCeti.hsymmInt` vanishes. -/
@[simp]
theorem hsymmInt_of_neg {m : ℤ} (hm : m < 0) : hsymmInt σ R m = 0 := by
  simp [hsymmInt, not_le.mpr hm]

/-- In a natural-number degree, `TauCeti.hsymmInt` is `MvPolynomial.hsymm`. -/
theorem hsymmInt_natCast (n : ℕ) : hsymmInt σ R n = MvPolynomial.hsymm σ R n := by
  simp [hsymmInt]

/-- `h_0 = 1`. -/
theorem hsymmInt_zero : hsymmInt σ R 0 = 1 := by
  simp

/-- Changing the coefficients along a ring homomorphism preserves `TauCeti.hsymmInt`. -/
@[simp]
theorem map_hsymmInt {S : Type*} [CommSemiring S] (m : ℤ) (f : R →+* S) :
    MvPolynomial.map f (hsymmInt σ R m) = hsymmInt σ S m := by
  unfold hsymmInt
  split_ifs <;> simp [MvPolynomial.map_hsymm]

/-- Renaming the variables along a bijection preserves `TauCeti.hsymmInt`. -/
@[simp]
theorem rename_hsymmInt {τ : Type*} [Fintype τ] [DecidableEq τ] (m : ℤ) (e : σ ≃ τ) :
    MvPolynomial.rename e (hsymmInt σ R m) = hsymmInt τ R m := by
  unfold hsymmInt
  split_ifs <;> simp [MvPolynomial.rename_hsymm]

end hsymmInt

end TauCeti
end
end TAF_LiteralSource_0352

section TAF_LiteralSource_0353
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Symmetric powers of the standard representation

This file specializes symmetric powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure symmetric
tensor.

A diagonal matrix acts diagonally on the basis of `Sym[k]^d (Fin n → k)` given by the unordered
`d`-tuples of standard basis vectors, with eigenvalue the product of the corresponding diagonal
entries. Summing those eigenvalues, the character of the `d`th symmetric power at a diagonal
matrix is the `d`th complete homogeneous symmetric polynomial in its diagonal entries, dual to the
elementary symmetric polynomial the exterior power gives.

## Main definitions

* `TauCeti.symPowerRep` is the symmetric-power representation of `GL n k`.
* `TauCeti.symPowerFDRep` is its bundled finite-dimensional form.

## Main results

* `TauCeti.char_symPowerRep_diagonal` identifies the character on diagonal matrices with a
  complete homogeneous symmetric polynomial.

## References

* The standard-representation specialization is adapted from the formal template in
  `TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower`.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

variable (k : Type) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The `d`th symmetric power of the standard representation of `GL n k`. -/
noncomputable abbrev symPowerRep :
    Representation k (GL (Fin n) k) (Sym[k]^d (Fin n → k)) :=
  (stdRep k n).symmetricPower d

/-- The symmetric power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev symPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (symPowerRep k n d)

end CommRing

section Field

variable [Field k]

/-- The character of the `d`th symmetric power on a diagonal matrix is the `d`th complete
homogeneous symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_symPowerRep_diagonal (t : Fin n → kˣ) : (symPowerRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.hsymm (Fin n) k d) := by
  rw [Representation.character, Representation.symmetricPower_apply,
    Module.Basis.trace_map_symmetricPower_of_apply (Pi.basisFun k (Fin n))
      (stdRep k n (diagGL t)) (fun i => (t i : k)) d (stdRep_diagGL_apply_basisFun t)]
  -- both sides sum, over the unordered `d`-tuples of indices, the product of the entries listed
  rw [eval_hsymm]

/-- The character of the bundled `d`th symmetric power on a diagonal matrix is the `d`th complete
homogeneous symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_symPowerFDRep_diagonal (t : Fin n → kˣ) : (symPowerFDRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.hsymm (Fin n) k d) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_symPowerRep_diagonal k n d t

end Field

end TauCeti
end
end TAF_LiteralSource_0353

