module
public import shared_results.part023
public import paper_results.part005
public import paper_results.dimension_core
public import shared_results.part003
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import paper_results.part002
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import paper_results.ordinary_ideal_tor_bounds
public import graph_foundation.part010
public import paper_results.transfer_formulas
public import paper_results.theorem81_analytic_spread
public import paper_results.torsion_core
public import paper_results.graded_homology_core
public import Mathlib.Algebra.CharP.Basic
public import graph_foundation.part009
public import paper_results.part003
public import paper_results.part004
public import graph_foundation.part008
public import paper_results.part001
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ULift

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.HomogeneousIdealQuotientTorShift -/
section

/-! # The ideal-to-quotient Tor shift for a homogeneous ideal

A positive ordinary-degree ideal cycle has a polynomial Koszul primitive.
Its image in the literal quotient is a cycle one homological degree higher.
Any quotient boundary would, after lifting its primitive, give an ideal
boundary. This constructs the nonzero class needed for the depth statements
without assuming Auslander--Buchsbaum or a numerical Betti shift.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul
open CommAlg.Polymatroid MvPolynomial FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]

/-- The map is coefficientwise the literal polynomial quotient map. -/
def ambientLiteralQuotientCoefficient (J : Ideal (MvPolynomial V K)) :
    CoefficientQuotient (k := K) (∅ : Family V) →ₗ[MvPolynomial V K]
      MvPolynomial V K ⧸ J :=
  (Ideal.Quotient.mkₐ (MvPolynomial V K) J).toLinearMap.comp
    emptyCoefficientPolynomialEquiv.toLinearMap

def ambientLiteralQuotient (J : Ideal (MvPolynomial V K)) (p : ℕ) :
    AmbientKoszulCoordinates (k := K) (V := V) p →ₗ[K]
      PolynomialCoordinateTor.Coordinates (V := V) (M := MvPolynomial V K ⧸ J) p :=
  (Finsupp.mapRange.linearMap (ambientLiteralQuotientCoefficient J)).restrictScalars K

lemma ambientLiteralQuotient_eq (P : QuotientGroebnerData V K) (p : ℕ)
    (x : AmbientKoszulCoordinates (k := K) (V := V) p) :
    ambientLiteralQuotient P.ideal p x = P.coordinates p (ambientKoszulProjection P p x) := by
  ext F
  exact (ambientKoszulProjection_polynomial P p x F).symm

lemma ambientLiteralQuotient_surjective (P : QuotientGroebnerData V K) (p : ℕ) :
    Function.Surjective (ambientLiteralQuotient P.ideal p) := by
  intro y
  refine ⟨ambientKoszulSection P p ((P.coordinates p).symm y), ?_⟩
  have hs := LinearMap.congr_fun (ambientKoszulProjection_section P p)
    ((P.coordinates p).symm y)
  change ambientKoszulProjection P p
    (ambientKoszulSection P p ((P.coordinates p).symm y)) = (P.coordinates p).symm y at hs
  rw [ambientLiteralQuotient_eq, hs, LinearEquiv.apply_symm_apply]

lemma ambientLiteralQuotient_d (J : Ideal (MvPolynomial V K)) (p : ℕ)
    (x : AmbientKoszulCoordinates (k := K) (V := V) (p+1)) :
    PolynomialCoordinateTor.differential (K := K) (V := V) (M := MvPolynomial V K ⧸ J)
      p (ambientLiteralQuotient J (p+1) x) =
      ambientLiteralQuotient J p (quotientDifferential (k := K) ∅ p x) :=
  coordinateDifferential_mapRange (X : V → MvPolynomial V K)
    (ModuleCat.of (MvPolynomial V K) (CoefficientQuotient (k := K) (∅ : Family V)))
    (ModuleCat.of (MvPolynomial V K) (MvPolynomial V K ⧸ J))
    (ambientLiteralQuotientCoefficient J) p x

lemma ambientLiteralQuotient_ideal (P : QuotientGroebnerData V K) (p : ℕ)
    (x : Set.powersetCard V p →₀ P.ideal) :
    ambientLiteralQuotient P.ideal p (idealCoordinatesToAmbient P.ideal p x) = 0 := by
  rw [ambientLiteralQuotient_eq]
  have h := idealCoordinatesToAmbient_mem_kernel P p x
  change ambientKoszulProjection P p (idealCoordinatesToAmbient P.ideal p x) = 0 at h
  rw [h, map_zero]

lemma ambientLiteralQuotient_kernel (P : QuotientGroebnerData V K) (p : ℕ)
    (x : AmbientKoszulCoordinates (k := K) (V := V) p)
    (hx : ambientLiteralQuotient P.ideal p x = 0) :
    ∃ y : Set.powersetCard V p →₀ P.ideal, idealCoordinatesToAmbient P.ideal p y = x := by
  have hk : ambientKoszulProjection P p x = 0 := by
    apply (P.coordinates p).injective
    rw [map_zero, ← ambientLiteralQuotient_eq, hx]
  obtain ⟨y, hy⟩ := idealCoordinatesToKernel_surjective P p ⟨x, hk⟩
  exact ⟨y, congrArg Subtype.val hy⟩

lemma idealCoordinatesToAmbient_previous (J : Ideal (MvPolynomial V K)) (p : ℕ)
    (x : Set.powersetCard V p →₀ J) :
    quotientPreviousDifferential (k := K) ∅ p (idealCoordinatesToAmbient J p x) =
      idealCoordinatesToAmbient J p.pred (actualIdealPreviousDifferential J p x) := by
  cases p with
  | zero => simp only [quotientPreviousDifferential, actualIdealPreviousDifferential,
      LinearMap.zero_apply, map_zero]
  | succ p => exact idealCoordinatesToAmbient_differential J p x

/-- Fine polynomial contractions assemble into a primitive in the same
positive ordinary degree. The sum uses only the finite support of the cycle. -/
theorem ambientKoszul_ordinary_filling (q : ℕ) (hq : 0 < q) (p : ℕ)
    (x : AmbientKoszulCoordinates (k := K) (V := V) p)
    (hx : x ∈ ordinaryQuotientPiece (k := K) (∅ : Family V) q p)
    (hdx : quotientPreviousDifferential (k := K) ∅ p x = 0) :
    ∃ y, y ∈ ordinaryQuotientPiece (k := K) (∅ : Family V) q (p+1) ∧
      quotientDifferential (k := K) ∅ p y = x := by
  apply fineCycleFilling_assemble
    (quotientCoefficientBasis (k := K) ∅ (p+1))
    (quotientCoefficientBasis (k := K) ∅ p)
    (quotientCoefficientBasis (k := K) ∅ p.pred)
    quotientDegree quotientDegree quotientDegree
    (quotientDifferential (k := K) ∅ p) (quotientPreviousDifferential (k := K) ∅ p)
    (quotientPreviousDifferential_homogeneous ∅ p) (fun α => α.degree = q) ?_ x hx hdx
  intro α hα y hy hdy
  apply ambientKoszul_fine_filling α _ p y hy hdy
  intro hz
  rw [hz, map_zero] at hα
  omega

variable (P : QuotientGroebnerData V K)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

/-- The connecting construction retains the original cycle and original
quotient, and detects nonvanishing even when p=0. -/
theorem quotientCoordinateHomology_nontrivial_of_idealClass (q : ℕ) (hq : 0 < q) (p : ℕ)
    (z : LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p))
    (hz : homologyClass (actualIdealOrdinaryDifferential P hJ q p)
      (actualIdealOrdinaryPrevious P hJ q p) (actualIdealOrdinaryDifferential_comp P hJ q p) z ≠ 0) :
    Nontrivial (PolynomialCoordinateTor.Homology (K := K) (V := V)
      (M := MvPolynomial V K ⧸ P.ideal) (p+1)) := by
  let x := idealCoordinatesToAmbient P.ideal p z.val.val
  have hx : x ∈ ordinaryQuotientPiece (k := K) (∅ : Family V) q p :=
    (actualIdealOrdinaryPiece_mem_iff P hJ q p z.val.val).mp z.val.property
  have hd : quotientPreviousDifferential (k := K) ∅ p x = 0 := by
    dsimp only [x]
    rw [idealCoordinatesToAmbient_previous,
      ← actualIdealOrdinaryPrevious_val P hJ q p z.val,
      z.property]
    change idealCoordinatesToAmbient P.ideal p.pred 0 = 0
    exact map_zero _
  obtain ⟨y, hy, hdy⟩ := ambientKoszul_ordinary_filling q hq p x hx hd
  let c := ambientLiteralQuotient P.ideal (p+1) y
  have hc : PolynomialCoordinateTor.previous (K := K) (V := V)
      (M := MvPolynomial V K ⧸ P.ideal) (p+1) c = 0 := by
    change PolynomialCoordinateTor.differential p c = 0
    dsimp only [c]
    rw [ambientLiteralQuotient_d, hdy]
    exact ambientLiteralQuotient_ideal P p z.val.val
  let w : LinearMap.ker (PolynomialCoordinateTor.previous (K := K) (V := V)
      (M := MvPolynomial V K ⧸ P.ideal) (p+1)) := ⟨c, hc⟩
  have hw : (Submodule.Quotient.mk w : PolynomialCoordinateTor.Homology (K := K)
      (V := V) (M := MvPolynomial V K ⧸ P.ideal) (p+1)) ≠ 0 := by
    intro hw
    obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).mp hw
    have hv' : PolynomialCoordinateTor.differential (K := K) (V := V)
        (M := MvPolynomial V K ⧸ P.ideal) (p+1) v = c := congrArg Subtype.val hv
    obtain ⟨t, ht⟩ := ambientLiteralQuotient_surjective P (p+2) v
    have ha : ambientLiteralQuotient P.ideal (p+1)
        (y - quotientDifferential (k := K) ∅ (p+1) t) = 0 := by
      rw [map_sub, ← ambientLiteralQuotient_d, ht, hv']
      exact sub_self c
    obtain ⟨a, ha'⟩ := ambientLiteralQuotient_kernel P (p+1) _ ha
    have hda : actualIdealCoordinateDifferential P.ideal p a = z.val.val := by
      apply idealCoordinatesToAmbient_injective P.ideal p
      rw [← idealCoordinatesToAmbient_differential, ha', map_sub, hdy]
      have hdd := LinearMap.congr_fun (quotientDifferential_comp (k := K) (∅ : Family V) p) t
      change quotientDifferential (k := K) ∅ p
        (quotientDifferential (k := K) ∅ (p+1) t) = 0 at hdd
      rw [hdd, sub_zero]
    obtain ⟨a', ha''⟩ := ordinaryIdeal_boundary_reflects P hJ q p z.val a hda
    apply hz
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨a', Subtype.ext ha''⟩
  exact ⟨⟨Submodule.Quotient.mk w, 0, hw⟩⟩

end FourPapers.Sublattice

namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul MvPolynomial
open FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

/-- A positive-degree genuine ideal Betti entry gives nonzero genuine
quotient Tor in the next homological degree. -/
theorem quotientTor_nonzero_of_ordinaryIdealBetti (p q : ℕ) (hq : 0 < q)
    (h : ordinaryIdealBettiNumber P hJ p q ≠ 0) :
    ¬ IsZero (finitePolynomialTor (p+1)
      (ModuleCat.of (MvPolynomial V K) (MvPolynomial V K ⧸ P.ideal))) := by
  rw [ordinaryIdealBettiNumber_eq_finrank] at h
  letI : Nontrivial (actualIdealOrdinaryHomology P hJ q p) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h)
  obtain ⟨a, ha⟩ := exists_ne (0 : actualIdealOrdinaryHomology P hJ q p)
  obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap
    (actualIdealOrdinaryDifferential P hJ q p) (actualIdealOrdinaryPrevious P hJ q p)
    (actualIdealOrdinaryDifferential_comp P hJ q p))).mkQ_surjective a
  letI := quotientCoordinateHomology_nontrivial_of_idealClass P hJ q hq p z ha
  intro hz
  let M := ModuleCat.of (MvPolynomial V K) (MvPolynomial V K ⧸ P.ideal)
  have hz' := (finitePolynomialTorPaperIso (p+1) M).isZero_iff.mp hz
  letI : Subsingleton (PolynomialCoordinateTor.Tor (K := K) (V := V)
      (M := MvPolynomial V K ⧸ P.ideal) (p+1)) :=
    ModuleCat.isZero_iff_subsingleton.mp
      ((ModuleCat.restrictScalars (algebraMap K (MvPolynomial V K))).map_isZero hz')
  have hh : Subsingleton (PolynomialCoordinateTor.Homology (K := K) (V := V)
      (M := MvPolynomial V K ⧸ P.ideal) (p+1)) :=
    (PolynomialCoordinateTor.torIso (K := K) (V := V)
      (M := MvPolynomial V K ⧸ P.ideal) (p+1)).toLinearEquiv.symm.injective.subsingleton
  exact not_subsingleton _ hh

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.quotientTor_nonzero_of_ordinaryIdealBetti

end
end
end


end
