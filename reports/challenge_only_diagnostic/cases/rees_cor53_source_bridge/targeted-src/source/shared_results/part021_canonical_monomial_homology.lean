module
public import graph_foundation.part014
public import shared_results.part021_closed_graph_ideal_rename

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.CanonicalMonomialHomology -/
section

/-! # Canonical ideal coordinates recover the literal monomial homology

The comparison is the identity on the original polynomial ideal and its
Koszul coordinates. Only the two proved descriptions of its ordinary
homogeneous submodule differ. No identification of the chosen finite
initial presentation with the supplied monomial generators is needed.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial FilteredHomology

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]

theorem monomialBasis_repr_coeff (B : Family V) (x : monomialIdeal K B)
    (a : {a : Exponent V // Contains B a}) :
    (monomialBasis B).repr x a = x.val.coeff a.val := by
  have h : (monomialBasis (k:=K) B).coord a =
      (MvPolynomial.lcoeff (R := K) a.val).comp ((monomialIdeal K B).subtype.restrictScalars K) := by
    apply (monomialBasis (k:=K) B).ext
    intro b
    simp only [Module.Basis.coord_apply,Module.Basis.repr_self,
      LinearMap.comp_apply,LinearMap.restrictScalars_apply,Submodule.subtype_apply,
      monomialBasis_val,MvPolynomial.lcoeff_apply,Finsupp.single_apply,coeff_monomial]
    by_cases h : b=a
    · subst b
      simp
    · have hv : b.val ≠ a.val := fun hv => h (Subtype.ext hv)
      simp [h,hv]
  exact LinearMap.congr_fun h x

theorem monomialCoefficientBasis_repr_coeff (B : Family V) (p : ℕ)
    (x : Set.powersetCard V p →₀ monomialIdeal K B) (a : MonomialIndex B p) :
    (monomialCoefficientBasis B p).repr x a = (x a.1).val.coeff a.2.val := by
  rw [monomialCoefficientBasis,Finsupp.basis_repr,monomialBasis_repr_coeff]

theorem ordinaryMonomialPiece_mem_ambient (B : Family V) (q p : ℕ)
    (x : Set.powersetCard V p →₀ monomialIdeal K B) :
    x ∈ ordinaryMonomialPiece (k := K) B q p ↔
      idealCoordinatesToAmbient (monomialIdeal K B) p x ∈
        Grading.Piece (quotientCoefficientBasis (k:=K) (∅ : Family V) p)
          (fun b => (quotientDegree b).degree) q := by
  rw [ordinaryMonomialPiece,Grading.mem_piece,Grading.mem_piece]
  constructor
  · intro hx a ha
    rw [idealCoordinatesToAmbient_repr] at ha
    have haB : Contains B a.2.val :=
      (mem_monomialIdeal_iff B (x a.1).val).mp (x a.1).property
        a.2.val (mem_support_iff.mpr ha)
    have h := hx ⟨a.1,⟨a.2.val,haB⟩⟩
      (by simpa only [monomialCoefficientBasis_repr_coeff] using ha)
    exact h
  · intro hx a ha
    have h := hx ⟨a.1,⟨a.2.val,emptyFamily_allowed a.2.val⟩⟩
      (by simpa only [idealCoordinatesToAmbient_repr,monomialCoefficientBasis_repr_coeff] using ha)
    exact h

variable (m : MonomialOrder V) (B : Family V)
  (hB : (monomialIdeal K B).IsHomogeneous
    (weightedHomogeneousSubmodule K (fun _ : V => (1:ℕ))))

def canonicalMonomialPieceEquiv (q p : ℕ) :
    actualIdealOrdinaryPiece (canonicalQuotientGroebnerData m (monomialIdeal K B)) q p ≃ₗ[K]
      ordinaryMonomialPiece (k := K) B q p :=
  LinearEquiv.ofEq _ _ (by
    ext x
    rw [actualIdealOrdinaryPiece_mem_iff _ hB,ordinaryMonomialPiece_mem_ambient]
    rfl)

/-- The identity on actual ideal coefficients intertwines the actual
variable-action Koszul differentials in all degrees, including degree zero. -/
def canonicalMonomialHomologyEquiv (q p : ℕ) :
    actualIdealOrdinaryHomology (canonicalQuotientGroebnerData m (monomialIdeal K B)) hB q p ≃ₗ[K]
      ordinaryMonomialHomology (k := K) B q p := by
  apply threeTermHomologyEquiv (R := K)
    (X := actualIdealOrdinaryPiece (canonicalQuotientGroebnerData m (monomialIdeal K B)) q (p+1))
    (Y := actualIdealOrdinaryPiece (canonicalQuotientGroebnerData m (monomialIdeal K B)) q p)
    (Z := actualIdealOrdinaryPiece (canonicalQuotientGroebnerData m (monomialIdeal K B)) q p.pred)
    (X' := ordinaryMonomialPiece (k := K) B q (p+1))
    (Y' := ordinaryMonomialPiece (k := K) B q p)
    (Z' := ordinaryMonomialPiece (k := K) B q p.pred)
    (actualIdealOrdinaryDifferential _ hB q p) (actualIdealOrdinaryPrevious _ hB q p)
    (actualIdealOrdinaryDifferential_comp _ hB q p)
    (ordinaryMonomialDifferential (k := K) B q p) (ordinaryMonomialPrevious (k := K) B q p)
    (ordinaryMonomialDifferential_comp (k := K) B q p)
    (canonicalMonomialPieceEquiv (K := K) m B hB q (p+1))
    (canonicalMonomialPieceEquiv (K := K) m B hB q p)
    (canonicalMonomialPieceEquiv (K := K) m B hB q p.pred)
  · intro x
    apply Subtype.ext
    rfl
  · intro x
    apply Subtype.ext
    cases p <;> rfl

theorem canonicalMonomialBettiNumber_eq (q p : ℕ) :
    ordinaryIdealBettiNumber (canonicalQuotientGroebnerData m (monomialIdeal K B)) hB p q =
      ordinaryMonomialBettiNumber (k:=K) B q p := by
  rw [ordinaryIdealBettiNumber_eq_finrank,ordinaryMonomialBettiNumber]
  exact (canonicalMonomialHomologyEquiv (K := K) m B hB q p).finrank_eq

end FourPapers.Sublattice

end
end
end


end
