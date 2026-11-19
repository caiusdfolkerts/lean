module

public import PaperVerification.BarQuadraticPairing
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Actual diagonal bar homology and the multiplication-row quadratic quotient

Positivity makes the incoming top differential vanish. This file uses
Mathlib's genuine homology-to-cycles isomorphism, then the explicit finite
coefficient pairing, to identify every positive diagonal homology group
with the dual of the actual homogeneous quadratic quotient piece.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
open CategoryTheory CategoryTheory.Limits

namespace PaperVerification.BarDiagonalHomology

open WeightedBar DiagonalBarWords BarQuadraticPairing AugmentedAlgebraBasis
open QuadraticWordFunctionals

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ) (hpos : ∀ i,0<δ i)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

local notation "C" n => internalComplex ε B hunit hε δ hδ n
local notation "b" => (FreeAlgebraWordDegree.basis (K := K) (J := DegreeOne δ))

theorem internalKernel_eq_diagonalCycles (r : ℕ) :
    LinearMap.ker (internalDifferential B δ hδ r (r+1))=
      diagonalCycles B δ (r+1) := by
  ext z
  change internalDifferential B δ hδ r (r+1) z=0 ↔
    ReducedBarBasis.differential B z.val=0
  constructor
  · intro hz
    have he := congrArg Subtype.val hz
    exact neg_eq_zero.mp he
  · intro hz
    apply Subtype.ext
    change -ReducedBarBasis.differential B z.val=0
    rw [hz,neg_zero]

/-- Incoming boundaries vanish by actual internal degree, so the actual
categorical homology is precisely the actual outgoing kernel. -/
def homologyCyclesEquiv (r : ℕ) :
    ((C (r+1)).homology (r+1)) ≃ₗ[K] diagonalCycles B δ (r+1) := by
  let e : ((C (r+1)).homology (r+1)) ≅
      ModuleCat.of K (LinearMap.ker (((C (r+1)).d (r+1) r).hom)) :=
    ((C (r+1)).isoHomologyπ (r+2) (r+1) (by simp)
      (internalComplex_top_differential ε B hunit hε δ hδ hpos (r+1))).symm ≪≫
      (C (r+1)).cyclesIsoSc' (r+2) (r+1) r (by simp) (by simp) ≪≫
        ((C (r+1)).sc' (r+2) (r+1) r).moduleCatCyclesIso
  exact e.toLinearEquiv.trans (LinearEquiv.ofEq _ _ (by
    rw [internalComplex_d]
    exact internalKernel_eq_diagonalCycles B δ hδ r))

/-- The comparison is with an independently defined genuine algebra
quotient, and holds without a Koszulness hypothesis. -/
def homologyDualQuotientEquiv (r : ℕ) :
    ((C (r+1)).homology (r+1)) ≃ₗ[K]
      Module.Dual K (quotientPiece b (relationSpace B δ) (r+1)) :=
  (homologyCyclesEquiv ε B hunit hε δ hpos hδ r).trans
    (cyclesDualQuotientEquiv B δ hpos hδ r)

include hpos in
theorem diagonal_finrank_eq_quotient_finrank (r : ℕ) :
    Module.finrank K ((C (r+1)).homology (r+1))=
      Module.finrank K (quotientPiece b (relationSpace B δ) (r+1)) := by
  letI : Module.Finite K (degreeSpace b (r+1)) :=
    Module.Finite.of_basis (wordSpaceBasis (K := K) δ (r+1))
  letI : Module.Finite K (quotientPiece b (relationSpace B δ) (r+1)) :=
    Module.Finite.of_surjective (pieceMap b (relationSpace B δ) (r+1))
      (pieceMap_surjective b (relationSpace B δ) (r+1))
  exact (homologyDualQuotientEquiv ε B hunit hε δ hpos hδ r).finrank_eq.trans
    (Subspace.dual_finrank_eq)

end PaperVerification.BarDiagonalHomology
