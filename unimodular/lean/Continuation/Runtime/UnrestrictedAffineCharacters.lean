module

public import Continuation.Runtime.NonpointedSmoothSemigroup

/-!
# Unrestricted smooth invariant affine character charts

An actual smooth normal invariant affine subalgebra of the Laurent ring
is the character algebra of a coordinate cone. The selected coordinate
set may be proper or empty: no torus fixed point and no full-dimensional
cone are assumed. Saturation, finite generation and generation of the
original lattice are derived from the actual ring and function field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ToricCharacters

open PaperVerification.ToricGeometry
open scoped Classical

variable (k : Type*) [Field k] {n : ℕ}
    (A : Subalgebra k (AddMonoidAlgebra k (Lattice n)))
    (hA : IsCharacterStable k A.toSubmodule)
    [Algebra.Smooth k A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra k K]
    [Algebra (AddMonoidAlgebra k (Lattice n)) K]
    [IsScalarTower k (AddMonoidAlgebra k (Lattice n)) K]
    [IsFractionRing (AddMonoidAlgebra k (Lattice n)) K]
    [Algebra A K]

local instance unrestrictedAffineAlgebraSMul : SMul A K :=
  (inferInstance : Algebra A K).toSMul

variable [IsScalarTower A (AddMonoidAlgebra k (Lattice n)) K]
    [IsFractionRing A K]

include hA K in
/-- Every smooth normal invariant affine chart is a smooth cone chart in
the original character lattice, with all invertible directions retained. -/
theorem smooth_invariant_affineAlgebra_eq_coordinateCone_unrestricted :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)),
      A = monoidChartAlgebra k (coordinateConeMonoid b I) := by
  let S := affineExponentMonoid k A
  let e : AddMonoidAlgebra k S ≃ₐ[k] A := invariantAffineSemigroupEquiv k A hA
  letI : Algebra (AddMonoidAlgebra k S) K :=
    ((algebraMap A K).comp e.toRingEquiv.toRingHom).toAlgebra
  letI : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq (by
    intro r
    exact (IsScalarTower.algebraMap_apply k
      (AddMonoidAlgebra k (Lattice n)) K r).trans
      (IsScalarTower.algebraMap_apply A
        (AddMonoidAlgebra k (Lattice n)) K (algebraMap k A r)).symm)
  letI : IsScalarTower k (AddMonoidAlgebra k S) K :=
    IsScalarTower.of_algebraMap_eq (by
      intro r
      change algebraMap k K r = algebraMap A K (e (algebraMap k (AddMonoidAlgebra k S) r))
      rw [e.commutes,← IsScalarTower.algebraMap_apply k A K])
  letI : IsFractionRing (AddMonoidAlgebra k S) K :=
    IsFractionRing.of_ringEquiv_left e.toRingEquiv (fun _=>rfl)
  letI : IsDomain (AddMonoidAlgebra k S) :=
    Function.Injective.isDomain (algebraMap (AddMonoidAlgebra k S) K)
      (IsFractionRing.injective (AddMonoidAlgebra k S) K)
  letI : Algebra.Smooth k (AddMonoidAlgebra k S) := Algebra.Smooth.of_equiv e.symm
  have hfg : S.FG := affineExponentMonoid_finitelyGenerated k A hA
  have hgroup : AddSubgroup.closure (S : Set (Lattice n))=⊤ :=
    affineExponentMonoid_groupClosure k A hA K
      (IsFractionRing.injective (AddMonoidAlgebra k (Lattice n)) K)
  have hsat (x : Lattice n) (N : ℕ) (hN : 0 < N) (hx : N • x ∈ S) : x ∈ S :=
    affineExponentMonoid_saturated k A K
      (IsFractionRing.injective (AddMonoidAlgebra k (Lattice n)) K) x hN hx
  obtain ⟨b, I, hS⟩ := smooth_saturatedMonoid_eq_coordinateCone S hsat k hfg hgroup
  have hdim : Module.finrank ℤ (Lattice n) = n := by
    simpa [ToricGeometry.Lattice] using
      Module.finrank_eq_card_basis (Pi.basisFun ℤ (Fin n))
  let e : Fin (Module.finrank ℤ (Lattice n)) ≃ Fin n := finCongr hdim
  refine ⟨b.reindex e, I.image e, ?_⟩
  rw [coordinateConeMonoid_reindex]
  exact (invariantAffineAlgebra_eq_semigroup k A hA).trans
    (congrArg (monoidChartAlgebra k) hS)


end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.smooth_invariant_affineAlgebra_eq_coordinateCone_unrestricted
