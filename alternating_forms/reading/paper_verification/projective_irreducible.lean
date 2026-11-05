module

public import PaperVerification.AlternatingFormsSectionFourGeometry

/-!
# Irreducibility of the actual projective spectrum of a domain

The homogeneous zero prime is an actual generic point. This gives the
irreducibility needed by the intrinsic complex-manifold construction,
without replacing the projective scheme by its affine coordinate model.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory

universe u

variable {A σ : Type u} [CommRing A] [IsDomain A]
  [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A nonempty `Proj` of a domain has a dense generic point. -/
theorem projective_irreducibleSpace_of_domain [Nonempty (Proj 𝒜)] :
    IrreducibleSpace (Proj 𝒜) := by
  letI : Nonempty (ProjectiveSpectrum 𝒜) := by
    change Nonempty (Proj 𝒜)
    infer_instance
  let x : ProjectiveSpectrum 𝒜 := Classical.choice inferInstance
  let η : ProjectiveSpectrum 𝒜 := {
    asHomogeneousIdeal := ⊥
    isPrime := by simpa only [HomogeneousIdeal.toIdeal_bot] using
      (inferInstance : (⊥ : Ideal A).IsPrime)
    not_irrelevant_le := fun hi => x.not_irrelevant_le (hi.trans bot_le) }
  have hη : closure ({η} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    change ProjectiveSpectrum.zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ
    exact ProjectiveSpectrum.zeroLocus_bot 𝒜
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← hη]
  exact isIrreducible_singleton.closure

variable {K : Type} [Field K] [CharZero K]

/-- Prime degeneration and the actual coordinate-plane witness establish
irreducibility in the complete odd-dimensional range. -/
theorem canonicalOdd_isotropicProj_irreducible (k t : ℕ) (hs : t+2 ≤ k+1) :
    IrreducibleSpace
      (Proj (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))) := by
  letI := canonicalOdd_isotropicProj_nonempty (K := K) k t hs
  letI := odd_isotropicPluckerIdeal_isPrime (K := K) k t hs
  exact projective_irreducibleSpace_of_domain _

end PaperVerification.AlternatingForms
