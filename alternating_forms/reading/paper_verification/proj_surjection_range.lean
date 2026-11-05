module

public import PaperVerification.HomogeneousQuotientClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The image of an actual surjective graded Proj map

The image consists precisely of the relevant homogeneous prime ideals
containing the literal kernel. This provides the underlying closed sets
of the homogeneous-coordinate filtration without replacing its schemes
by zero loci or by sets of closed points.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

namespace PaperVerification

universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A graded map preserves every element of positive homogeneous degree. -/
theorem irrelevant_le_comap_graded (f : 𝒜 →+*ᵍ ℬ) :
    𝒜₊ ≤ ℬ₊.comap f := by
  apply _root_.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
  intro d hd a ha
  exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hd (f.map_mem ha)

/-- Surjectivity on rings identifies the actual image of the Proj map
with the homogeneous primes containing its kernel. -/
theorem range_projMap_of_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊ ≤ 𝒜₊.map f) (hs : Function.Surjective f)
    (p : ProjectiveSpectrum 𝒜) :
    p ∈ Set.range (Proj.map f hf) ↔ RingHom.ker f.toRingHom ≤ p.asHomogeneousIdeal.toIdeal := by
  constructor
  · rintro ⟨q, rfl⟩ a ha
    change f a ∈ q.asHomogeneousIdeal.toIdeal
    have hfa : f a = 0 := RingHom.mem_ker.mp ha
    exact hfa.symm ▸ Ideal.zero_mem _
  · intro hk
    have hback : (p.asHomogeneousIdeal.map f).comap f = p.asHomogeneousIdeal := by
      apply HomogeneousIdeal.ext
      change (p.asHomogeneousIdeal.toIdeal.map f.toRingHom).comap f.toRingHom = _
      rw [Ideal.comap_map_of_surjective' f.toRingHom hs, sup_eq_left.mpr hk]
    let q : ProjectiveSpectrum ℬ := {
      asHomogeneousIdeal := p.asHomogeneousIdeal.map f
      isPrime := Ideal.map_isPrime_of_surjective hs hk
      not_irrelevant_le := by
        intro h
        apply p.not_irrelevant_le
        rw [← hback]
        exact (irrelevant_le_comap_graded f).trans (HomogeneousIdeal.comap_mono f h) }
    refine ⟨q, ?_⟩
    apply ProjectiveSpectrum.ext
    exact hback

namespace HomogeneousQuotientProjective

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K ι : Type} [Field K]
    (I J : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (homogeneousSubmodule ι K))
    (hJ : J.IsHomogeneous (homogeneousSubmodule ι K))
    (hIJ : I ≤ J)

/-- Exact prime-ideal description of the accepted homogeneous quotient
closed immersion. -/
theorem quotientProjMap_range (p : ProjectiveSpectrum (grading I hI)) :
    p ∈ Set.range (quotientProjMap I J hI hJ hIJ) ↔
      J ≤ p.asHomogeneousIdeal.toIdeal.comap (Ideal.Quotient.mk I) := by
  rw [quotientProjMap, range_projMap_of_surjective _ _ (Ideal.Quotient.factor_surjective hIJ)]
  change RingHom.ker (Ideal.Quotient.factor hIJ) ≤ p.asHomogeneousIdeal.toIdeal ↔ _
  rw [Ideal.Quotient.factor_ker, Ideal.map_le_iff_le_comap]

end HomogeneousQuotientProjective
end PaperVerification
