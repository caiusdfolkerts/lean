module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Dense affine charts and genuine scheme rationality

These general lemmas use Mathlib's actual projective spectrum, partial
scheme isomorphisms, and `Scheme.IsRationalOver`.  Density of a nonempty
basic open in the projective spectrum of a domain is proved from the
homogeneous zero prime, rather than taken as an application hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory

universe u

section ProjectiveDensity

variable {A σ : Type u} [CommRing A] [IsDomain A]
  [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A nonempty basic open of the actual projective spectrum of a domain
is dense.  The proof constructs and uses the homogeneous zero prime. -/
theorem projective_basicOpen_dense_of_nonempty (f : A)
    (h : (Proj.basicOpen 𝒜 f : Set (Proj 𝒜)).Nonempty) :
    Dense (Proj.basicOpen 𝒜 f : Set (Proj 𝒜)) := by
  obtain ⟨x,hx⟩ := h
  let η : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := by simpa only [HomogeneousIdeal.toIdeal_bot] using
        (inferInstance : (⊥ : Ideal A).IsPrime)
      not_irrelevant_le := fun hi => x.not_irrelevant_le (hi.trans bot_le) }
  have hηdense : Dense ({η} : Set (ProjectiveSpectrum 𝒜)) := by
    rw [dense_iff_closure_eq, ← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    change ProjectiveSpectrum.zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ
    exact ProjectiveSpectrum.zeroLocus_bot 𝒜
  apply hηdense.mono
  intro y hy
  obtain rfl := Set.mem_singleton_iff.mp hy
  change f ∉ (⊥ : HomogeneousIdeal 𝒜)
  intro hf
  have hf0 : f = 0 := Ideal.mem_bot.mp hf
  apply hx
  rw [hf0]
  exact x.asHomogeneousIdeal.toIdeal.zero_mem

end ProjectiveDensity

section Birationality

variable {S X Y : Scheme.{u}}

theorem scheme_birationalOver_of_iso (sX : X ⟶ S) (sY : Y ⟶ S)
    (e : X ≅ Y) (h : e.hom ≫ sY = sX) : Scheme.BirationalOver sX sY := by
  refine ⟨Scheme.PartialIso.ofIso e, ?_⟩
  simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso, h]

/-- The actual birational correspondence with the displayed affine space.
Keeping its index explicit lets finite-dimensional rationality be stated
without relying on the more permissive `IsRationalOver` class. -/
theorem scheme_birationalOver_affine_of_dense_chart
    (sX : X ⟶ S) (U : X.Opens) (hU : Dense (U : Set X)) (n : Type u)
    (e : U.toScheme ≅ 𝔸(n; S))
    (he : e.hom ≫ (𝔸(n; S) ↘ S) = U.ι ≫ sX) :
    Scheme.BirationalOver sX (𝔸(n; S) ↘ S) :=
  (U.birationalOver_of_dense sX hU).symm.trans
    (scheme_birationalOver_of_iso (U.ι ≫ sX) (𝔸(n; S) ↘ S) e he)

/-- A dense open with an affine-space isomorphism over the base yields
the standard scheme-theoretic rationality property. -/
theorem scheme_isRationalOver_of_dense_affine_chart
    (sX : X ⟶ S) (U : X.Opens) (hU : Dense (U : Set X)) (n : Type u)
    (e : U.toScheme ≅ 𝔸(n; S))
    (he : e.hom ≫ (𝔸(n; S) ↘ S) = U.ι ≫ sX) :
    Scheme.IsRationalOver sX := by
  exact ⟨n, scheme_birationalOver_affine_of_dense_chart sX U hU n e he⟩

end Birationality

end PaperVerification.AlternatingForms
