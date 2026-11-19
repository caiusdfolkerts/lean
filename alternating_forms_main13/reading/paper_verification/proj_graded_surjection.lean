module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions induced by surjective graded maps

Surjectivity on each homogeneous piece implies surjectivity on every
degree-zero localization.  The standard affine charts then show that the
induced morphism of actual projective schemes is a closed immersion.
The argument retains the scheme structure; no radical is taken.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal
open _root_.HomogeneousLocalization
open scoped HomogeneousIdeal

namespace PaperVerification

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The exact piecewise surjectivity needed by the Proj construction. -/
def GradedSurjective (f : 𝒜 →+*ᵍ ℬ) : Prop :=
  ∀ d b, b ∈ ℬ d → ∃ a, a ∈ 𝒜 d ∧ f a = b

theorem irrelevant_le_map_of_gradedSurjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : GradedSurjective f) : ℬ₊ ≤ 𝒜₊.map f := by
  apply _root_.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
  intro d hd b hb
  obtain ⟨a, ha, rfl⟩ := hf d b hb
  change f a ∈ (𝒜₊.map f).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  exact Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd ha)

/-- Homogeneous numerators lift without altering their degree or denominator. -/
theorem gradedAwayMap_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : GradedSurjective f) {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨r, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  obtain ⟨a, ha, rfl⟩ := hf (r • d) b hb
  exact ⟨Away.mk 𝒜 hs r a ha, Away.map_mk f s hs r a ha⟩

/-- The standard affine chart square for a Proj morphism is cartesian. -/
theorem gradedProjMap_chart_isPullback (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊ ≤ 𝒜₊.map f) {d : ℕ} (hd : 0 < d)
    (s : A) (hs : s ∈ 𝒜 d) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map f s)))
      (Proj.awayι ℬ (f s) (f.map_mem hs) hd)
      (Proj.awayι 𝒜 s hs hd) (Proj.map f hf) := by
  apply IsOpenImmersion.isPullback
  · exact Proj.awayι_comp_map f hf hd s hs
  · simp only [Proj.opensRange_awayι, Proj.map_preimage_basicOpen]

/-- A map surjective on every homogeneous piece gives a closed immersion of
Mathlib's projective schemes. -/
theorem isClosedImmersion_projMap_of_gradedSurjective
    (f : 𝒜 →+*ᵍ ℬ) (hf : GradedSurjective f) :
    IsClosedImmersion
      (Proj.map f (irrelevant_le_map_of_gradedSurjective f hf)) := by
  let h := irrelevant_le_map_of_gradedSurjective f hf
  apply IsZariskiLocalAtTarget.of_openCover (Proj.affineOpenCover 𝒜).openCover
  intro s
  let g := Spec.map (CommRingCat.ofHom (Away.map f s.2.1))
  have hg : IsClosedImmersion g :=
    IsClosedImmersion.spec_of_surjective _ (gradedAwayMap_surjective f hf s.2.2)
  let square := gradedProjMap_chart_isPullback f h s.1.2 s.2.1 s.2.2
  change IsClosedImmersion (pullback.snd (Proj.map f h)
    (Proj.awayι 𝒜 s.2.1 s.2.2 s.1.2))
  rw [← square.flip.isoPullback_inv_snd]
  exact IsClosedImmersion.comp _ _

end PaperVerification
