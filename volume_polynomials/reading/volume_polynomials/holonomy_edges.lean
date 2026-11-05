module

public import VolumePolynomials.HolonomySeries
public import VolumePolynomials.AffineShapeTransfer
public import Mathlib.Data.Set.Finite.Range

@[expose] public section
noncomputable section

open Set

namespace VolumePolynomials.Holonomy

/-- An exposed edge means the entire exposed face of a nonzero linear
functional is a nondegenerate closed segment. -/
def IsExposedEdge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K F : Set E) : Prop :=
  ∃ l : E →L[ℝ] ℝ, l ≠ 0 ∧ F = l.toExposed K ∧
    ∃ a v : E, v ≠ 0 ∧
      F = {x | ∃ t : Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), x = a + (t : ℝ) • v}

theorem exposed_affine_image (l : Plane →L[ℝ] ℝ)
    (f : Plane →L[ℝ] ThreeSpace) (g : ThreeSpace →L[ℝ] Plane)
    (hgf : Function.LeftInverse g f) (v : ThreeSpace) (S : Set Plane) :
    (l.comp g).toExposed ((fun x => v + f x) '' S) =
      (fun x => v + f x) '' l.toExposed S := by
  first
  | ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro z hz
      have h := hmax (v + f z) ⟨z, hz, rfl⟩
      simpa only [ContinuousLinearMap.comp_apply, map_add, hgf z, hgf x,
        add_le_add_iff_left] using h
    · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      simpa only [ContinuousLinearMap.comp_apply, map_add, hgf z, hgf x,
        add_le_add_iff_left] using hmax z hz

theorem IsExposedEdge.affine_image {S R : Set Plane} (hR : IsExposedEdge S R)
    (f : Plane →L[ℝ] ThreeSpace) (g : ThreeSpace →L[ℝ] Plane)
    (hgf : Function.LeftInverse g f) (v : ThreeSpace) :
    IsExposedEdge ((fun x => v + f x) '' S) ((fun x => v + f x) '' R) := by
  first
  | obtain ⟨l, hl, hRl, a, u, hu, hsegment⟩ := hR
    refine ⟨l.comp g, ?_, ?_, v + f a, f u, ?_, ?_⟩
    · intro hz
      apply hl
      apply ContinuousLinearMap.ext
      intro x
      have h : (l.comp g) (f x) = 0 := by
        simp only [hz, ContinuousLinearMap.zero_apply]
      simpa only [ContinuousLinearMap.comp_apply, hgf x, ContinuousLinearMap.zero_apply] using h
    · rw [hRl, exposed_affine_image l f g hgf v S]
    · intro hz
      exact hu (hgf.injective (hz.trans (map_zero f).symm))
    · rw [hsegment]
      ext y
      constructor
      · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, by simp only [map_add, map_smul, add_assoc]⟩
      · rintro ⟨t, rfl⟩
        exact ⟨a + (t : ℝ) • u, ⟨t, rfl⟩,
          by simp only [map_add, map_smul, add_assoc]⟩

/-- The displayed exposed faces are pairwise different; this is an actual
infinite family of edges, not merely infinitely many normal descriptions. -/
theorem forcedBody_exposed_faces_injective (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    Function.Injective (fun j : ℕ =>
      (orbitNormal lam j).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ))) := by
  first
  | obtain ⟨a, ha⟩ := forcedBody_exposed_faces lam hlam₀ hlam₁
    intro i j hij
    change (orbitNormal lam i).toExposed (forcedBody lam hlam₀.le hlam₁ : Set Plane) =
      (orbitNormal lam j).toExposed (forcedBody lam hlam₀.le hlam₁ : Set Plane) at hij
    by_contra hne
    have hp : a i + (1 / 2 : ℝ) • weightedOrbit lam i ∈
        (orbitNormal lam i).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) := by
      rw [ha i]
      exact ⟨⟨1 / 2, ⟨by norm_num, le_rfl⟩⟩, rfl⟩
    have hm : a i + (-(1 / 2) : ℝ) • weightedOrbit lam i ∈
        (orbitNormal lam i).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) := by
      rw [ha i]
      exact ⟨⟨-(1 / 2), ⟨le_rfl, by norm_num⟩⟩, rfl⟩
    rw [hij] at hp hm
    have heq : orbitNormal lam j (a i + (1 / 2 : ℝ) • weightedOrbit lam i) =
        orbitNormal lam j (a i + (-(1 / 2) : ℝ) • weightedOrbit lam i) :=
      (hm.2 _ hp.1).antisymm (hp.2 _ hm.1)
    simp only [map_add, map_smul, smul_eq_mul] at heq
    have hz : orbitNormal lam j (weightedOrbit lam i) = 0 := by linarith
    exact weightedOrbit_nonparallel lam hlam₀ j i (Ne.symm hne) hz

theorem forcedBody_infinitely_many_exposed_edges
    (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    Set.Infinite {F : Set (ℝ × ℝ) |
      IsExposedEdge (forcedBody lam hlam₀.le hlam₁) F} := by
  first
  | obtain ⟨a, ha⟩ := forcedBody_exposed_faces lam hlam₀ hlam₁
    apply (Set.infinite_range_of_injective
      (forcedBody_exposed_faces_injective lam hlam₀ hlam₁)).mono
    rintro F ⟨j, rfl⟩
    refine ⟨orbitNormal lam j, ?_, rfl, a j, weightedOrbit lam j,
      weightedOrbit_ne_zero lam hlam₀ j, ha j⟩
    intro hz
    have hp := orbitNormal_positive_direction lam hlam₀ j
    simpa [hz] using hp

/-- Infinite exposed edges persist in every actual affine realization, with
the support functional extended to three-space using the proved left inverse. -/
theorem affineCopy_infinitely_many_exposed_edges
    (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    {T : Set ThreeSpace} (hT : AffineCopy (forcedBody lam hlam₀.le hlam₁) T) :
    Set.Infinite {R : Set ThreeSpace | IsExposedEdge T R} := by
  first
  | obtain ⟨v, f, g, hgf, hT⟩ :=
      (affineCopy_iff_exists_linear_leftInverse _ _).mp hT
    let F : Plane → ThreeSpace := fun x => v + f x
    have hF : Function.Injective F := by
      intro x y hxy
      exact hgf.injective (add_left_cancel hxy)
    have hTF : T = F '' (forcedBody lam hlam₀.le hlam₁ : Set Plane) := by
      rw [hT, ← Set.image_vadd, Set.image_image]
      rfl
    have hImage : Function.Injective (fun R : Set Plane => F '' R) := by
      intro R Q hRQ
      have h := congrArg (Set.preimage F) hRQ
      simpa only [Set.preimage_image_eq _ hF] using h
    apply ((forcedBody_infinitely_many_exposed_edges lam hlam₀ hlam₁).image hImage.injOn).mono
    rintro R ⟨Q, hQ, rfl⟩
    rw [hTF]
    exact IsExposedEdge.affine_image hQ f g hgf v


end VolumePolynomials.Holonomy
