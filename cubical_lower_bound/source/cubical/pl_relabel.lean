import cubical.pl_abstract

/-!
# Piecewise affine transport of finite abstract complexes

The vertex maps need only be inverse on vertices actually belonging to
the complexes.  Unused labels therefore do not impose artificial
restrictions on barycentric subdivision or link constructions.
-/

noncomputable section

namespace Cubical.PL

open Set Geometry
open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem standardRealization_vertexIso (P : PreAbstractSimplicialComplex ι)
    (Q : PreAbstractSimplicialComplex κ) (f : ι → κ) (g : κ → ι)
    (hf : ∀ s ∈ P.faces, s.image f ∈ Q.faces)
    (hg : ∀ t ∈ Q.faces, t.image g ∈ P.faces)
    (hgf : ∀ i, {i} ∈ P.faces → g (f i) = i)
    (hfg : ∀ j, {j} ∈ Q.faces → f (g j) = j) :
    IsGlueIso (standardRealization P) (standardRealization Q)
      (vertexEvaluation (fun i => standardVertex (f i)))
      (vertexEvaluation (fun j => standardVertex (g j))) := by
  classical
  constructor
  · rintro s' ⟨s, hs, rfl⟩
    refine ⟨s.image f, hf s hs, ?_⟩
    ext x
    simp only [Finset.mem_image, standardVertex, vertexEvaluation_single]
    aesop
  · rintro t' ⟨t, ht, rfl⟩
    refine ⟨t.image g, hg t ht, ?_⟩
    ext x
    simp only [Finset.mem_image, standardVertex, vertexEvaluation_single]
    aesop
  · rintro s' ⟨s, hs, rfl⟩ x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [vertexEvaluation_single, standardVertex]
    rw [hgf i
      ((P.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hi)
        (Finset.singleton_nonempty i))]
  · rintro t' ⟨t, ht, rfl⟩ x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    simp only [vertexEvaluation_single, standardVertex]
    rw [hfg j
      ((Q.isRelLowerSet_faces ht).2 (Finset.singleton_subset_iff.mpr hj)
        (Finset.singleton_nonempty j))]

theorem exists_isPLHomeomorphOn_vertexIso (P : PreAbstractSimplicialComplex ι)
    (Q : PreAbstractSimplicialComplex κ) (f : ι → κ) (g : κ → ι)
    (hf : ∀ s ∈ P.faces, s.image f ∈ Q.faces)
    (hg : ∀ t ∈ Q.faces, t.image g ∈ P.faces)
    (hgf : ∀ i, {i} ∈ P.faces → g (f i) = i)
    (hfg : ∀ j, {j} ∈ Q.faces → f (g j) = j) :
    ∃ F : (ι → ℝ) → (κ → ℝ),
      IsPLHomeomorphOn F (standardRealization P).space (standardRealization Q).space := by
  letI : Finite (standardRealization P).faces := (standardRealization_finite_faces P).to_subtype
  letI : Finite (standardRealization Q).faces := (standardRealization_finite_faces Q).to_subtype
  exact ⟨_, (standardRealization_vertexIso P Q f g hf hg hgf hfg).isPLHomeomorphOn⟩

theorem isPLSphere_iff_of_vertexIso (P : PreAbstractSimplicialComplex ι)
    (Q : PreAbstractSimplicialComplex κ) (f : ι → κ) (g : κ → ι)
    (hf : ∀ s ∈ P.faces, s.image f ∈ Q.faces)
    (hg : ∀ t ∈ Q.faces, t.image g ∈ P.faces)
    (hgf : ∀ i, {i} ∈ P.faces → g (f i) = i)
    (hfg : ∀ j, {j} ∈ Q.faces → f (g j) = j) (n : ℕ) :
    IsPLSphere n (standardRealization P).space ↔
      IsPLSphere n (standardRealization Q).space := by
  obtain ⟨F, hF⟩ := exists_isPLHomeomorphOn_vertexIso P Q f g hf hg hgf hfg
  exact ⟨fun h => h.of_isPLHomeomorphOn hF, fun h => h.of_isPLHomeomorphOn hF.symm⟩

end Cubical.PL
