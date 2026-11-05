import cubical.pl_abstract
import differential_geometry.topology.piecewise_linear.link_euclidean

/-! Faithful affine images preserve links as actual PL realizations. -/

noncomputable section

namespace Bier

open Set Geometry
open DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [DecidableEq E] [DecidableEq F]

theorem exists_linear_image_glueIso (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (f : E →ₗ[ℝ] F) (hf : Set.InjOn f K.space) :
    ∃ L : Geometry.SimplicialComplex ℝ F, L.faces.Finite ∧ L.space = f '' K.space ∧
      IsGlueIso K L f (Function.invFunOn f K.space) := by
  classical
  obtain ⟨L, hfin, hspace, hfaces, hpl⟩ :=
    exists_simplicialComplex_image_of_affineOn_faces K (f := f)
      (fun _ _ => ⟨f.toAffineMap, fun _ _ => rfl⟩) hf
  refine ⟨L, hfin, hspace, ?_⟩
  have hvert : ∀ s ∈ K.faces, ∀ v ∈ s, v ∈ K.space := fun s hs v hv =>
    K.convexHull_subset_space hs (subset_convexHull ℝ _ hv)
  have hleft : ∀ s ∈ K.faces, ∀ v ∈ s, Function.invFunOn f K.space (f v) = v :=
    fun s hs v hv => hf.leftInvOn_invFunOn (hvert s hs v hv)
  constructor
  · intro s hs
    exact (hfaces _).mpr ⟨s, hs, rfl⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := (hfaces _).mp ht
    rw [Finset.image_image]
    have heq : s.image (Function.invFunOn f K.space ∘ f) = s := by
      conv_rhs => rw [← Finset.image_id (s := s)]
      exact Finset.image_congr (fun v hv => hleft s hs v hv)
    rwa [heq]
  · exact hleft
  · intro t ht u hu
    obtain ⟨s, hs, rfl⟩ := (hfaces _).mp ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [hleft s hs v hv]

end Bier
