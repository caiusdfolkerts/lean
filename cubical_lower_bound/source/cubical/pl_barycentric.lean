import differential_geometry.topology.simplicial_complex.realization.barycentric_realization
import differential_geometry.topology.piecewise_linear.star_complex
import cubical.pl_sphere_rigidity

/-!
# Piecewise affine equivalence of standard and barycentric realizations

The abstract face-chain realization of a simplicial complex has a
genuine piecewise affine homeomorphism to its original realization.
This is the bridge needed to recover rigidity of original vertex links
from the topology of their face-poset subdivisions.
-/

noncomputable section

namespace Cubical.PL

open Set Geometry
open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear
attribute [local instance] Classical.propDecidable

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- On geometric vertices, invert an injective labeling into its
standard coordinate vertex; values away from the vertices are irrelevant. -/
def standardVertexInverse (v : ι → E) (y : E) : ι → ℝ :=
  if h : ∃ i, v i = y then Pi.single h.choose 1 else 0

@[simp]
theorem standardVertexInverse_apply (v : ι → E) (hv : Function.Injective v) (i : ι) :
    standardVertexInverse v (v i) = Pi.single i 1 := by
  unfold standardVertexInverse
  rw [dif_pos ⟨i, rfl⟩]
  congr 1
  exact hv (Exists.choose_spec (⟨i, rfl⟩ : ∃ j, v j = v i))

/-- The standard realization and any faithful affine realization have
inverse simplicial vertex maps. -/
theorem standardRealization_glueIso (P : PreAbstractSimplicialComplex ι)
    (v : ι → E) (hv : Function.Injective v)
    (K : Geometry.SimplicialComplex ℝ E) (hfaces : K.faces = (P.map v).faces) :
    IsGlueIso (standardRealization P) K (vertexEvaluation v) (standardVertexInverse v) := by
  classical
  constructor
  · rintro r ⟨s, hs, rfl⟩
    have heq : (s.image (fun i => Pi.single i (1 : ℝ))).image (vertexEvaluation v) =
        s.image v := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro i _
      exact vertexEvaluation_single v i
    rw [heq, hfaces]
    exact ⟨s, hs, rfl⟩
  · intro t ht
    rw [hfaces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have heq : (s.image v).image (standardVertexInverse v) =
        s.image (fun i => Pi.single i (1 : ℝ)) := by
      rw [Finset.image_image]
      exact Finset.image_congr (fun i _ => standardVertexInverse_apply v hv i)
    rw [heq]
    exact ⟨s, hs, rfl⟩
  · rintro r ⟨s, hs, rfl⟩ x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [vertexEvaluation_single, standardVertexInverse_apply v hv]
  · intro t ht x hx
    rw [hfaces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [standardVertexInverse_apply v hv, vertexEvaluation_single]

/-- A faithful affine realization is piecewise affine homeomorphic to
the standard coordinate realization, with a piecewise affine inverse. -/
theorem exists_isPLHomeomorphOn_realization (P : PreAbstractSimplicialComplex ι)
    (v : ι → E) (hv : Function.Injective v)
    (K : Geometry.SimplicialComplex ℝ E) (hfaces : K.faces = (P.map v).faces) :
    ∃ f : (ι → ℝ) → E, IsPLHomeomorphOn f (standardRealization P).space K.space := by
  classical
  letI : Finite (standardRealization P).faces := (standardRealization_finite_faces P).to_subtype
  have hfinite : K.faces.Finite := by
    rw [hfaces]
    exact (Set.toFinite P.faces).image (fun s => s.image v)
  letI : Finite K.faces := hfinite.to_subtype
  exact ⟨_, (standardRealization_glueIso P v hv K hfaces).isPLHomeomorphOn⟩

/-- The abstract barycentric subdivision and the original abstract
simplicial complex have genuinely PL-equivalent realizations. -/
theorem exists_isPLHomeomorphOn_barycentric (P : PreAbstractSimplicialComplex ι) :
    ∃ f : (Finset ι → ℝ) → (ι → ℝ),
      IsPLHomeomorphOn f (standardRealization (abstractBarycentric P)).space
        (standardRealization P).space := by
  classical
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_realization (abstractBarycentric P)
    (standardFaceCentroid : Finset ι → ι → ℝ) standardFaceCentroid_injective
    (barycentricGeometricRealization P) (by
      ext s
      constructor <;> rintro ⟨C, hC, rfl⟩ <;> refine ⟨C, hC, ?_⟩ <;>
        ext y <;> simp only [Finset.mem_image, standardFaceCentroid])
  rw [barycentricGeometricRealization_space] at hf
  exact ⟨f, hf⟩

/-- Being a PL sphere is invariant under abstract barycentric
subdivision; neither direction assumes rigidity or a cycle condition. -/
theorem isPLSphere_barycentric_iff (P : PreAbstractSimplicialComplex ι) (n : ℕ) :
    IsPLSphere n (standardRealization (abstractBarycentric P)).space ↔
      IsPLSphere n (standardRealization P).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_barycentric P
  exact ⟨fun h => h.of_isPLHomeomorphOn hf, fun h => h.of_isPLHomeomorphOn hf.symm⟩

/-- Rigidity is obtained for the original simplicial graph when its
face-chain realization is a PL sphere. -/
theorem edgeGraph_genericallyRigid_of_barycentric_sphere
    (P : PreAbstractSimplicialComplex ι) {n : ℕ} (hn : 1 ≤ n)
    (hP : IsPLSphere (n + 1) (standardRealization (abstractBarycentric P)).space) :
    Cubical.Rigidity.GenericallyRigid
      (DifferentialGeometry.Topology.SimplicialComplex.edgeGraph (standardRealization P))
      (EuclideanSpace ℝ (Fin (n + 2))) := by
  letI : Finite (standardRealization P).faces := (standardRealization_finite_faces P).to_subtype
  exact sphere_edgeGraph_genericallyRigid (standardRealization P) hn
    ((isPLSphere_barycentric_iff P (n + 1)).mp hP)

end Cubical.PL
