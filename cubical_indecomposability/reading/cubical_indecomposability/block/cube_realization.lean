import cubical_indecomposability.block.face_realization

/-!
# The facets are combinatorial three-cubes

For every facet we construct an order isomorphism between its ordinary
geometric face poset and the face poset of the standard geometric cube.
The intermediate coordinate-face codes have three coordinates, each free
or fixed at either of its two endpoint values.  The empty face may be adjoined on both
sides without changing this notion of combinatorial equivalence.
-/

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Cubical.Cube

/-- The 27 finite codes are exactly the ordinary coordinate faces. -/
def cubeCodeEquiv : Fin 27 ≃ FaceCode 3 :=
  Equiv.ofBijective codeOfFin27 codeOfFin27_bijective

@[simp] theorem cubeCodeEquiv_apply (c : Fin 27) :
    cubeCodeEquiv c = codeOfFin27 c := rfl

theorem indexedFace_code_top (f : Fin 24) :
    indexedFace (codeFace f 0) = facet f := by
  rw [indexedFace_eq_hull, codeFace_top, facet_eq_hull]

theorem indexedFace_code_subset (f : Fin 24) (c : Fin 27) :
    indexedFace (codeFace f c) ⊆ facet f := by
  rw [← indexedFace_code_top f, indexedFace_subset_iff, codeFace_top]
  exact codeFace_subset_facet f c

/-- The actual geometric face named by a coordinate code inside a facet. -/
def cubeFaceMap (f : Fin 24) (c : FaceCode 3) :
    FaceType (facePolytope polytope (facet_isFace f)) :=
  ⟨indexedFace (codeFace f (cubeCodeEquiv.symm c)),
    facePolytope_isFace_of polytope (facet_isFace f)
      (indexedFace_isFace _) (indexedFace_code_subset f _)⟩

theorem cubeFaceMap_le_iff (f : Fin 24) (c d : FaceCode 3) :
    cubeFaceMap f c ≤ cubeFaceMap f d ↔ c ≤ d := by
  change indexedFace (codeFace f (cubeCodeEquiv.symm c)) ⊆
      indexedFace (codeFace f (cubeCodeEquiv.symm d)) ↔ c ≤ d
  rw [indexedFace_subset_iff, codeFace_le_iff]
  have hc : codeOfFin27 (cubeCodeEquiv.symm c) = c :=
    cubeCodeEquiv.apply_symm_apply c
  have hd : codeOfFin27 (cubeCodeEquiv.symm d) = d :=
    cubeCodeEquiv.apply_symm_apply d
  rw [hc, hd]

theorem cubeFaceMap_injective (f : Fin 24) : Function.Injective (cubeFaceMap f) := by
  intro c d h
  apply le_antisymm
  · exact (cubeFaceMap_le_iff f c d).mp h.le
  · exact (cubeFaceMap_le_iff f d c).mp h.ge

theorem cubeFaceMap_surjective (f : Fin 24) : Function.Surjective (cubeFaceMap f) := by
  intro F
  have hFP : polytope.IsFace F.val :=
    isFace_of_facePolytope polytope (facet_isFace f) F.property
  obtain ⟨i, hi⟩ := indexedFace_complete hFP
  have hif : indexedFace i ⊆ facet f := by
    rw [hi]
    simpa only [facePolytope_toSet] using
      face_subset_toSet (facePolytope polytope (facet_isFace f)) F.property
  have himask : faceMask i ⊆ facetLabels f := by
    rw [← indexedFace_code_top f] at hif
    have h := (indexedFace_subset_iff i (codeFace f 0)).mp hif
    simpa only [codeFace_top] using h
  obtain ⟨c, hci⟩ := codeFace_complete f i himask
  refine ⟨cubeCodeEquiv c, Subtype.ext ?_⟩
  change indexedFace (codeFace f (cubeCodeEquiv.symm (cubeCodeEquiv c))) = F.val
  rw [cubeCodeEquiv.symm_apply_apply, hci, hi]

/-- Exact order correspondence between coordinate codes and actual faces. -/
def cubeFaceOrderIso (f : Fin 24) :
    FaceCode 3 ≃o FaceType (facePolytope polytope (facet_isFace f)) where
  toEquiv := Equiv.ofBijective (cubeFaceMap f)
    ⟨cubeFaceMap_injective f, cubeFaceMap_surjective f⟩
  map_rel_iff' := fun {c d} => cubeFaceMap_le_iff f c d

/-- Every displayed facet has the face lattice of the standard three-cube. -/
def facetCubeOrderIso (f : Fin 24) :
    FaceType (facePolytope polytope (facet_isFace f)) ≃o
      FaceType (standardCube 3) :=
  (cubeFaceOrderIso f).symm.trans (cubeFacesOrderIso 3 (by decide)).symm

/-- The same equivalence including the empty face on both sides. -/
def facetCubeCompleteOrderIso (f : Fin 24) :
    Papers.Polytopes.CompleteFaceType (facePolytope polytope (facet_isFace f)) ≃o
      Papers.Polytopes.CompleteFaceType (standardCube 3) :=
  Papers.Polytopes.extendFaceOrderIso (facetCubeOrderIso f)

theorem facet_dimension (f : Fin 24) : faceDim (facet f) = 3 := by
  rw [← indexedFace_code_top f, indexedFace_dimension]
  exact congrArg Fin.val (codeFace_rank_zero f)

/-- Every geometric facet is one of the displayed 24 facets. -/
theorem facets_complete {F : Set (E 4)} (hF : polytope.IsFace F)
    (hdF : faceDim F + 1 = polytope.dim) : ∃ f, F = facet f := by
  obtain ⟨i, hi⟩ := indexedFace_complete hF
  have hrank : faceRank i = 3 := by
    apply Fin.ext
    have h := indexedFace_dimension i
    rw [hi] at h
    rw [polytope_dimension] at hdF
    omega
  obtain ⟨f, hfi⟩ := faceRank_three i hrank
  exact ⟨f, hi.symm.trans (hfi ▸ indexedFace_code_top f)⟩

/-- The ordinary geometric meaning of the paper's word “cubical”. -/
theorem polytope_isCubical : IsCubical polytope := by
  intro F hF hdF
  obtain ⟨f, rfl⟩ := facets_complete hF hdF
  rw [polytope_dimension]
  exact ⟨facetCubeOrderIso f⟩

end CubicalIndecomposability.Block
