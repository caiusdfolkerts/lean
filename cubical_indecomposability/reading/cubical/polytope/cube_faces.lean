import cubical.polytope.cube_face_affine
import cubical.polytope.facet_geometry
import cubical.cube_face_code

/-! # The geometric cube face lattice is the coordinate face lattice

The construction uses actual exposing linear functionals. Thus the
coordinate descriptions classify geometric faces, not merely subsets
that have been declared to be faces.
-/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Cube

def cubeCoordinateWeight : FaceCoordinate → ℝ
  | .free => 0
  | .fixed b => if b then 1 else -1

def cubeFaceFunctional {d : ℕ} (p : FaceCode d) : E d →L[ℝ] ℝ :=
  ∑ i, cubeCoordinateWeight (p i) • EuclideanSpace.proj i

@[simp] theorem cubeFaceFunctional_apply {d : ℕ} (p : FaceCode d) (x : E d) :
    cubeFaceFunctional p x = ∑ i, cubeCoordinateWeight (p i) * x i := by
  simp [cubeFaceFunctional]

theorem cubeFaceFunctional_term_le {d : ℕ} (p : FaceCode d)
    (s : Fin d → Bool) (i : Fin d) :
    cubeCoordinateWeight (p i) * vertIper s i ≤
      cubeCoordinateWeight (p i) * vertIper (baseCode p) i := by
  cases hp : p i with
  | free => simp [cubeCoordinateWeight, hp]
  | fixed b =>
    cases b <;> cases hs : s i <;>
      simp [cubeCoordinateWeight, hp, baseCode, hs]

theorem cubeFaceFunctional_term_eq_iff {d : ℕ} (p : FaceCode d)
    (s : Fin d → Bool) (i : Fin d) :
    cubeCoordinateWeight (p i) * vertIper s i =
      cubeCoordinateWeight (p i) * vertIper (baseCode p) i ↔
        p i = .free ∨ p i = .fixed (s i) := by
  cases hp : p i with
  | free => simp [cubeCoordinateWeight, hp]
  | fixed b =>
    cases b <;> cases hs : s i <;>
      norm_num [cubeCoordinateWeight, hp, baseCode, hs]

theorem cubeFaceFunctional_le {d : ℕ} (p : FaceCode d) (s : Fin d → Bool) :
    cubeFaceFunctional p (vertIper s) ≤ cubeFaceFunctional p (vertIper (baseCode p)) := by
  simp only [cubeFaceFunctional_apply]
  exact Finset.sum_le_sum (fun i _ => cubeFaceFunctional_term_le p s i)

theorem cubeFaceFunctional_eq_iff {d : ℕ} (p : FaceCode d) (s : Fin d → Bool) :
    cubeFaceFunctional p (vertIper s) = cubeFaceFunctional p (vertIper (baseCode p)) ↔
      Matches p s := by
  simp only [cubeFaceFunctional_apply]
  rw [Finset.sum_eq_sum_iff_of_le (fun i _ => cubeFaceFunctional_term_le p s i)]
  simp only [Finset.mem_univ, forall_true_left, cubeFaceFunctional_term_eq_iff, Matches]

def coordinateCubeFace {d : ℕ} (p : FaceCode d) : FaceType (standardCube d) := by
  let l := cubeFaceFunctional p
  have hmax : ∀ x ∈ (standardCube d).toSet, l x ≤ l (vertIper (baseCode p)) := by
    apply le_su_toSet
    intro x hx
    obtain ⟨s, rfl⟩ := mem_verticiIper.mp hx
    exact cubeFaceFunctional_le p s
  exact ⟨l.toExposed (standardCube d).toSet,
    ContinuousLinearMap.toExposed.isExposed,
    ⟨vertIper (baseCode p), subset_convexHull ℝ _ (mem_verticiIper.mpr ⟨_, rfl⟩), hmax⟩⟩

@[simp] theorem mem_coordinateCubeFace {d : ℕ} (p : FaceCode d) (s : Fin d → Bool) :
    vertIper s ∈ (coordinateCubeFace p).val ↔ Matches p s := by
  constructor
  · intro h
    apply (cubeFaceFunctional_eq_iff p s).mp
    exact le_antisymm (cubeFaceFunctional_le p s)
      (h.2 _ (subset_convexHull ℝ _ (mem_verticiIper.mpr ⟨_, rfl⟩)))
  · intro h
    refine ⟨subset_convexHull ℝ _ (mem_verticiIper.mpr ⟨_, rfl⟩), ?_⟩
    change ∀ x ∈ (standardCube d).toSet,
      cubeFaceFunctional p x ≤ cubeFaceFunctional p (vertIper s)
    rw [(cubeFaceFunctional_eq_iff p s).mpr h]
    apply le_su_toSet
    intro x hx
    obtain ⟨t, rfl⟩ := mem_verticiIper.mp hx
    exact cubeFaceFunctional_le p t

theorem coordinateCubeFace_injective (d : ℕ) :
    Function.Injective (coordinateCubeFace (d := d)) := by
  intro p q h
  apply (faceCode_eq_iff p q).mpr
  intro s
  rw [← mem_coordinateCubeFace, ← mem_coordinateCubeFace, h]

theorem coordinateCubeFace_surjective (d : ℕ) (hd : 1 ≤ d) :
    Function.Surjective (coordinateCubeFace (d := d)) := by
  intro F
  obtain ⟨v, hv⟩ := (facePolytope (standardCube d) F.property).vertices_nonempty
  obtain ⟨s, rfl⟩ := mem_verticiIper.mp (Finset.mem_filter.mp hv).1
  have hs := (Finset.mem_filter.mp hv).2
  refine ⟨faceCode s (iperFaceFree F.val s), Subtype.ext ?_⟩
  apply (face_eq_iff_vertices_eq (standardCube d)
    (coordinateCubeFace _).property F.property).mpr
  intro x hx
  obtain ⟨t, rfl⟩ := mem_verticiIper.mp hx
  rw [mem_coordinateCubeFace, matches_faceCode_iff]
  exact (vertIper_mem_face_iff d hd F.property hs t).symm

theorem coordinateCubeFace_le_iff {d : ℕ} (p q : FaceCode d) :
    coordinateCubeFace p ≤ coordinateCubeFace q ↔ p ≤ q := by
  constructor
  · intro h
    apply le_of_matches
    intro s hs
    exact (mem_coordinateCubeFace q s).mp (h ((mem_coordinateCubeFace p s).mpr hs))
  · intro h
    apply (faceVertices_subset_iff (standardCube d)
      (coordinateCubeFace p).property (coordinateCubeFace q).property).mp
    intro v hv
    obtain ⟨s, hs⟩ := mem_verticiIper.mp v.property
    rw [mem_faceVertices] at hv ⊢
    rw [← hs, mem_coordinateCubeFace] at hv ⊢
    exact matches_of_le h hv

/-- A face-order equivalence proved from the convex geometry of the cube. -/
def cubeFacesOrderIso (d : ℕ) (hd : 1 ≤ d) :
    FaceType (standardCube d) ≃o FaceCode d :=
  ({ toEquiv := Equiv.ofBijective coordinateCubeFace
       ⟨coordinateCubeFace_injective d, coordinateCubeFace_surjective d hd⟩
     map_rel_iff' := fun {p q} => coordinateCubeFace_le_iff p q } :
      FaceCode d ≃o FaceType (standardCube d)).symm

theorem coordinateCubeFace_dim (d : ℕ) (hd : 1 ≤ d) (p : FaceCode d) :
    faceDim (coordinateCubeFace p).val = (freeCoords p).card := by
  let F := coordinateCubeFace p
  let s := baseCode p
  let A := iperFaceFree F.val s
  have hs : vertIper s ∈ F.val := (mem_coordinateCubeFace p s).mpr (baseCode_matches p)
  have hcode : faceCode s A = p := by
    apply (faceCode_eq_iff _ _).mpr
    intro t
    rw [matches_faceCode_iff, ← mem_coordinateCubeFace]
    exact (vertIper_mem_face_iff d hd F.property hs t).symm
  have hfree : A = freeCoords p := by rw [← hcode, freeCoords_faceCode]
  exact (ipercubo_face_free_card d hd F.property hs).symm.trans (congrArg Finset.card hfree)

theorem cubeFacesOrderIso_dim (d : ℕ) (hd : 1 ≤ d)
    (F : FaceType (standardCube d)) :
    faceDim F.val = (freeCoords (cubeFacesOrderIso d hd F)).card := by
  have h := coordinateCubeFace_dim d hd (cubeFacesOrderIso d hd F)
  have hF : coordinateCubeFace (cubeFacesOrderIso d hd F) = F :=
    (cubeFacesOrderIso d hd).symm_apply_apply F
  rwa [hF] at h

end LeanEval.Geometry.PlatonicClassification
