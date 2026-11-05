import cubical.polytope.cube_face_counts
import cubical.polytope.affine_face_order

/-! # Every geometric cube face is affinely a standard cube -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

def cubeFaceLinear {d : ℕ} (A : Finset (Fin d)) : E A.card →ₗ[ℝ] E d where
  toFun x := (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun i => if hi : i ∈ A then x (A.equivFin ⟨i, hi⟩) else 0)
  map_add' x y := by
    ext i
    by_cases hi : i ∈ A <;> simp [hi]
  map_smul' r x := by
    ext i
    by_cases hi : i ∈ A <;> simp [hi]

@[simp] theorem cubeFaceLinear_apply {d : ℕ} (A : Finset (Fin d))
    (x : E A.card) (i : Fin d) :
    cubeFaceLinear A x i = if hi : i ∈ A then x (A.equivFin ⟨i, hi⟩) else 0 := by
  rfl

def cubeFaceProjection {d : ℕ} (A : Finset (Fin d)) : E d →ₗ[ℝ] E A.card where
  toFun y := (EuclideanSpace.equiv (Fin A.card) ℝ).symm
    (fun j => y (A.equivFin.symm j).val)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp] theorem cubeFaceProjection_apply {d : ℕ} (A : Finset (Fin d))
    (y : E d) (j : Fin A.card) :
    cubeFaceProjection A y j = y (A.equivFin.symm j).val := rfl

def cubeFaceOffset {d : ℕ} (s : Fin d → Bool) (A : Finset (Fin d)) : E d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun i => if i ∈ A then 0 else vertIper s i)

def cubeFaceInsertion {d : ℕ} (s : Fin d → Bool) (A : Finset (Fin d)) :
    E A.card →ᵃ[ℝ] E d :=
  (cubeFaceLinear A).toAffineMap + AffineMap.const ℝ (E A.card) (cubeFaceOffset s A)

@[simp] theorem cubeFaceInsertion_apply {d : ℕ} (s : Fin d → Bool)
    (A : Finset (Fin d)) (x : E A.card) (i : Fin d) :
    cubeFaceInsertion s A x i =
      if hi : i ∈ A then x (A.equivFin ⟨i, hi⟩) else vertIper s i := by
  by_cases hi : i ∈ A <;> simp [cubeFaceInsertion, cubeFaceOffset, hi]

theorem cubeFaceProjection_insertion {d : ℕ} (s : Fin d → Bool)
    (A : Finset (Fin d)) (x : E A.card) :
    cubeFaceProjection A (cubeFaceInsertion s A x) = x := by
  ext j
  rw [cubeFaceProjection_apply, cubeFaceInsertion_apply,
    dif_pos (A.equivFin.symm j).property]
  simp

def cubeCodeInsertion {d : ℕ} (s : Fin d → Bool) (A : Finset (Fin d))
    (t : Fin A.card → Bool) : Fin d → Bool :=
  fun i => if hi : i ∈ A then t (A.equivFin ⟨i, hi⟩) else s i

theorem cubeFaceInsertion_vertex {d : ℕ} (s : Fin d → Bool)
    (A : Finset (Fin d)) (t : Fin A.card → Bool) :
    cubeFaceInsertion s A (vertIper t) = vertIper (cubeCodeInsertion s A t) := by
  ext i
  by_cases hi : i ∈ A <;> simp [cubeCodeInsertion, hi]

theorem cubeFaceInsertion_restrict_vertex {d : ℕ} (s u : Fin d → Bool)
    (A : Finset (Fin d)) (hu : u ∈ Cubical.Cube.FaceAt s A) :
    cubeFaceInsertion s A (vertIper (fun j => u (A.equivFin.symm j).val)) = vertIper u := by
  ext i
  by_cases hi : i ∈ A
  · simp [hi]
  · simp [hi, hu i hi]

theorem cubeFaceInsertion_image_vertices (d : ℕ) (hd : 1 ≤ d)
    {F : Set (E d)} (hF : (standardCube d).IsFace F)
    (s : Fin d → Bool) (hs : vertIper s ∈ F) :
    cubeFaceInsertion s (iperFaceFree F s) ''
      ((standardCube (iperFaceFree F s).card).vertices : Set (E (iperFaceFree F s).card)) =
      ((facePolytope (standardCube d) hF).vertices : Set (E d)) := by
  let A := iperFaceFree F s
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := mem_verticiIper.mp hy
    rw [cubeFaceInsertion_vertex]
    refine Finset.mem_filter.mpr ⟨mem_verticiIper.mpr ⟨_, rfl⟩, ?_⟩
    apply (vertIper_mem_face_iff d hd hF hs _).mpr
    intro i hi
    simp [cubeCodeInsertion, hi]
  · intro hx
    obtain ⟨u, rfl⟩ := mem_verticiIper.mp (Finset.mem_filter.mp hx).1
    have hu : u ∈ Cubical.Cube.FaceAt s A :=
      (vertIper_mem_face_iff d hd hF hs u).mp (Finset.mem_filter.mp hx).2
    exact ⟨vertIper (fun j => u (A.equivFin.symm j).val),
      mem_verticiIper.mpr ⟨_, rfl⟩, cubeFaceInsertion_restrict_vertex s u A hu⟩

theorem cubeFaceInsertion_image_body (d : ℕ) (hd : 1 ≤ d)
    {F : Set (E d)} (hF : (standardCube d).IsFace F)
    (s : Fin d → Bool) (hs : vertIper s ∈ F) :
    cubeFaceInsertion s (iperFaceFree F s) ''
      (standardCube (iperFaceFree F s).card).toSet =
        (facePolytope (standardCube d) hF).toSet := by
  change cubeFaceInsertion s (iperFaceFree F s) '' convexHull ℝ _ = convexHull ℝ _
  rw [AffineMap.image_convexHull, cubeFaceInsertion_image_vertices d hd hF s hs]

def cubeFaceOrderIso (d : ℕ) (hd : 1 ≤ d)
    {F : Set (E d)} (hF : (standardCube d).IsFace F)
    (s : Fin d → Bool) (hs : vertIper s ∈ F) :
    FaceType (standardCube (iperFaceFree F s).card) ≃o
      FaceType (facePolytope (standardCube d) hF) :=
  affineFaceOrderIso _ _ (cubeFaceInsertion s (iperFaceFree F s))
    (cubeFaceProjection (iperFaceFree F s)).toAffineMap
    (fun x _ => cubeFaceProjection_insertion s (iperFaceFree F s) x)
    (cubeFaceInsertion_image_body d hd hF s hs)

/-- The standard cube meets the geometric definition of cubical. -/
theorem standardCube_isCubical (d : ℕ) (hd : 1 ≤ d) : IsCubical (standardCube d) := by
  intro F hF hdF
  have hdim : (standardCube d).dim = d := ipercubo_isFullDim d hd
  obtain ⟨v, hv⟩ := (facePolytope (standardCube d) hF).vertices_nonempty
  obtain ⟨s, rfl⟩ := mem_verticiIper.mp (Finset.mem_filter.mp hv).1
  have hs := (Finset.mem_filter.mp hv).2
  have hcard : (iperFaceFree F s).card = (standardCube d).dim - 1 := by
    rw [ipercubo_face_free_card d hd hF hs]
    omega
  have φ := (cubeFaceOrderIso d hd hF s hs).symm
  rw [hcard] at φ
  exact ⟨φ⟩

end LeanEval.Geometry.PlatonicClassification
