import cubical.polytope.simplicial_polytope

/-! # Exposed faces of an actual geometric simplex -/

open Set
open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- The convex hull of a subset of extreme vertices contains no other
extreme vertex of the original polytope. -/
theorem vertices_filter_convexHull_subset (P : ConvexPolytope n)
    (S : Finset (E n)) (hS : S ⊆ P.vertices) :
    P.vertices.filter (fun x => x ∈ convexHull ℝ (S : Set (E n))) = S := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxP, hxS⟩
    have hxext : x ∈ P.toSet.extremePoints ℝ := by
      change x ∈ (convexHull ℝ (P.vertices : Set (E n))).extremePoints ℝ
      rw [← P.vertices_eq_extremePoints]
      exact hxP
    have hsub : convexHull ℝ (S : Set (E n)) ⊆ P.toSet :=
      convexHull_mono (fun _ h => hS h)
    exact extremePoints_convexHull_subset
      (inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hxS, hxext⟩)
  · intro hx
    exact ⟨hS hx, subset_convexHull ℝ _ hx⟩

theorem affineIndependent_face_vertices (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    {F : Set (E n)} (hF : P.IsFace F) :
    AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val) := by
  let f : VertexType (facePolytope P hF) → VertexType P :=
    fun v => ⟨v.val, (Finset.mem_filter.mp v.property).1⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun q : VertexType P => q.val) h)
  exact hi.comp_embedding ⟨f, hf⟩

/-- Removing one vertex from a simplex leaves an exposed face whenever the
remaining vertex set is nonempty. -/
theorem simplex_erase_isFace (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (x : VertexType P) (hne : (P.vertices.erase x.val).Nonempty) :
    P.IsFace (convexHull ℝ ((P.vertices.erase x.val : Finset (E n)) : Set (E n))) := by
  let S := P.vertices.erase x.val
  obtain ⟨u, hu⟩ := hne
  have huS : u ∈ S := hu
  have huP : u ∈ P.vertices := Finset.mem_of_mem_erase hu
  have hi' : AffineIndepOn ℝ id (P.vertices : Set (E n)) := hi
  have hxnot : x.val ∉ affineSpan ℝ (S : Set (E n)) := by
    have h := hi'.notMem_affineSpan_sdiff x.property
    simpa [S, Finset.coe_erase] using h
  have hxsubnot : x.val - u ∉ vectorSpan ℝ (S : Set (E n)) := by
    rw [← direction_affineSpan]
    intro h
    exact hxnot ((AffineSubspace.vsub_right_mem_direction_iff_mem
      (mem_affineSpan ℝ huS) x.val).mp h)
  obtain ⟨f, hfzero, hfx⟩ := LinearMap.exists_extend_of_notMem
    (0 : vectorSpan ℝ (S : Set (E n)) →ₗ[ℝ] ℝ) hxsubnot (-1)
  let l : E n →L[ℝ] ℝ := f.toContinuousLinearMap
  have hconstant : ∀ w ∈ S, l w = l u := by
    intro w hw
    have hwu : w - u ∈ vectorSpan ℝ (S : Set (E n)) :=
      vsub_mem_vectorSpan ℝ hw huS
    have h := congrArg (fun g : vectorSpan ℝ (S : Set (E n)) →ₗ[ℝ] ℝ => g ⟨w-u, hwu⟩) hfzero
    change f (w-u) = 0 at h
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hxlow : l x.val = l u - 1 := by
    rw [map_sub] at hfx
    change f x.val = f u - 1
    linarith
  have hmaxverts : ∀ w ∈ (P.vertices : Set (E n)), l w ≤ l u := by
    intro w hw
    by_cases hwx : w = x.val
    · rw [hwx, hxlow]
      linarith
    · exact (hconstant w (Finset.mem_erase.mpr ⟨hwx, hw⟩)).le
  have hmax := le_su_toSet P l hmaxverts
  let F := l.toExposed P.toSet
  have hF : P.IsFace F :=
    ⟨ContinuousLinearMap.toExposed.isExposed,
      ⟨u, subset_convexHull ℝ _ huP, hmax⟩⟩
  have hvertices : P.vertices.filter (fun w => w ∈ F) = S := by
    ext w
    simp only [Finset.mem_filter, S, Finset.mem_erase]
    constructor
    · rintro ⟨hwP, hwF⟩
      refine ⟨?_, hwP⟩
      intro hwx
      have hule : l u ≤ l w := hwF.2 u (subset_convexHull ℝ _ huP)
      rw [hwx, hxlow] at hule
      linarith
    · rintro ⟨hwx, hwP⟩
      refine ⟨hwP, subset_convexHull ℝ _ hwP, ?_⟩
      intro z hz
      rw [hconstant w (Finset.mem_erase.mpr ⟨hwx, hwP⟩)]
      exact hmax z hz
  have hset := face_eq_hull_vertices P hF
  rw [hvertices] at hset
  exact hset ▸ hF

/-- Every nonempty subset of a simplex's vertices spans an exposed face. -/
theorem simplex_subset_isFace (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (S : Finset (E n)) (hS : S ⊆ P.vertices) (hne : S.Nonempty) :
    P.IsFace (convexHull ℝ (S : Set (E n))) := by
  have aux : ∀ k : ℕ, ∀ Q : ConvexPolytope n, Q.vertices.card ≤ k →
      AffineIndependent ℝ (fun v : VertexType Q => v.val) →
      ∀ T : Finset (E n), T ⊆ Q.vertices → T.Nonempty →
        Q.IsFace (convexHull ℝ (T : Set (E n))) := by
    intro k
    induction k with
    | zero =>
      intro Q hcard _ T _ _
      have hpos := Finset.card_pos.mpr Q.vertices_nonempty
      omega
    | succ k ih =>
      intro Q hcard hAI T hT hTne
      by_cases heq : T = Q.vertices
      · subst T
        exact toSet_isFace Q
      obtain ⟨x, hxQ, hxT⟩ := Finset.exists_of_ssubset (hT.ssubset_of_ne heq)
      have hTErase : T ⊆ Q.vertices.erase x := by
        intro y hy
        refine Finset.mem_erase.mpr ⟨?_, hT hy⟩
        intro hyx
        exact hxT (hyx ▸ hy)
      have hErase := simplex_erase_isFace Q hAI ⟨x, hxQ⟩ (hTne.mono hTErase)
      let R := facePolytope Q hErase
      have hRverts : R.vertices = Q.vertices.erase x :=
        vertices_filter_convexHull_subset Q _ (Finset.erase_subset _ _)
      have hRcard : R.vertices.card ≤ k := by
        rw [hRverts, Finset.card_erase_of_mem hxQ]
        omega
      have hTR : T ⊆ R.vertices := by rwa [hRverts]
      exact isFace_of_facePolytope Q hErase
        (ih R hRcard (affineIndependent_face_vertices Q hAI hErase) T hTR hTne)
  exact aux P.vertices.card P le_rfl hi S hS hne

theorem simplex_face_vertices_card (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    {F : Set (E n)} (hF : P.IsFace F) :
    (facePolytope P hF).vertices.card = faceDim F + 1 := by
  have h := (vertices_affineIndependent_iff (facePolytope P hF)).mp
    (affineIndependent_face_vertices P hi hF)
  rwa [facePolytope_dim] at h

theorem simplex_subset_dimension (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (S : Finset (E n)) (hS : S ⊆ P.vertices) (hne : S.Nonempty) :
    faceDim (convexHull ℝ (S : Set (E n))) + 1 = S.card := by
  have hF := simplex_subset_isFace P hi S hS hne
  have hcard := simplex_face_vertices_card P hi hF
  have hvertices : (facePolytope P hF).vertices = S :=
    vertices_filter_convexHull_subset P S hS
  rw [hvertices] at hcard
  exact hcard.symm

/-- The graph of an actual geometric simplex is complete. -/
theorem simplex_graph_adj (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (u v : VertexType P) (hne : u ≠ v) : (polytopeGraph P).Adj u v := by
  have hne' : u.val ≠ v.val := fun h => hne (Subtype.ext h)
  have hsub : ({u.val, v.val} : Finset (E n)) ⊆ P.vertices := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨u.property, v.property⟩
  have hnePair : ({u.val, v.val} : Finset (E n)).Nonempty := by simp
  have hF := simplex_subset_isFace P hi _ hsub hnePair
  have hdF := simplex_subset_dimension P hi _ hsub hnePair
  have hc : ({u.val, v.val} : Finset (E n)).card = 2 := by simp [hne']
  refine ⟨hne, convexHull ℝ (({u.val, v.val} : Finset (E n)) : Set (E n)),
    hF, by omega, ?_, ?_⟩
  · exact subset_convexHull ℝ _ (by simp)
  · exact subset_convexHull ℝ _ (by simp)

end LeanEval.Geometry.PlatonicClassification
