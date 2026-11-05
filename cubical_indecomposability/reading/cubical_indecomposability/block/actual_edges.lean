import cubical_indecomposability.block.face_realization

/-!
# The edge list consists of actual exposed edges

This is the bridge from geometric parallel redrawings to the finite linear
system used for the rigidity proof.  Each listed pair spans a proved
one-dimensional exposed face of the actual convex polytope.
-/

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- Vertex labels viewed as the ordinary extreme vertices of the polytope. -/
def labelledVertex (v : Fin 32) : VertexType polytope := ⟨p v, vertex_mem v⟩

def edgeFaceIndex (e : Fin 80) : Fin 209 := ⟨32 + e.val, by omega⟩

/-- The edge row is the complete vertex mask of its geometric face. -/
theorem edgeFace_mask (e : Fin 80) :
    faceMask (edgeFaceIndex e) = {edgeVertex e 0, edgeVertex e 1} :=
  edgeMask e

theorem edgeFace_rank (e : Fin 80) : faceRank (edgeFaceIndex e) = 1 := by
  simp only [faceRank, edgeFaceIndex]
  have h0 : ¬32 + e.val < 32 := by omega
  have h1 : 32 + e.val < 112 := by omega
  simp only [h0, h1, if_false, if_true]

theorem edgeFace_dimension (e : Fin 80) :
    faceDim (indexedFace (edgeFaceIndex e)) = 1 := by
  simpa only [edgeFace_rank, Fin.val_one] using indexedFace_dimension (edgeFaceIndex e)

/-- Rank-one catalogue entries are exactly the entries indexed by the edge list. -/
theorem faceRank_one_iff_edgeFaceIndex (i : Fin 209) :
    faceRank i = 1 ↔ ∃ e : Fin 80, edgeFaceIndex e = i := by
  constructor
  · intro hrank
    have hval := congrArg Fin.val hrank
    have hb : 32 ≤ i.val ∧ i.val < 112 := by
      simp only [faceRank] at hval
      split_ifs at hval <;> norm_num at hval <;> omega
    refine ⟨⟨i.val - 32, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp [edgeFaceIndex]
    omega
  · rintro ⟨e, rfl⟩
    exact edgeFace_rank e

/-- The endpoints are distinct because their exposed hull has dimension one. -/
theorem edgeVertex_ne (e : Fin 80) : edgeVertex e 0 ≠ edgeVertex e 1 := by
  intro h
  have hmask : faceMask (edgeFaceIndex e) = {edgeVertex e 1} := by
    simpa [h] using edgeFace_mask e
  have hface : indexedFace (edgeFaceIndex e) = {p (edgeVertex e 1)} := by
    rw [indexedFace_eq_hull, hmask, Finset.coe_singleton,
      Set.image_singleton, convexHull_singleton]
  have hd := edgeFace_dimension e
  rw [hface, faceDim_singleton] at hd
  exact Nat.zero_ne_one hd

/-- Each declared edge is an edge in the standard geometric sense. -/
theorem declaredEdge (e : Fin 80) :
    GeneralVertexStep polytope (p (edgeVertex e 0)) (p (edgeVertex e 1)) := by
  refine ⟨vertex_mem _, ?_, indexedFace (edgeFaceIndex e),
    indexedFace_isFace _, edgeFace_dimension e, ?_, ?_⟩
  · exact fun h => edgeVertex_ne e (p_injective h)
  · rw [vertex_mem_indexedFace, edgeFace_mask]
    simp
  · rw [vertex_mem_indexedFace, edgeFace_mask]
    simp

theorem declaredEdge_adj (e : Fin 80) :
    (polytopeGraph polytope).Adj (labelledVertex (edgeVertex e 0))
      (labelledVertex (edgeVertex e 1)) := by
  obtain ⟨_, hne, F, hF, hdF, h0, h1⟩ := declaredEdge e
  refine ⟨?_, F, hF, hdF, h0, h1⟩
  intro heq
  exact hne (congrArg Subtype.val heq)

/-- The finite edge list is exactly the actual geometric edge relation,
with both orientations permitted. -/
theorem generalVertexStep_iff_edge (u v : Fin 32) :
    GeneralVertexStep polytope (p u) (p v) ↔
      ∃ e : Fin 80,
        (u = edgeVertex e 0 ∧ v = edgeVertex e 1) ∨
        (u = edgeVertex e 1 ∧ v = edgeVertex e 0) := by
  constructor
  · rintro ⟨_, huv, A, hA, hdim, huA, hvA⟩
    obtain ⟨i, hi⟩ := indexedFace_complete hA
    have hrank : faceRank i = 1 := by
      apply Fin.ext
      have h := indexedFace_dimension i
      rw [hi, hdim] at h
      exact h.symm
    obtain ⟨e, he⟩ := (faceRank_one_iff_edgeFaceIndex i).mp hrank
    have hu : u ∈ faceMask (edgeFaceIndex e) :=
      (vertex_mem_indexedFace _ _).mp (by simpa only [he, hi] using huA)
    have hv : v ∈ faceMask (edgeFaceIndex e) :=
      (vertex_mem_indexedFace _ _).mp (by simpa only [he, hi] using hvA)
    rw [edgeFace_mask] at hu hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    have hne : u ≠ v := fun h => huv (congrArg p h)
    refine ⟨e, ?_⟩
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact False.elim (hne (hu.trans hv.symm))
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
    · exact False.elim (hne (hu.trans hv.symm))
  · rintro ⟨e, h | h⟩
    · rcases h with ⟨rfl, rfl⟩
      exact declaredEdge e
    · rcases h with ⟨rfl, rfl⟩
      obtain ⟨_, hne, A, hA, hdim, h0, h1⟩ := declaredEdge e
      exact ⟨vertex_mem _, hne.symm, A, hA, hdim, h1, h0⟩

/-- The same exact enumeration in the standard polytope graph API. -/
theorem labelledVertex_adj_iff_edge (u v : Fin 32) :
    (polytopeGraph polytope).Adj (labelledVertex u) (labelledVertex v) ↔
      ∃ e : Fin 80,
        (u = edgeVertex e 0 ∧ v = edgeVertex e 1) ∨
        (u = edgeVertex e 1 ∧ v = edgeVertex e 0) := by
  rw [← generalVertexStep_iff_edge]
  constructor
  · rintro ⟨hne, A, hA, hdim, hu, hv⟩
    refine ⟨vertex_mem _, ?_, A, hA, hdim, hu, hv⟩
    intro heq
    exact hne (Subtype.ext heq)
  · rintro ⟨_, hne, A, hA, hdim, hu, hv⟩
    refine ⟨?_, A, hA, hdim, hu, hv⟩
    intro heq
    exact hne (congrArg Subtype.val heq)

end CubicalIndecomposability.Block
