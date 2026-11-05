import cubical.polytope.vertex_slice
import cubical.polytope.graph_parity

/-!
# Bipartition of geometric polytopes whose two-faces are squares

The proof uses a generic linear height and its concrete hyperplane vertex
figures. Descending links are connected by monotone paths. In a square, a
vertex whose two neighbors are lower is a global maximum, so the opposite
vertex is also lower. The abstract finite-descent coloring theorem then
applies to the actual geometric edge graph.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- The corner and opposite-corner incidence property of a square two-face. -/
def HasSquareTwoFaceCorners (P : ConvexPolytope n) : Prop :=
  ∀ (F : Set (E n)), P.IsFace F → faceDim F = 2 →
    ∀ (v a b : VertexType P), v.val ∈ F → a.val ∈ F → b.val ∈ F →
      (polytopeGraph P).Adj v a → (polytopeGraph P).Adj v b → a ≠ b →
      ∃ z : VertexType P, z ≠ v ∧ z.val ∈ F ∧
        (polytopeGraph P).Adj a z ∧ (polytopeGraph P).Adj b z ∧
        ∀ u : VertexType P, u.val ∈ F → (polytopeGraph P).Adj v u →
          u = a ∨ u = b

/-- One height simultaneously separates the original vertices and every chosen
concrete vertex figure. -/
theorem exists_height_for_vertex_figures (P : ConvexPolytope n)
    (D : (v : VertexType P) → DatiFetta P v.val) :
    ∃ l : E n →L[ℝ] ℝ, Set.InjOn l (P.vertices : Set (E n)) ∧
      ∀ v, Set.InjOn l ((D v).politopo.vertices : Set (E n)) := by
  classical
  let S : Finset (E n) := P.vertices ∪
    Finset.univ.biUnion (fun v : VertexType P => (D v).politopo.vertices)
  obtain ⟨l, hl⟩ := exists_separating_functional S
  refine ⟨l, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hl (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hy) hxy
  · intro v x hx y hy hxy
    have hxS : x ∈ S := Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hx⟩)
    have hyS : y ∈ S := Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hy⟩)
    exact hl hxS hyS hxy

/-- At a strict local maximum of a square, the opposite corner is also below
the maximum. The assertion uses the geometric linearity of the height. -/
theorem lower_twoFace_has_lower_opposite (P : ConvexPolytope n)
    (hsquare : HasSquareTwoFaceCorners P) (l : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn l (P.vertices : Set (E n)))
    (v : VertexType P) (a b : NeighborOf v)
    (hab : LowerTwoFaceRelation v l a b) :
    ∃ z : VertexType P, l z.val < l v.val ∧
      (polytopeGraph P).Adj a.val z ∧ (polytopeGraph P).Adj b.val z := by
  classical
  rcases hab with ⟨ha, hb, hne, F, hF, hdF, hvF, haF, hbF⟩
  have hab' : a.val ≠ b.val := fun h => hne (Subtype.ext h)
  obtain ⟨z, hzv, hzF, haz, hbz, hneighbors⟩ :=
    hsquare F hF hdF v a.val b.val hvF haF hbF a.property b.property hab'
  have hvQ : v.val ∈ (facePolytope P hF).vertices :=
    Finset.mem_filter.mpr ⟨v.property, hvF⟩
  have hzQ : z.val ∈ (facePolytope P hF).vertices :=
    Finset.mem_filter.mpr ⟨z.property, hzF⟩
  have hlocal : ∀ y, GeneralVertexStep (facePolytope P hF) v.val y → l y ≤ l v.val := by
    rintro y ⟨hy, hvy, e, he, hde, hve, hye⟩
    have hyP := (Finset.mem_filter.mp hy).1
    have hyF := (Finset.mem_filter.mp hy).2
    let u : VertexType P := ⟨y, hyP⟩
    have hAdj : (polytopeGraph P).Adj v u :=
      ⟨fun h => hvy (congrArg Subtype.val h), e,
        isFace_of_facePolytope P hF he, hde, hve, hye⟩
    rcases hneighbors u hyF hAdj with hua | hub
    · have hval : y = a.val.val := congrArg Subtype.val hua
      exact hval ▸ ha.le
    · have hval : y = b.val.val := congrArg Subtype.val hub
      exact hval ▸ hb.le
  have hzle := local_max_global_max (facePolytope P hF) l hvQ hlocal z.val hzQ
  have hzne : l z.val ≠ l v.val :=
    fun h => hzv (Subtype.ext (hinj z.property v.property h))
  exact ⟨z, lt_of_le_of_ne hzle hzne, haz, hbz⟩

/-- The genuine geometric edge graph is bipartite when every two-face has
square incidence. No topological or graph-connectivity hypothesis is assumed. -/
theorem polytopeGraph_colorable_two_of_square_corners (P : ConvexPolytope n)
    (hdim : 1 ≤ P.dim) (hsquare : HasSquareTwoFaceCorners P) :
    (polytopeGraph P).Colorable 2 := by
  classical
  let D (v : VertexType P) : DatiFetta P v.val :=
    Classical.choice (esiste_datiFetta P v.property hdim)
  obtain ⟨l, hlP, hlD⟩ := exists_height_for_vertex_figures P D
  let height : VertexType P → ℕ := fun v => heightRank P.vertices l v.val
  have hheight : ∀ a b : VertexType P, height a < height b ↔ l a.val < l b.val := by
    intro a b
    exact heightRank_lt_iff P.vertices l a.property b.property
  have hne : ∀ ⦃u v : VertexType P⦄, (polytopeGraph P).Adj u v → height u ≠ height v := by
    intro u v huv heq
    exact huv.1 (Subtype.ext ((heightRank_injOn P.vertices l hlP) u.property v.property heq))
  apply Cubical.colorable_two_of_descending_square_fans (polytopeGraph P) height hne
  intro v a b hva hvb ha hb
  let a' : NeighborOf v := ⟨a, hva⟩
  let b' : NeighborOf v := ⟨b, hvb⟩
  have hpath := (D v).lowerNeighbors_connected l (hlD v) a' b'
    ((hheight a v).mp ha) ((hheight b v).mp hb)
  have hmap : ∀ p q : NeighborOf v, LowerTwoFaceRelation v l p q →
      Cubical.LowerSquareRelation (polytopeGraph P) height v p.val q.val := by
    intro p q hpq
    obtain ⟨z, hz, hpz, hqz⟩ := lower_twoFace_has_lower_opposite P hsquare l hlP v p q hpq
    exact ⟨(hheight p.val v).mpr hpq.1, (hheight q.val v).mpr hpq.2.1,
      z, (hheight z v).mpr hz, hpz, hqz⟩
  exact Relation.ReflTransGen.lift (fun x : NeighborOf v => x.val) hmap _ _ hpath

end LeanEval.Geometry.PlatonicClassification
