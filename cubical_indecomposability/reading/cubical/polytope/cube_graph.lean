import cubical.polytope.cubical
import cubical.polytope.combinatorial_transport
import cubical.polytope.monotone
import cubical.cube

/-!
# Identifying the geometric cube graph with bit-vector adjacency

The reverse direction uses the geometric improving-edge theorem. A coordinate
functional improves when that bit is flipped; every geometric cube edge has
only one free coordinate, so an improving edge must make exactly that flip.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

def cubeVertex (d : ℕ) (s : Cubical.Cube.Vertex d) : VertexType (standardCube d) :=
  ⟨vertIper s, mem_verticiIper.mpr ⟨s, rfl⟩⟩

def cubeVertexEquiv (d : ℕ) : Cubical.Cube.Vertex d ≃ VertexType (standardCube d) :=
  Equiv.ofBijective (cubeVertex d) ⟨
    fun _ _ h ↦ vertIper_injective (congrArg Subtype.val h),
    by
      rintro ⟨x, hx⟩
      obtain ⟨s, rfl⟩ := mem_verticiIper.mp hx
      exact ⟨s, rfl⟩⟩

theorem cube_edge_changes_one_coordinate (d : ℕ) (hd : 1 ≤ d)
    (s t : Cubical.Cube.Vertex d)
    (h : (polytopeGraph (standardCube d)).Adj (cubeVertex d s) (cubeVertex d t)) :
    ∃ i, t = Cubical.Cube.flip s i := by
  classical
  rcases h with ⟨hne, F, hF, hdim, hs, ht⟩
  have hF' : (ipercubo d hd).IsFace F := hF
  have hcard := (ipercubo_face_free_card d hd hF' hs).trans hdim
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hother : ∀ j, j ≠ i → t j = s j := by
    intro j hji
    apply (vertIper_mem_face_iff d hd hF' hs t).mp ht j
    simpa [hi] using hji
  have hat : t i ≠ s i := by
    intro heq
    have hst : s = t := by
      funext j
      by_cases hji : j = i
      · subst j
        exact heq.symm
      · exact (hother j hji).symm
    exact hne (congrArg (cubeVertex d) hst)
  refine ⟨i, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j
    rw [Cubical.Cube.flip_same]
    cases hs' : s i <;> cases ht' : t i <;> simp_all
  · simpa [hji] using hother j hji

theorem cube_flip_is_edge (d : ℕ) (hd : 1 ≤ d)
    (s : Cubical.Cube.Vertex d) (i : Fin d) :
    (polytopeGraph (standardCube d)).Adj
      (cubeVertex d s) (cubeVertex d (Cubical.Cube.flip s i)) := by
  classical
  let a : ℝ := if s i then -1 else 1
  let l : E d →L[ℝ] ℝ := a • EuclideanSpace.proj i
  have hl (x : E d) : l x = a * x i := rfl
  have hup : l (vertIper s) < l (vertIper (Cubical.Cube.flip s i)) := by
    rw [hl, hl, vertIper_apply, vertIper_apply, Cubical.Cube.flip_same]
    cases h : s i <;> norm_num [a, h]
  obtain ⟨y, hy, hly⟩ := exists_improving_step (standardCube d) l
    (cubeVertex d s).property
    ⟨vertIper (Cubical.Cube.flip s i), (cubeVertex d _).property, hup⟩
  obtain ⟨t, rfl⟩ := mem_verticiIper.mp hy.1
  have hedge : (polytopeGraph (standardCube d)).Adj (cubeVertex d s) (cubeVertex d t) := by
    refine ⟨?_, hy.2.2⟩
    intro h
    exact hy.2.1 (congrArg Subtype.val h)
  obtain ⟨j, rfl⟩ := cube_edge_changes_one_coordinate d hd s t hedge
  have hji : j = i := by
    by_contra hji
    change l (vertIper s) < l (vertIper (Cubical.Cube.flip s j)) at hly
    rw [hl, hl, vertIper_apply, vertIper_apply,
      Cubical.Cube.flip_other s j i (Ne.symm hji)] at hly
    exact lt_irrefl _ hly
  simpa [hji] using hedge

/-- The actual geometric standard cube has exactly the bit-vector cube graph. -/
def cubeGraphIso (d : ℕ) (hd : 1 ≤ d) :
    Cubical.Cube.graph d ≃g polytopeGraph (standardCube d) where
  __ := cubeVertexEquiv d
  map_rel_iff' := by
    intro s t
    constructor
    · exact cube_edge_changes_one_coordinate d hd s t
    · rintro ⟨i, rfl⟩
      exact cube_flip_is_edge d hd s i

end LeanEval.Geometry.PlatonicClassification
