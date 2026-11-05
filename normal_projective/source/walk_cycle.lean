module

public import graph_polygon
public import falling_paths

/-!
# From a cycle walk to its labelled Jordan polygon

The finite cyclic list is extracted from an actual simple graph cycle. This
keeps the combinatorial and topological versions of the negative cycle tied to
the same vertices and edges.
-/

@[expose] public section

namespace NormalProjective.Planar

open Set Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace GraphCycle

def ofWalk {G : SimpleGraph V} {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    GraphCycle G where
  length := p.length
  length_ge_three := hp.three_le_length
  vertex :=
    { toFun := fun i => p.getVert i.val
      inj' := by
        intro i j hij
        apply Fin.ext
        exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; have := i.isLt; omega)
          (by change j.val ≤ p.length - 1; have := j.isLt; omega) hij }
  edge := by
    intro i
    have hn : 0 < p.length := by have := hp.three_le_length; omega
    letI : NeZero p.length := ⟨ne_of_gt hn⟩
    change G.Adj (p.getVert i.val) (p.getVert (finRotate p.length i).val)
    have hval : (finRotate p.length i).val = (i.val + 1) % p.length := by
      rw [finRotate_apply]
      have h1 : (1 : Fin p.length).val = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by have := hp.three_le_length; omega)
      rw [Fin.val_add,h1]
    rw [hval]
    by_cases hi : i.val + 1 < p.length
    · rw [Nat.mod_eq_of_lt hi]
      exact p.adj_getVert_succ i.isLt
    · have heq : i.val + 1 = p.length := by have := i.isLt; omega
      rw [heq,Nat.mod_self,Walk.getVert_zero]
      simpa only [heq,Walk.getVert_length] using p.adj_getVert_succ i.isLt

theorem ofWalk_vertex_mem_support {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) (i : Fin (ofWalk p hp).length) :
    (ofWalk p hp).vertex i ∈ p.support := p.getVert_mem_support i.val

theorem ofWalk_first {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) :
    (ofWalk p hp).vertex ⟨0,by change 0 < p.length; have := hp.three_le_length; omega⟩ = a := by
  change p.getVert 0 = a
  exact Walk.getVert_zero p

theorem ofWalk_second {G : SimpleGraph V} {a b : V}
    (p : G.Walk a a) (hp : p.IsCycle) (h1 : p.getVert 1 = b) :
    (ofWalk p hp).vertex ⟨1,by change 1 < p.length; have := hp.three_le_length; omega⟩ = b := h1

end GraphCycle

namespace TriangularDisk

variable (D : TriangularDisk V)

theorem exists_negative_cycle
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
    (h : V → ℝ) (hh : ∀ i, i ∉ D.boundary → Dirichlet.Harmonic w h i)
    {a b v : V} (hab : D.toTriangulation.graph.Adj a b)
    (hav : D.toTriangulation.graph.Adj a v)
    (hbv : D.toTriangulation.graph.Adj b v)
    (ha : h a = 0) (hb : h b = 0) (hv : 0 < h v)
    (hinterior : a ∉ D.boundary ∨ b ∉ D.boundary) :
    ∃ C : GraphCycle D.toTriangulation.graph,
      ∃ i : Fin C.length,
        C.vertex i = a ∧ C.vertex (finRotate C.length i) = b ∧
          ∀ u ∈ C.vertices, u = a ∨ u = b ∨ h u < 0 := by
  obtain ⟨p,hp,h1,hvertices⟩ := D.exists_negative_cycle_walk
    w hw he hoff h hh hab hav hbv ha hb hv hinterior
  let C := GraphCycle.ofWalk p hp
  have hlen : 3 ≤ C.length := C.length_ge_three
  let i : Fin C.length := ⟨0,by omega⟩
  refine ⟨C,i,GraphCycle.ofWalk_first p hp,?_,?_⟩
  · have hrot : (finRotate C.length i).val = 1 := by
      simp [finRotate_apply,i,Fin.val_add,Fin.val_one',
        Nat.mod_eq_of_lt (show 1 < C.length by omega)]
    change p.getVert (finRotate C.length i).val = b
    rwa [hrot]
  · rintro u ⟨j,rfl⟩
    exact hvertices _ (GraphCycle.ofWalk_vertex_mem_support p hp j)

end TriangularDisk

end NormalProjective.Planar
