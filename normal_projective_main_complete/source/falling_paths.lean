module

public import boundary_corners
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# A genuine negative-side cycle through an interior edge

Two falling paths are joined by an actual side of the triangular boundary and
then reduced to a simple path. The initial edge closes it into a graph cycle.
Every other cycle vertex has strictly negative harmonic height.
-/

@[expose] public section

namespace NormalProjective.Planar

open Set Finset Relation SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DirichletPaths

theorem increasingPath_eq_or_lt (G : SimpleGraph V) (x : V → ℝ) {i j : V}
    (h : ReflTransGen (Dirichlet.IncreasingEdge G x) i j) : i = j ∨ x i < x j := by
  cases h with
  | refl => exact Or.inl rfl
  | tail hprev hnext =>
    exact Or.inr (lt_of_le_of_lt (Dirichlet.increasingPath_le G x hprev) hnext.2)

def negativeVertices (x : V → ℝ) (a b : V) : Set V :=
  {v | v = a ∨ v = b ∨ x v < 0}

def lowerGraph (G : SimpleGraph V) (x : V → ℝ) (a b : V) : SimpleGraph V where
  Adj i j := G.Adj i j ∧ i ∈ negativeVertices x a b ∧
    j ∈ negativeVertices x a b ∧ (x i < 0 ∨ x j < 0)
  symm := ⟨by
    rintro i j ⟨hij,hi,hj,hstrict⟩
    exact ⟨hij.symm,hj,hi,hstrict.symm⟩⟩
  loopless := ⟨by rintro i ⟨hii,_⟩; exact hii.ne rfl⟩

theorem lowerGraph_le (G : SimpleGraph V) (x : V → ℝ) (a b : V) :
    lowerGraph G x a b ≤ G := fun _ _ h => h.1

theorem falling_vertex (G : SimpleGraph V) (x : V → ℝ) {i j : V}
    (hi : x i = 0)
    (h : ReflTransGen (Dirichlet.IncreasingEdge G (fun v => -x v)) i j) :
    j = i ∨ x j < 0 := by
  rcases increasingPath_eq_or_lt G (fun v => -x v) h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by linarith)

theorem falling_reachable_lower (G : SimpleGraph V) (x : V → ℝ) (a b : V)
    {i j : V} (hiab : i = a ∨ i = b) (hi : x i = 0)
    (h : ReflTransGen (Dirichlet.IncreasingEdge G (fun v => -x v)) i j) :
    (lowerGraph G x a b).Reachable i j := by
  induction h with
  | refl => exact .refl i
  | @tail v z hprev hnext ih =>
    have hv : v ∈ negativeVertices x a b := by
      rcases falling_vertex G x hi hprev with rfl | hv
      · exact hiab.elim Or.inl (Or.inr ∘ Or.inl)
      · exact Or.inr (Or.inr hv)
    have hvle : x v ≤ 0 := by
      have h := Dirichlet.increasingPath_le G (fun v => -x v) hprev
      linarith
    have hz : x z < 0 := by have h := hnext.2; linarith
    exact ih.trans (show (lowerGraph G x a b).Adj v z from
      ⟨hnext.1,hv,Or.inr (Or.inr hz),Or.inr hz⟩).reachable

theorem lower_walk_vertices (G : SimpleGraph V) (x : V → ℝ) (a b : V)
    {i j : V} (hi : i ∈ negativeVertices x a b)
    (p : (lowerGraph G x a b).Walk i j) :
    ∀ v ∈ p.support, v ∈ negativeVertices x a b := by
  induction p with
  | nil => simpa using hi
  | @cons u v z huv p ih =>
    intro t ht
    simp only [Walk.support_cons,List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact huv.2.1
    · exact ih huv.2.2.1 t ht

end DirichletPaths

namespace TriangularDisk

open DirichletPaths

variable (D : TriangularDisk V)

/-- An actual simple graph cycle through `a → b`, with strictly negative
height at every other vertex. The assumption that at least one endpoint is
interior is derived from the adjacent-face geometry in the embedding proof. -/
theorem exists_negative_cycle_walk
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
    (h : V → ℝ) (hh : ∀ i, i ∉ D.boundary → Dirichlet.Harmonic w h i)
    {a b v : V} (hab : D.toTriangulation.graph.Adj a b)
    (hav : D.toTriangulation.graph.Adj a v)
    (hbv : D.toTriangulation.graph.Adj b v)
    (ha : h a = 0) (hb : h b = 0) (hv : 0 < h v)
    (hinterior : a ∉ D.boundary ∨ b ∉ D.boundary) :
    ∃ p : D.toTriangulation.graph.Walk a a,
      p.IsCycle ∧ p.getVert 1 = b ∧
        ∀ u ∈ p.support, u = a ∨ u = b ∨ h u < 0 := by
  classical
  let G := D.toTriangulation.graph
  let H := lowerGraph G h a b
  obtain ⟨u,huB,hau,hu⟩ := Dirichlet.exists_falling_path_to_boundary G D.boundary
    w hw he hoff h hh hav (by linarith)
  obtain ⟨z,hzB,hbz,hz⟩ := Dirichlet.exists_falling_path_to_boundary G D.boundary
    w hw he hoff h hh hbv (by linarith)
  have hauH : H.Reachable a u := falling_reachable_lower G h a b (Or.inl rfl) ha hau
  have hbzH : H.Reachable b z := falling_reachable_lower G h a b (Or.inr rfl) hb hbz
  have huOK : u ∈ negativeVertices h a b := by
    rcases falling_vertex G h ha hau with rfl | hu
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hu)
  have hzOK : z ∈ negativeVertices h a b := by
    rcases falling_vertex G h hb hbz with rfl | hz
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hz)
  have hstrict : h u < 0 ∨ h z < 0 := by
    rcases hinterior with haB | hbB
    · rcases falling_vertex G h ha hau with rfl | hu
      · exact False.elim (haB huB)
      · exact Or.inl hu
    · rcases falling_vertex G h hb hbz with rfl | hz
      · exact False.elim (hbB hzB)
      · exact Or.inr hz
  have huz : H.Reachable u z := by
    by_cases huz : u = z
    · subst z
      exact .refl u
    · obtain ⟨i,rfl⟩ := huB
      obtain ⟨j,rfl⟩ := hzB
      have hij : i ≠ j := fun hij => huz (congrArg D.corner hij)
      exact (show H.Adj (D.corner i) (D.corner j) from
        ⟨D.boundary_edge i j hij,huOK,hzOK,hstrict⟩).reachable
  obtain ⟨p⟩ := hauH.trans (huz.trans hbzH.symm)
  let q : H.Walk b a := (p.toPath : H.Walk a b).reverse
  have hqpath : q.IsPath := p.toPath.property.reverse
  let qG : G.Walk b a := q.mapLe (lowerGraph_le G h a b)
  have hqGpath : qG.IsPath := hqpath.mapLe _
  have hno : s(a,b) ∉ qG.edges := by
    intro heab
    have heab' : s(a,b) ∈ q.edges := by simpa [qG] using heab
    have hadj := q.adj_of_mem_edges heab'
    rcases hadj.2.2.2 with h | h <;> linarith
  refine ⟨Walk.cons hab qG,(Walk.cons_isCycle_iff qG hab).mpr ⟨hqGpath,hno⟩,?_,?_⟩
  · simp
  · intro t ht
    simp only [Walk.support_cons,List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact Or.inl rfl
    · have htq : t ∈ q.support := by simpa [qG] using ht
      exact lower_walk_vertices G h a b (Or.inr (Or.inl rfl)) q t htq

end TriangularDisk

end NormalProjective.Planar
