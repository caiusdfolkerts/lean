module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fin.VecNotation

@[expose] public section
namespace GraphicalZonotopes
namespace CliqueDegree

open Finset

/-- Every graph on six named vertices containing the two tetrahedra
`0123` and `0124` has exactly these six optional edges.  The parameter
records `34, 05, 15, 25, 35, 45`; all remaining non-loop edges are forced. -/
def sixGraph (b : Fin 6 → Bool) : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧
    (if i = 5 then b (j+1) = true
     else if j = 5 then b (i+1) = true
     else i.val < 3 ∨ j.val < 3 ∨ b 0 = true)
  symm := ⟨by
    intro i j
    by_cases hi : i = 5 <;> by_cases hj : j = 5 <;>
      simp [hi,hj,ne_comm,or_comm,or_left_comm]⟩
  loopless := ⟨by intro i; simp⟩

instance (b : Fin 6 → Bool) : DecidableRel (sixGraph b).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧
    (if i = 5 then b (j+1) = true
     else if j = 5 then b (i+1) = true
     else i.val < 3 ∨ j.val < 3 ∨ b 0 = true)))

def HasSixthAttachment (G : SimpleGraph (Fin 6)) : Prop :=
  ∃ T : Finset (Fin 6), T.card = 3 ∧ 5 ∉ T ∧ G.IsClique T ∧
    ∀ i ∈ T, G.Adj i 5

def EveryTriangleSaturated (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] : Prop :=
  ∀ T : Finset (Fin 6), T.card = 3 → G.IsClique T → ∃ i ∈ T, 5 ≤ G.degree i

instance (b : Fin 6 → Bool) : Decidable (HasSixthAttachment (sixGraph b)) := by
  unfold HasSixthAttachment
  infer_instance

instance (b : Fin 6 → Bool) : Decidable (EveryTriangleSaturated (sixGraph b)) := by
  unfold EveryTriangleSaturated
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The finite local obstruction in Lemma 4.5.  This checks exactly the
64 possible supergraphs of the two initial tetrahedra, with every possible
attachment triangle.  It is used as a local lemma in the arbitrary-graph
argument, not as a bounded version of the paper's theorem.  `decide` builds
a proof checked by reduction in the Lean kernel; no native evaluator is used. -/
theorem six_vertex_obstruction :
    ∀ b : Fin 6 → Bool, HasSixthAttachment (sixGraph b) →
      EveryTriangleSaturated (sixGraph b) := by
  decide

def optionalEdges (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] : Fin 6 → Bool :=
  ![decide (G.Adj 3 4),decide (G.Adj 0 5),decide (G.Adj 1 5),
    decide (G.Adj 2 5),decide (G.Adj 3 5),decide (G.Adj 4 5)]

/-- The finite certificate represents every supergraph of the two indicated
tetrahedra, rather than a selected collection of examples. -/
theorem eq_sixGraph (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h₃ : G.IsClique ({0,1,2,3} : Finset (Fin 6)))
    (h₄ : G.IsClique ({0,1,2,4} : Finset (Fin 6))) :
    G = sixGraph (optionalEdges G) := by
  have h01 : G.Adj 0 1 := h₃ (by decide) (by decide) (by decide)
  have h02 : G.Adj 0 2 := h₃ (by decide) (by decide) (by decide)
  have h03 : G.Adj 0 3 := h₃ (by decide) (by decide) (by decide)
  have h04 : G.Adj 0 4 := h₄ (by decide) (by decide) (by decide)
  have h12 : G.Adj 1 2 := h₃ (by decide) (by decide) (by decide)
  have h13 : G.Adj 1 3 := h₃ (by decide) (by decide) (by decide)
  have h14 : G.Adj 1 4 := h₄ (by decide) (by decide) (by decide)
  have h23 : G.Adj 2 3 := h₃ (by decide) (by decide) (by decide)
  have h24 : G.Adj 2 4 := h₄ (by decide) (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixGraph,optionalEdges,h01,h02,h03,h04,h12,h13,h14,h23,h24,
      SimpleGraph.adj_comm] <;> first | exact G.adj_symm h01 | assumption

theorem six_vertex_obstruction_graph (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h₃ : G.IsClique ({0,1,2,3} : Finset (Fin 6)))
    (h₄ : G.IsClique ({0,1,2,4} : Finset (Fin 6)))
    (ha : HasSixthAttachment G) : EveryTriangleSaturated G := by
  have he := eq_sixGraph G h₃ h₄
  have ha' : HasSixthAttachment (sixGraph (optionalEdges G)) := by simpa only [he] using ha
  have hs := six_vertex_obstruction (optionalEdges G) ha'
  simpa only [← he] using hs

section Ambient
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An extra neighbor outside an embedded finite graph raises the ambient
degree by one. This is the arbitrary-size bridge for the six-vertex local
certificate. -/
theorem degree_ge_of_extra_neighbor (f : Fin 6 ↪ V) (i : Fin 6) (w : V)
    (hw : w ∉ Set.range f) (hadj : G.Adj (f i) w) :
    (G.comap f).degree i+1 ≤ G.degree (f i) := by
  classical
  let S := ((G.comap f).neighborFinset i).map f
  have hwS : w ∉ S := by
    intro h
    obtain ⟨j,hj,he⟩ := mem_map.mp h
    exact hw ⟨j,he⟩
  have hsub : insert w S ⊆ G.neighborFinset (f i) := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact (G.mem_neighborFinset _ _).mpr hadj
    · obtain ⟨j,hj,rfl⟩ := mem_map.mp hv
      exact (G.mem_neighborFinset _ _).mpr ((G.comap f).mem_neighborFinset _ _ |>.mp hj)
  calc
    (G.comap f).degree i+1 = (insert w S).card := by
      rw [card_insert_of_notMem hwS]
      simp only [S,card_map,SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ (G.neighborFinset (f i)).card := card_le_card hsub
    _ = G.degree (f i) := rfl

/-- Once the first six vertices of a triangle-connected tetrahedron family
have appeared, a graph of maximum degree five cannot attach a seventh vertex
to any triangle on those six vertices. The ambient vertex type is unrestricted. -/
theorem no_seventh_triangle_attachment (f : Fin 6 ↪ V)
    (hdeg : ∀ v, G.degree v ≤ 5)
    (h₃ : (G.comap f).IsClique ({0,1,2,3} : Finset (Fin 6)))
    (h₄ : (G.comap f).IsClique ({0,1,2,4} : Finset (Fin 6)))
    (ha : HasSixthAttachment (G.comap f))
    (w : V) (hw : w ∉ Set.range f) (T : Finset (Fin 6))
    (hT : T.card = 3) (hcl : (G.comap f).IsClique T)
    (hneigh : ∀ i ∈ T, G.Adj (f i) w) : False := by
  classical
  obtain ⟨i,hi,hfive⟩ := six_vertex_obstruction_graph (G.comap f) h₃ h₄ ha T hT hcl
  have hsix := degree_ge_of_extra_neighbor G f i w hw (hneigh i hi)
  have hup := hdeg (f i)
  omega

end Ambient

end CliqueDegree
end GraphicalZonotopes
