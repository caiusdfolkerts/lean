module

public import Papers.GraphicalZonotopes.GraphDefinitions
public import Papers.GraphicalZonotopes.EdgeCoordinates
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Actual edge counts for every subgraph of a clique book -/

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BookEdges
open Finset
open scoped BigOperators
variable {s k : ℕ}

abbrev Vertex (s k : ℕ) := Fin s ⊕ Fin k

def outerNeighbors (G : SimpleGraph (Vertex s k)) (i : Fin s) : Finset (Fin k) := by
  classical
  exact univ.filter (fun j => G.Adj (Sum.inl i) (Sum.inr j))

@[simp] theorem mem_outerNeighbors (G : SimpleGraph (Vertex s k)) (i : Fin s) (j : Fin k) :
    j∈outerNeighbors G i ↔ G.Adj (Sum.inl i) (Sum.inr j) := by
  classical
  simp [outerNeighbors]

private theorem degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v=∑ w : V,if G.Adj v w then 1 else 0 := by
  classical
  have he : G.neighborFinset v=univ.filter (G.Adj v) := by ext w; simp
  rw [←SimpleGraph.card_neighborFinset_eq_degree,he,Finset.card_eq_sum_ones,Finset.sum_filter]

/-- Exact edge decomposition into all hub pairs and actual private spokes.
It applies to every subgraph, with no extremality or lattice assumption. -/
theorem edge_count (G : SimpleGraph (Vertex s k))
    (hsub : G≤cliqueBook s k)
    (hhub : ∀ i j : Fin s,i≠j → G.Adj (Sum.inl i) (Sum.inl j)) :
    (edgeFamily G).card=s.choose 2+∑ i : Fin s,(outerNeighbors G i).card := by
  classical
  have hleft (i j : Fin s) : G.Adj (Sum.inl i) (Sum.inl j) ↔ i≠j := by
    constructor
    · intro h he
      exact h.ne (congrArg Sum.inl he)
    · exact hhub i j
  have hright (i j : Fin k) : ¬G.Adj (Sum.inr i) (Sum.inr j) := by
    intro h
    have hh := hsub h
    simpa only [cliqueBook,Sum.isLeft_inr,Bool.false_eq_true,or_self,and_false] using hh
  have hspokes (i : Fin s) : (outerNeighbors G i).card=
      ∑ j : Fin k,if G.Adj (Sum.inl i) (Sum.inr j) then 1 else 0 := by
    rw [outerNeighbors,Finset.card_eq_sum_ones,Finset.sum_filter]
  have htop := (⊤ : SimpleGraph (Fin s)).sum_degrees_eq_twice_card_edges
  simp only [degree_sum,SimpleGraph.top_adj,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin] at htop
  have hall := G.sum_degrees_eq_twice_card_edges
  simp only [degree_sum,Fintype.sum_sum_type,hleft,hright,if_false,sum_const_zero,
    add_zero,Finset.sum_add_distrib] at hall
  have htranspose : (∑ j : Fin k,∑ i : Fin s,if G.Adj (Sum.inr j) (Sum.inl i) then 1 else 0)=
      ∑ i : Fin s,∑ j : Fin k,if G.Adj (Sum.inl i) (Sum.inr j) then 1 else 0 := by
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [G.adj_comm]
  rw [htranspose,htop] at hall
  have he : (edgeFamily G).card=G.edgeFinset.card := by
    rw [edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]
  rw [he]
  simp only [hspokes]
  omega

/-- A uniform lower bound at each hub gives the paper's direction bound. -/
theorem edge_count_lower (G : SimpleGraph (Vertex s k)) (hsub : G≤cliqueBook s k)
    (hhub : ∀ i j : Fin s,i≠j → G.Adj (Sum.inl i) (Sum.inl j))
    (u : ℕ) (hdegree : ∀ i : Fin s,u≤(outerNeighbors G i).card) :
    s.choose 2+s*u≤(edgeFamily G).card := by
  rw [edge_count G hsub hhub]
  apply Nat.add_le_add_left
  have h : (∑ _i : Fin s,u) ≤ ∑ i : Fin s,(outerNeighbors G i).card :=
    sum_le_sum (fun i _ => hdegree i)
  simpa only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] using h

/-- Exact uniform spoke counts give equality, without an extra graphical
assumption hidden in the numerical statement. -/
theorem edge_count_eq (G : SimpleGraph (Vertex s k)) (hsub : G≤cliqueBook s k)
    (hhub : ∀ i j : Fin s,i≠j → G.Adj (Sum.inl i) (Sum.inl j))
    (u : ℕ) (hdegree : ∀ i : Fin s,(outerNeighbors G i).card=u) :
    (edgeFamily G).card=s.choose 2+s*u := by
  rw [edge_count G hsub hhub]
  simp only [hdegree,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]

end GraphicalZonotopes.BookEdges
