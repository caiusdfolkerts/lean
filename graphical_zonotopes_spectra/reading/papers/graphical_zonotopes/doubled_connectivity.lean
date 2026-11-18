module

public import Papers.GraphicalZonotopes.DoubledFourCoefficients
public import Papers.GraphicalZonotopes.DoubledLocalLines

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

def selectedClique (T : Finset I) (b : I → Fin 2) : Finset (I×Fin 2) :=
  T.image fun i => (i,b i)

@[simp] theorem mem_selectedClique (T : Finset I) (b : I → Fin 2) (w : I×Fin 2) :
    w∈selectedClique T b ↔ w.1∈T ∧ b w.1=w.2 := by
  constructor
  · intro hw
    obtain ⟨i,hi,he⟩ := mem_image.mp hw
    have h1 : i=w.1 := congrArg Prod.fst he
    have h2 : b i=w.2 := congrArg Prod.snd he
    simpa [h1] using And.intro hi h2
  · rintro ⟨hi,hb⟩
    exact mem_image.mpr ⟨w.1,hi,Prod.ext rfl hb⟩

@[simp] theorem selectedClique_card (T : Finset I) (b : I → Fin 2) :
    (selectedClique T b).card=T.card :=
  card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

theorem selectedClique_isClique (T : Finset I) (b : I → Fin 2) :
    (graph I).IsClique (selectedClique T b) := by
  intro u hu v hv huv
  have hu' := (mem_selectedClique T b u).mp hu
  have hv' := (mem_selectedClique T b v).mp hv
  intro he
  apply huv
  apply Prod.ext he
  rw [← hu'.2,← hv'.2,he]

def canonicalEdge (e : SlopeEdge (graph I)) : SlopeEdge (graph I) :=
  ⟨((e.1.1.1,0),(e.1.2.1,0)),e.2⟩

theorem shared_four_reachable {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (e f : SlopeEdge (graph I)) {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C)
    (he₁ : e.1.1∈C) (he₂ : e.1.2∈C) (hf₁ : f.1.1∈C) (hf₂ : f.1.2∈C) :
    (coefficientEdgeGraph (graph I) z).Reachable e f := by
  by_cases hef : e=f
  · subst f
    exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable ⟨hef,C,hnon C hcard hC,he₁,he₂,hf₁,hf₂⟩

theorem edge_reachable_canonical (hI : 4≤Fintype.card I)
    {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (e : SlopeEdge (graph I)) :
    (coefficientEdgeGraph (graph I) z).Reachable e (canonicalEdge e) := by
  let a := e.1.1.1
  let b := e.1.2.1
  have hab : a≠b := e.2
  obtain ⟨T,hST,hTU,hT⟩ := exists_subsuperset_card_eq
    (subset_univ ({a,b} : Finset I))
    (show ({a,b} : Finset I).card≤4 by simp [card_pair hab])
    (show 4≤(univ : Finset I).card by simpa using hI)
  have hD : (T\{a,b}).card=2 := by rw [card_sdiff_of_subset hST,hT,card_pair hab]
  obtain ⟨i,j,hij,hDij⟩ := card_eq_two.mp hD
  have hi : i∈T ∧ i≠a ∧ i≠b := by
    have h : i∈T\{a,b} := by rw [hDij]; simp
    simpa using h
  have hj : j∈T ∧ j≠a ∧ j≠b := by
    have h : j∈T\{a,b} := by rw [hDij]; simp
    simpa using h
  have haT : a∈T := hST (by simp)
  have hbT : b∈T := hST (by simp)
  let f : SlopeEdge (graph I) := ⟨((i,0),(j,0)),hij⟩
  let bits : I → Fin 2 := fun k => if k=a then e.1.1.2 else if k=b then e.1.2.2 else 0
  have hfirst : (coefficientEdgeGraph (graph I) z).Reachable e f := by
    apply shared_four_reachable hnon e f (C := selectedClique T bits)
      (by simpa using hT) (selectedClique_isClique T bits)
    · simp [bits,a,haT]
    · simp [bits,b,a,hbT,Ne.symm hab]
    · simp [f,bits,hi.1,hi.2.1,hi.2.2]
    · simp [f,bits,hj.1,hj.2.1,hj.2.2]
  have hsecond : (coefficientEdgeGraph (graph I) z).Reachable f (canonicalEdge e) := by
    apply shared_four_reachable hnon f (canonicalEdge e) (C := selectedClique T (fun _ => 0))
      (by simpa using hT) (selectedClique_isClique T (fun _ => 0))
    · simp [f,hi.1]
    · simp [f,hj.1]
    · simpa [canonicalEdge,a] using haT
    · simpa [canonicalEdge,b] using hbT
  exact hfirst.trans hsecond

theorem canonical_edges_reachable (hI : 4≤Fintype.card I)
    {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (e f : SlopeEdge (graph I)) :
    (coefficientEdgeGraph (graph I) z).Reachable (canonicalEdge e) (canonicalEdge f) := by
  let S : Finset I := {e.1.1.1,e.1.2.1,f.1.1.1,f.1.2.1}
  obtain ⟨T,hST,hTU,hT⟩ := exists_subsuperset_card_eq
    (subset_univ S) (show S.card≤4 from card_le_four) (by simpa using hI)
  apply shared_four_reachable hnon (canonicalEdge e) (canonicalEdge f)
    (C := selectedClique T (fun _ => 0)) (by simpa using hT)
    (selectedClique_isClique T (fun _ => 0))
  · simpa [canonicalEdge] using hST (by simp [S] : e.1.1.1∈S)
  · simpa [canonicalEdge] using hST (by simp [S] : e.1.2.1∈S)
  · simpa [canonicalEdge] using hST (by simp [S] : f.1.1.1∈S)
  · simpa [canonicalEdge] using hST (by simp [S] : f.1.2.1∈S)

theorem slopeEdge_nonempty (hI : 2≤Fintype.card I) : Nonempty (SlopeEdge (graph I)) := by
  obtain ⟨S,hS,hcard⟩ := exists_subset_card_eq
    (show 2≤(univ : Finset I).card by simpa using hI)
  obtain ⟨i,j,hij,rfl⟩ := card_eq_two.mp hcard
  exact ⟨⟨((i,0),(j,0)),hij⟩⟩

/-- Nonzero tetrahedral coefficients connect all actual edge scales, with no
bound on the number of doubled parts. -/
theorem coefficientEdgeGraph_connected (hI : 4≤Fintype.card I)
    {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0) :
    (coefficientEdgeGraph (graph I) z).Connected := by
  letI := slopeEdge_nonempty (by omega : 2≤Fintype.card I)
  refine ⟨?_⟩
  intro e f
  exact (edge_reachable_canonical hI hnon e).trans
    ((canonical_edges_reachable hI hnon e f).trans (edge_reachable_canonical hI hnon f).symm)

theorem graph_connected (hI : 2≤Fintype.card I) : (graph I).Connected := by
  obtain ⟨e⟩ := slopeEdge_nonempty hI
  letI : Nonempty (I×Fin 2) := ⟨e.1.1⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : u.1≠v.1
  · exact SimpleGraph.Adj.reachable huv
  · have he : u.1=v.1 := not_not.mp huv
    obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
      (show ({u.1} : Finset I).card<(univ : Finset I).card by simpa using (show 1 < Fintype.card I by omega))
    have hiu : i≠u.1 := by simpa using hn
    have hiv : i≠v.1 := by simpa only [he] using hiu
    exact (SimpleGraph.Adj.reachable (show (graph I).Adj u (i,0) from Ne.symm hiu)).trans
      (SimpleGraph.Adj.reachable (show (graph I).Adj (i,0) v from hiv))

end DoubledParts
end GraphicalZonotopes
