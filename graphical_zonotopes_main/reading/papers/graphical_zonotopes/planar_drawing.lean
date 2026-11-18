module

public import Mathlib.Combinatorics.Graph.Maps
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
public import Schoenflies.Graph.Drawing

@[expose] public section
noncomputable section
open scoped Classical Graph

namespace Graph.IsDrawing

/-- A genuine drawing restricts to every subgraph, using the same edge arcs. -/
theorem restrictSimpleAdapter {β : Type*} {G H : Graph Schoenflies.Plane β}
    {drawing : β → ℝ → Schoenflies.Plane} (h : Graph.IsDrawing G drawing)
    (hHG : H ≤ G) : Graph.IsDrawing H drawing := by
  constructor
  · intro e he
    obtain ⟨hc,hi,hl⟩ := h.edge_param (hHG.edgeSet_mono he)
    exact ⟨hc,hi,(hHG.isLink_iff he).mpr hl⟩
  · intro e x y v hl hv hve
    exact h.vertex_mem_edgeArc (hl.mono hHG) (hHG.vertexSet_mono hv) hve
  · intro e f he hf hef p hpe hpf
    obtain ⟨_,hie,hif⟩ := h.edge_inter (hHG.edgeSet_mono he)
      (hHG.edgeSet_mono hf) hef hpe hpf
    have hie' : H.Inc e p := (hHG.inc_congr he).mpr hie
    have hif' : H.Inc f p := (hHG.inc_congr hf).mpr hif
    exact ⟨hie'.vertex_mem,hie',hif'⟩

end Graph.IsDrawing

namespace GraphicalZonotopes
namespace PlaneDrawing

variable {V : Type*}

/-- Transport an ordinary simple graph to actual points of the Euclidean plane.
The edge names remain precisely the unordered pairs of the original vertices. -/
def planeGraph (G : SimpleGraph V) (p : V → Schoenflies.Plane) :
    Graph Schoenflies.Plane (Sym2 V) := (Graph.ofSimpleGraph G).map p

@[simp] theorem planeGraph_vertexSet (G : SimpleGraph V) (p : V → Schoenflies.Plane) :
    V(planeGraph G p) = Set.range p := by
  simp [planeGraph]

@[simp] theorem planeGraph_edgeSet (G : SimpleGraph V) (p : V → Schoenflies.Plane) :
    E(planeGraph G p) = G.edgeSet := rfl

@[simp] theorem planeGraph_isLink (G : SimpleGraph V) (p : V → Schoenflies.Plane)
    (hp : Function.Injective p) (e : Sym2 V) (u v : V) :
    (planeGraph G p).IsLink e (p u) (p v) ↔ e = s(u,v) ∧ G.Adj u v := by
  constructor
  · rintro ⟨a,b,⟨he,hE⟩,ha,hb⟩
    have hau : a = u := hp ha
    have hbv : b = v := hp hb
    subst a; subst b
    exact ⟨he,by simpa [he] using hE⟩
  · rintro ⟨rfl,huv⟩
    exact ⟨u,v,⟨rfl,by simpa using huv⟩,rfl,rfl⟩

/-- An injective point placement preserves looplessness and uniqueness of edges. -/
theorem planeGraph_simple (G : SimpleGraph V) (p : V → Schoenflies.Plane)
    (hp : Function.Injective p) : (planeGraph G p).Simple where
  not_isLoopAt e x := by
    rintro ⟨u,v,⟨he,hE⟩,hu,hv⟩
    have huv : u = v := hp (hu.trans hv.symm)
    subst v
    simpa [he] using hE
  eq_of_isLink := by
    rintro e f x y ⟨u,v,⟨he,hE⟩,hu,hv⟩ ⟨a,b,⟨hf,hF⟩,ha,hb⟩
    have hua : u = a := hp (hu.trans ha.symm)
    have hvb : v = b := hp (hv.trans hb.symm)
    subst a; subst b
    exact he.trans hf.symm

instance planeGraph_finite [Finite V] (G : SimpleGraph V)
    (p : V → Schoenflies.Plane) : (planeGraph G p).Finite where
  finite_vertexSet := by rw [planeGraph_vertexSet]; exact Set.finite_range p
  finite_edgeSet := Set.toFinite _

@[simp] theorem planeGraph_vertex_ncard [Fintype V] (G : SimpleGraph V)
    (p : V → Schoenflies.Plane) (hp : Function.Injective p) :
    V(planeGraph G p).ncard = Fintype.card V := by
  rw [planeGraph_vertexSet,Set.ncard_range_of_injective hp,Nat.card_eq_fintype_card]

@[simp] theorem planeGraph_edge_ncard [Fintype V] (G : SimpleGraph V)
    (p : V → Schoenflies.Plane) : E(planeGraph G p).ncard = G.edgeFinset.card := by
  classical
  rw [planeGraph_edgeSet,← G.coe_edgeFinset,Set.ncard_coe_finset]

theorem ofSimpleGraph_mono {G H : SimpleGraph V} (h : G ≤ H) :
    Graph.ofSimpleGraph G ≤ Graph.ofSimpleGraph H := by
  constructor
  · exact Set.Subset.rfl
  · rintro e u v ⟨rfl,he⟩
    exact ⟨rfl,by simpa using h (show G.Adj u v by simpa using he)⟩

theorem planeGraph_mono {G H : SimpleGraph V} (h : G ≤ H)
    (p : V → Schoenflies.Plane) : planeGraph G p ≤ planeGraph H p :=
  (ofSimpleGraph_mono h).map p

end PlaneDrawing

/-- Planarity in its geometric sense: an injective placement of the vertices in
ℝ² and simple continuous edge arcs meeting only at their common endpoints.
This uses the genuine drawing predicate from the Jordan–Schönflies library. -/
def HasPlaneDrawing {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p : V → Schoenflies.Plane, Function.Injective p ∧
    ∃ drawing : Sym2 V → ℝ → Schoenflies.Plane,
      Graph.IsDrawing (PlaneDrawing.planeGraph G p) drawing

theorem HasPlaneDrawing.mono {V : Type*} {G H : SimpleGraph V}
    (hG : HasPlaneDrawing G) (hHG : H ≤ G) : HasPlaneDrawing H := by
  obtain ⟨p,hp,drawing,hd⟩ := hG
  exact ⟨p,hp,drawing,hd.restrictSimpleAdapter (PlaneDrawing.planeGraph_mono hHG p)⟩

end GraphicalZonotopes
