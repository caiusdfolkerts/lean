import Papers.GraphicalZonotopes.ArcK5Definitions
import Schoenflies.Graph.Redrawing

noncomputable section
open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

/-- The ten unordered pairs of distinct labels among five vertices. -/
abbrev K5Edge := {q : Fin 5 × Fin 5 // q.1 < q.2}

/-- A finite graph on five named plane points, with exactly one edge for each
unordered pair. It is an ordinary graph with actual plane vertices. -/
def k5ArcGraph (x : Fin 5 → Plane) : Graph Plane K5Edge where
  vertexSet := Set.range x
  edgeSet := Set.univ
  IsLink e u v := (u = x e.1.1 ∧ v = x e.1.2) ∨
    (u = x e.1.2 ∧ v = x e.1.1)
  isLink_symm := by
    intro e _
    constructor
    rintro u v (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact Or.inr ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e u v a b (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun _ => ⟨x e.1.1,x e.1.2,Or.inl ⟨rfl,rfl⟩⟩,fun _ => Set.mem_univ _⟩
  left_mem_of_isLink := by
    rintro e u v (⟨rfl,_⟩ | ⟨rfl,_⟩)
    · exact ⟨e.1.1,rfl⟩
    · exact ⟨e.1.2,rfl⟩

instance k5ArcGraph_finite (x : Fin 5 → Plane) : (k5ArcGraph x).Finite where
  finite_vertexSet := Set.finite_range x
  finite_edgeSet := Set.finite_univ

theorem k5ArcGraph_isLink (x : Fin 5 → Plane) (e : K5Edge) :
    (k5ArcGraph x).IsLink e (x e.1.1) (x e.1.2) := Or.inl ⟨rfl,rfl⟩

theorem k5ArcGraph_inc (x : Fin 5 → Plane) (e : K5Edge) {p : Plane}
    (hp : p ∈ ({x e.1.1,x e.1.2} : Set Plane)) : (k5ArcGraph x).Inc e p := by
  rcases hp with rfl | rfl
  · exact (k5ArcGraph_isLink x e).inc_left
  · exact (k5ArcGraph_isLink x e).inc_right

namespace IsArcK5
variable {x : Fin 5 → Plane} {P : Fin 5 → Fin 5 → Set Plane}

noncomputable def arcDrawing (h : IsArcK5 x P) : K5Edge → ℝ → Plane :=
  fun e => (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose

theorem edgeArc_eq (h : IsArcK5 x P) (e : K5Edge) :
    edgeArc h.arcDrawing e = P e.1.1 e.1.2 :=
  (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose_spec.2.2.1

theorem arcDrawing_zero (h : IsArcK5 x P) (e : K5Edge) :
    h.arcDrawing e 0 = x e.1.1 :=
  (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose_spec.2.2.2.1

theorem arcDrawing_one (h : IsArcK5 x P) (e : K5Edge) :
    h.arcDrawing e 1 = x e.1.2 :=
  (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose_spec.2.2.2.2

/-- The ten genuine simple arcs supply a finite plane drawing. -/
theorem isDrawing (h : IsArcK5 x P) : IsDrawing (k5ArcGraph x) h.arcDrawing := by
  constructor
  · intro e _
    obtain ⟨hc,hi,_,_,_⟩ := (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose_spec
    refine ⟨hc,hi,?_⟩
    rw [h.arcDrawing_zero,h.arcDrawing_one]
    exact k5ArcGraph_isLink x e
  · intro e u v w hl hwV hw
    obtain ⟨k,rfl⟩ := hwV
    have hv := h.vertex e.1.1 e.1.2 k (ne_of_lt e.2) (by rwa [h.edgeArc_eq] at hw)
    rcases hl with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hv.imp (congrArg x) (congrArg x)
    · exact (hv.imp (congrArg x) (congrArg x)).symm
  · intro e f _ _ hef p hp hq
    rw [h.edgeArc_eq] at hp hq
    have hpairs : e.1 ≠ f.1 := fun hh => hef (Subtype.ext hh)
    have hreverse : e.1 ≠ (f.1.2,f.1.1) := by
      intro hh
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      have he := e.2
      have hf := f.2
      simp only [Prod.fst,Prod.snd] at h1 h2
      omega
    obtain ⟨hpe,hpf⟩ := h.meet e.1.1 e.1.2 f.1.1 f.1.2
      (ne_of_lt e.2) (ne_of_lt f.2) hpairs hreverse ⟨hp,hq⟩
    refine ⟨?_,k5ArcGraph_inc x e hpe,k5ArcGraph_inc x f hpf⟩
    rcases hpe with rfl | rfl
    · exact ⟨e.1.1,rfl⟩
    · exact ⟨e.1.2,rfl⟩

/-- Restore an ordered-pair notation from the ten edge arcs. Diagonal values
are empty and play no role in the K₅ configuration. -/
def edgeFamily (drawing : K5Edge → ℝ → Plane) (i j : Fin 5) : Set Plane :=
  if hij : i < j then edgeArc drawing ⟨(i,j),hij⟩
  else if hji : j < i then edgeArc drawing ⟨(j,i),hji⟩ else ∅

theorem edgeFamily_eq (drawing : K5Edge → ℝ → Plane) {i j : Fin 5} (hij : i < j) :
    edgeFamily drawing i j = edgeArc drawing ⟨(i,j),hij⟩ := by
  simp only [edgeFamily,dif_pos hij]

theorem edgeFamily_symm (drawing : K5Edge → ℝ → Plane) (i j : Fin 5) :
    edgeFamily drawing i j = edgeFamily drawing j i := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [edgeFamily,hij,not_lt_of_ge hij.le]
  · rfl
  · simp [edgeFamily,hji,not_lt_of_ge hji.le]

theorem edgeFamily_edge (drawing : K5Edge → ℝ → Plane) (i j : Fin 5) (hij : i ≠ j) :
    ∃ e : K5Edge, edgeFamily drawing i j = edgeArc drawing e ∧
      (e.1 = (i,j) ∨ e.1 = (j,i)) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨⟨(i,j),hij⟩,edgeFamily_eq drawing hij,Or.inl rfl⟩
  · refine ⟨⟨(j,i),hji⟩,?_,Or.inr rfl⟩
    rw [edgeFamily_symm drawing i j,edgeFamily_eq drawing hji]

theorem isLink_of_pair {e : K5Edge} {i j : Fin 5}
    (he : e.1 = (i,j) ∨ e.1 = (j,i)) : (k5ArcGraph x).IsLink e (x i) (x j) := by
  rcases he with he | he
  · exact Or.inl ⟨by rw [he],by rw [he]⟩
  · exact Or.inr ⟨by rw [he],by rw [he]⟩

/-- A drawing of the ten-edge graph gives the same unrestricted arc interface. -/
theorem of_drawing (hx : Function.Injective x) {drawing : K5Edge → ℝ → Plane}
    (hd : IsDrawing (k5ArcGraph x) drawing) : IsArcK5 x (edgeFamily drawing) := by
  constructor
  · exact hx
  · intro i j hij
    obtain ⟨e,he,hpair⟩ := edgeFamily_edge drawing i j hij
    rw [he]
    exact hd.edge_isArcBetween (isLink_of_pair hpair)
  · exact edgeFamily_symm drawing
  · intro i j k hij hk
    obtain ⟨e,he,hpair⟩ := edgeFamily_edge drawing i j hij
    rw [he] at hk
    have hv : x k ∈ V(k5ArcGraph x) := ⟨k,rfl⟩
    exact (hd.vertex_mem_edgeArc (isLink_of_pair hpair) hv hk).imp
      (fun hh => hx hh) (fun hh => hx hh)
  · intro i j k l hij hkl hpairs hreverse p hp
    obtain ⟨e,he,hepair⟩ := edgeFamily_edge drawing i j hij
    obtain ⟨f,hf,hfpair⟩ := edgeFamily_edge drawing k l hkl
    have hef : e ≠ f := by
      intro hh
      have hval : e.1 = f.1 := congrArg Subtype.val hh
      rcases hepair with hepair | hepair <;>
        rcases hfpair with hfpair | hfpair
      · exact hpairs (hepair.symm.trans (hval.trans hfpair))
      · exact hreverse (hepair.symm.trans (hval.trans hfpair))
      · apply hreverse
        exact congrArg Prod.swap (hepair.symm.trans (hval.trans hfpair))
      · apply hpairs
        exact congrArg Prod.swap (hepair.symm.trans (hval.trans hfpair))
    rw [he,hf] at hp
    obtain ⟨_,hpe,hpf⟩ := hd.edge_inter (Set.mem_univ _) (Set.mem_univ _) hef hp.1 hp.2
    exact ⟨hpe.eq_or_eq_of_isLink (isLink_of_pair hepair),
      hpf.eq_or_eq_of_isLink (isLink_of_pair hfpair)⟩

/-- Every genuine K₅ arc configuration has a polygonal redrawing on exactly
the same five points. No graph realization or edge-straightening assumption
is left in the conclusion. -/
theorem exists_polygonal (h : IsArcK5 x P) :
    ∃ P' : Fin 5 → Fin 5 → Set Plane, IsArcK5 x P' ∧
      ∀ i j,i ≠ j → IsPolygonal (P' i j) := by
  obtain ⟨drawing,hd,hpoly⟩ := polygonal_redrawing (k5ArcGraph x) h.arcDrawing h.isDrawing
  refine ⟨edgeFamily drawing,of_drawing h.injective hd,?_⟩
  intro i j hij
  obtain ⟨e,he,_⟩ := edgeFamily_edge drawing i j hij
  rw [he]
  exact hpoly e (Set.mem_univ _)

end IsArcK5
end Graph
