module

public import Papers.GraphicalZonotopes.PlanarDrawing
public import Papers.GraphicalZonotopes.ArcK5PathReplacement
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical Graph
namespace GraphicalZonotopes
open Finset Schoenflies
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual graph path avoiding a prescribed finite set is realized by a
simple plane arc avoiding the corresponding points. The proof transports
Mathlib walks to the library's edge-list walks, then shortens them without
adding an edge. -/
theorem PlaneDrawing.avoiding_path {G : SimpleGraph V} {p : V → Plane}
    (hp : Function.Injective p) {drawing : Sym2 V → ℝ → Plane}
    (hd : Graph.IsDrawing (planeGraph G p) drawing)
    (T : Finset V) (u w : V) (hu : u ∉ T) (hw : w ∉ T)
    (hreach : (G.induce ((T : Set V)ᶜ)).Reachable ⟨u,hu⟩ ⟨w,hw⟩) :
    ∃ W : List (Sym2 V),(planeGraph G p).IsPath (p u) W (p w) ∧
      ∀ t ∈ T,p t ∉ Graph.edgesCover drawing W := by
  let H := planeGraph G p
  have aux : ∀ {a b : ↥((T : Set V)ᶜ)},(G.induce ((T : Set V)ᶜ)).Walk a b →
      ∃ W : List (Sym2 V),H.IsWalk (p a.1) W (p b.1) ∧
        ∀ e ∈ W,∃ r s : V,r ∉ T ∧ s ∉ T ∧ H.IsLink e (p r) (p s) := by
    intro a b q
    induction q with
    | @nil a =>
      refine ⟨[],Graph.IsWalk.nil ?_,?_⟩
      · change p a.1 ∈ V(planeGraph G p)
        rw [planeGraph_vertexSet]
        exact ⟨a.1,rfl⟩
      · intro e he
        simp at he
    | @cons a b c hab q ih =>
      obtain ⟨W,hW,hends⟩ := ih
      have hl : H.IsLink s(a.1,b.1) (p a.1) (p b.1) :=
        (planeGraph_isLink G p hp _ _ _).mpr ⟨rfl,hab⟩
      refine ⟨s(a.1,b.1)::W,Graph.IsWalk.cons hl hW,?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨a.1,b.1,a.2,b.2,hl⟩
      · exact hends e he
  obtain ⟨W,hW,hends⟩ := aux hreach.some
  obtain ⟨P,hP,hPW⟩ := hW.contains_path
  refine ⟨P,hP,?_⟩
  intro t ht hmem
  obtain ⟨e,he,hte⟩ := Graph.mem_edgesCover_iff.mp hmem
  obtain ⟨r,s,hr,hs,hl⟩ := hends e (hPW he)
  have hv : p t ∈ V(H) := by
    change p t ∈ V(planeGraph G p)
    rw [planeGraph_vertexSet]
    exact ⟨t,rfl⟩
  rcases hd.vertex_mem_edgeArc hl hv hte with htr | hts
  · exact hr (hp htr ▸ ht)
  · exact hs (hp hts ▸ ht)

/-- The forbidden configuration behind the planar triangle-apex separation:
a triangle, two distinct vertices complete to it, and a path joining those
two vertices away from the triangle yield ten genuine noncrossing K₅ arcs. -/
theorem HasPlaneDrawing.arcK5_of_triangle_apex_path {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (T : Finset V) (hT : T.card = 3) (hcT : G.IsClique T)
    (u w : V) (hu : u ∉ T) (hw : w ∉ T) (huw : u ≠ w)
    (huAdj : ∀ t ∈ T,G.Adj u t) (hwAdj : ∀ t ∈ T,G.Adj w t)
    (hreach : (G.induce ((T : Set V)ᶜ)).Reachable ⟨u,hu⟩ ⟨w,hw⟩) :
    ∃ (x : Fin 5 → Plane) (P : Fin 5 → Fin 5 → Set Plane),Graph.IsArcK5 x P := by
  obtain ⟨p,hp,drawing,hd⟩ := hG
  obtain ⟨W,hpath,havoid⟩ := PlaneDrawing.avoiding_path hp hd T u w hu hw hreach
  obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := card_eq_three.mp hT
  have haT : a ∈ T := by rw [hTabc]; simp
  have hbT : b ∈ T := by rw [hTabc]; simp
  have hcT' : c ∈ T := by rw [hTabc]; simp
  have hua : u ≠ a := fun he => hu (he.symm ▸ haT)
  have hub : u ≠ b := fun he => hu (he.symm ▸ hbT)
  have huc : u ≠ c := fun he => hu (he.symm ▸ hcT')
  have hwa : w ≠ a := fun he => hw (he.symm ▸ haT)
  have hwb : w ≠ b := fun he => hw (he.symm ▸ hbT)
  have hwc : w ≠ c := fun he => hw (he.symm ▸ hcT')
  let names : Fin 5 → V := ![a,b,c,u,w]
  let x : Fin 5 → Plane := p ∘ names
  let e : Fin 5 → Fin 5 → Sym2 V := fun i j => s(names i,names j)
  have hnames : Function.Injective names := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [names]
  have hxab := hcT haT hbT hab
  have hxac := hcT haT hcT' hac
  have hxbc := hcT hbT hcT' hbc
  have hxuA := huAdj a haT
  have hxuB := huAdj b hbT
  have hxuC := huAdj c hcT'
  have hxwA := hwAdj a haT
  have hxwB := hwAdj b hbT
  have hxwC := hwAdj c hcT'
  have hadj : ∀ i j : Fin 5,i ≠ j → ¬ Graph.IsApexPair i j → G.Adj (names i) (names j) := by
    intro i j hij hbad
    fin_cases i <;> fin_cases j <;>
      simp_all [names,Graph.IsApexPair,SimpleGraph.adj_comm]
  have hvertex : ∀ i,x i ∈ V(PlaneDrawing.planeGraph G p) := by
    intro i
    rw [PlaneDrawing.planeGraph_vertexSet]
    exact ⟨names i,rfl⟩
  have he : ∀ i j : Fin 5,i ≠ j → ¬ Graph.IsApexPair i j →
      (PlaneDrawing.planeGraph G p).IsLink (e i j) (x i) (x j) := by
    intro i j hij hbad
    exact (PlaneDrawing.planeGraph_isLink G p hp _ _ _).mpr ⟨rfl,hadj i j hij hbad⟩
  have hpath' : (PlaneDrawing.planeGraph G p).IsPath (x 3) W (x 4) := by
    simpa [x,names] using hpath
  have havoid' : ∀ i : Fin 3,x ⟨i.1,by omega⟩ ∉ Graph.edgesCover drawing W := by
    intro i
    apply havoid
    fin_cases i <;> simp [names,hTabc]
  exact ⟨x,Graph.apexPathFamily drawing e W,hd.arcK5_of_apex_path x (hp.comp hnames)
    hvertex e (fun i j => Sym2.eq_swap) he W hpath' havoid'⟩

end GraphicalZonotopes
