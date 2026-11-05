module

public import Papers.GraphicalZonotopes.PlanarDrawing
public import Papers.GraphicalZonotopes.TriangleApexCount
public import Schoenflies.Graph.K33Land

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Graph
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A genuine plane drawing excludes a K₃,₃ subgraph. The imported obstruction
is the closed theorem for arbitrary continuous injective edge arcs. -/
theorem HasPlaneDrawing.no_complete_bipartite_three_three {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (x y : Fin 3 → V)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j,x i ≠ y j) (hadj : ∀ i j,G.Adj (x i) (y j)) : False := by
  obtain ⟨p,hp,drawing,hd⟩ := hG
  let e : Fin 3 → Fin 3 → Sym2 V := fun i j => s(x i,y j)
  have hk : Graph.IsK33Config (PlaneDrawing.planeGraph G p) (p ∘ x) (p ∘ y) e := by
    constructor
    · intro i j
      exact (PlaneDrawing.planeGraph_isLink G p hp _ _ _).mpr ⟨rfl,hadj i j⟩
    · exact hp.comp hx
    · exact hp.comp hy
    · intro i j heq
      exact hxy i j (hp heq)
  exact hk.not_exists_isDrawing ⟨drawing,hd⟩

/-- Any three distinct vertices in a planar graph have at most two common
neighbours outside the triple. The three vertices need not themselves form
a triangle; the stronger statement is exactly the K₃,₃ obstruction. -/
theorem HasPlaneDrawing.common_apices_bound {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (T : Finset V) (hT : T.card = 3) :
    (univ.filter (fun v : V => v ∉ T ∧ ∀ t ∈ T,G.Adj v t)).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree : 2 < (univ.filter
      (fun v : V => v ∉ T ∧ ∀ t ∈ T,G.Adj v t)).card := by omega
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := two_lt_card_iff.mp hthree
  have hu' := (mem_filter.mp hu).2
  have hv' := (mem_filter.mp hv).2
  have hw' := (mem_filter.mp hw).2
  obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := card_eq_three.mp hT
  let x : Fin 3 → V := ![a,b,c]
  let y : Fin 3 → V := ![u,v,w]
  have hx : Function.Injective x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [x]
  have hy : Function.Injective y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [y]
  have hxmem : ∀ i,x i ∈ T := by
    intro i
    fin_cases i <;> simp [x,hTabc]
  have hyoutside : ∀ j,y j ∉ T := by
    intro j
    fin_cases j
    · exact hu'.1
    · exact hv'.1
    · exact hw'.1
  have hyadj : ∀ j,∀ t ∈ T,G.Adj (y j) t := by
    intro j
    fin_cases j
    · exact hu'.2
    · exact hv'.2
    · exact hw'.2
  exact hG.no_complete_bipartite_three_three x y hx hy
    (fun i j heq => hyoutside j (heq ▸ hxmem i))
    (fun i j => G.adj_symm (hyadj j _ (hxmem i)))

/-- Planarity bounds the number of tetrahedra on any triangle by two. -/
theorem HasPlaneDrawing.triangleMultiplicity_le_two {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (T : Finset V) (hT : T.card = 3)
    (hcT : G.IsClique T) : triangleMultiplicity G T ≤ 2 := by
  rw [triangleMultiplicity_eq_commonApices_card hT hcT]
  exact hG.common_apices_bound T hT

/-- In particular every planar graph satisfies the admissibility bound used
by the full three-tree theorem. -/
theorem HasPlaneDrawing.admissible {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) : Admissible G := by
  intro T hT hcT
  exact (hG.triangleMultiplicity_le_two T hT hcT).trans (by omega)

end GraphicalZonotopes
