module

public import Papers.GraphicalZonotopes.ThreeTreeLink
public import Papers.GraphicalZonotopes.EdgeCoordinates

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem linkPair_excludes_endpoints {G : SimpleGraph V} {u v : V} {E : Finset V}
    (hE : E∈edgeFamily (edgeLink G u v)) : u∉E ∧ v∉E := by
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hE
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  have he := hcl a (by simp) b (by simp) hab
  exact ⟨by simp [G.ne_of_adj he.2.1,G.ne_of_adj he.2.2.2.1],
    by simp [G.ne_of_adj he.2.2.1,G.ne_of_adj he.2.2.2.2]⟩

theorem tetrahedron_of_linkPair {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    {E : Finset V} (hE : E∈edgeFamily (edgeLink G u v)) :
    insert u (insert v E)∈tetrahedra G := by
  classical
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hE
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  have he := hcl a (by simp) b (by simp) hab
  have hua := G.ne_of_adj he.2.1
  have hub := G.ne_of_adj he.2.2.2.1
  have hva := G.ne_of_adj he.2.2.1
  have hvb := G.ne_of_adj he.2.2.2.2
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_,?_⟩
  · simp [huv.ne,hua,hub,hva,hvb,hab]
  · intro x hx y hy hxy
    change x ∈ (insert u (insert v {a,b}) : Finset V) at hx
    change y ∈ (insert u (insert v {a,b}) : Finset V) at hy
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact False.elim (hxy rfl) | exact huv | exact huv.symm |
        exact he.1 | exact he.1.symm | exact he.2.1 | exact he.2.1.symm |
        exact he.2.2.1 | exact he.2.2.1.symm | exact he.2.2.2.1 |
        exact he.2.2.2.1.symm | exact he.2.2.2.2 | exact he.2.2.2.2.symm

theorem linkPair_of_tetrahedron {G : SimpleGraph V} {u v : V} (huv : u≠v)
    {C : Finset V} (hC : C∈tetrahedra G) (huC : u∈C) (hvC : v∈C) :
    (C.erase u).erase v∈edgeFamily (edgeLink G u v) := by
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
  apply (mem_edgeFamily _ _).mpr
  refine ⟨?_,?_⟩
  · rw [card_erase_of_mem (mem_erase.mpr ⟨huv.symm,hvC⟩),
      card_erase_of_mem huC,hc]
  · intro a ha b hb hab
    obtain ⟨hav,ha'⟩ := mem_erase.mp ha
    obtain ⟨hau,haC⟩ := mem_erase.mp ha'
    obtain ⟨hbv,hb'⟩ := mem_erase.mp hb
    obtain ⟨hbu,hbC⟩ := mem_erase.mp hb'
    exact ⟨hcl haC hbC hab,hcl huC haC hau.symm,hcl hvC haC hav.symm,
      hcl huC hbC hbu.symm,hcl hvC hbC hbv.symm⟩

def tetrahedraContaining (G : SimpleGraph V) (u v : V) : Finset (Finset V) := by
  classical
  exact (tetrahedra G).filter (fun C => u∈C ∧ v∈C)

/-- Every tetrahedron through an actual edge corresponds to exactly one
edge of its common-neighbor graph, with no omitted interaction or duplicate
coefficient. This is the coordinate dictionary used by the Boolean kernel
and lattice-oscillation arguments. -/
def tetrahedronLinkEquiv (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    ↥(tetrahedraContaining G u v) ≃ ↥(edgeFamily (edgeLink G u v)) where
  toFun C := ⟨(C.1.erase u).erase v,linkPair_of_tetrahedron huv.ne
    (mem_filter.mp C.2).1 (mem_filter.mp C.2).2.1 (mem_filter.mp C.2).2.2⟩
  invFun E := ⟨insert u (insert v E.1),mem_filter.mpr
    ⟨tetrahedron_of_linkPair huv E.2,by simp,by simp⟩⟩
  left_inv C := by
    apply Subtype.ext
    have huC := (mem_filter.mp C.2).2.1
    have hvC := (mem_filter.mp C.2).2.2
    ext x
    by_cases hxu : x=u <;> by_cases hxv : x=v <;> simp [hxu,hxv,huC,hvC]
  right_inv E := by
    apply Subtype.ext
    obtain ⟨huE,hvE⟩ := linkPair_excludes_endpoints E.2
    simp [huv.ne,huE,hvE]

theorem tetrahedronLink_card (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    (tetrahedraContaining G u v).card=(edgeLink G u v).edgeFinset.card := by
  have he := Fintype.card_congr (tetrahedronLinkEquiv G huv)
  simp only [Fintype.card_coe] at he
  rw [he,edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]

end GraphicalZonotopes
