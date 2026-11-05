module

public import Continuation.CycleBounds.PathBridges
public import Mathlib.Data.Finset.Union

@[expose] public section

/-! # Six internally disjoint graph walks produce a literal K4 minor -/

noncomputable section
open Set
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E : Type*}

theorem connectedIn_of_chain {G : IncidenceGraph V E} (a : V) (w : List V)
    (h : (a :: w).IsChain (Adj G)) {x : V} (hx : x ∈ a :: w) :
    ConnectedIn G (a :: w).toFinset a x := by
  have h' : (a :: w).IsChain (fun u v ↦ u ∈ a :: w ∧ v ∈ a :: w ∧ Adj G u v) :=
    List.IsChain.iff_mem.mp h
  exact h'.induction (fun y ↦ ConnectedIn G (a :: w).toFinset a y) (a :: w)
    (fun _ _ huv hp ↦ hp.tail ⟨List.mem_toFinset.mpr huv.1,
      List.mem_toFinset.mpr huv.2.1, huv.2.2⟩) (fun _ ↦ .refl) x hx

/-- A topological K4 model described by six ordinary graph walks. Internal
vertices avoid the four endpoints and the other five walks. Walks may have
repetitions in their own interior; this harmless generality simplifies extraction. -/
structure K4Subdivision (G : IncidenceGraph V E) where
  vertex : Option (Fin 3) ↪ V
  inside : Fin 6 → List V
  chain : ∀ e, ((vertex (K4Network.source e) :: inside e) ++
    [vertex (K4Network.target e)]).IsChain (Adj G)
  avoids : ∀ e i, vertex i ∉ inside e
  disjoint : ∀ e f, e ≠ f → ∀ x ∈ inside e, x ∉ inside f

namespace K4Subdivision
variable {G : IncidenceGraph V E} (D : K4Subdivision G)

/-- Allocate each path interior to its initial endpoint. -/
def branch (i : Option (Fin 3)) : Finset V :=
  insert (D.vertex i) (Finset.univ.biUnion (fun e : Fin 6 ↦
    if K4Network.source e = i then (D.inside e).toFinset else ∅))

theorem mem_branch (i : Option (Fin 3)) (x : V) :
    x ∈ D.branch i ↔ x = D.vertex i ∨
      ∃ e, K4Network.source e = i ∧ x ∈ D.inside e := by
  classical
  rw [branch, Finset.mem_insert, Finset.mem_biUnion]
  constructor
  · rintro (hx | ⟨e, _, hx⟩)
    · exact Or.inl hx
    · by_cases he : K4Network.source e = i
      · rw [if_pos he] at hx
        exact Or.inr ⟨e, he, List.mem_toFinset.mp hx⟩
      · rw [if_neg he] at hx
        simpa using hx
  · rintro (hx | ⟨e, he, hx⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨e, Finset.mem_univ e, by rw [if_pos he]; exact List.mem_toFinset.mpr hx⟩

theorem branch_disjoint (i j : Option (Fin 3)) (hij : i ≠ j) :
    Disjoint (D.branch i) (D.branch j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  rcases (D.mem_branch i x).mp hxi with hxi | ⟨e, hei, hxe⟩ <;>
    rcases (D.mem_branch j x).mp hxj with hxj | ⟨f, hfj, hxf⟩
  · exact hij (D.vertex.injective (hxi.symm.trans hxj))
  · exact D.avoids f i (hxi ▸ hxf)
  · exact D.avoids e j (hxj ▸ hxe)
  · by_cases hef : e = f
    · subst f
      exact hij (hei.symm.trans hfj)
    · exact D.disjoint e f hef x hxe hxf

theorem center_connected (i : Option (Fin 3)) (x : V) (hx : x ∈ D.branch i) :
    ConnectedIn G (D.branch i) (D.vertex i) x := by
  rcases (D.mem_branch i x).mp hx with rfl | ⟨e, hei, hxe⟩
  · exact .refl
  · have hchain : (D.vertex i :: D.inside e).IsChain (Adj G) := by
      simpa only [hei] using (D.chain e).left_of_append
    apply (connectedIn_of_chain (D.vertex i) (D.inside e) hchain
      (List.mem_cons_of_mem _ hxe)).mono
    intro y hy
    rcases List.mem_cons.mp (List.mem_toFinset.mp hy) with rfl | hye
    · exact (D.mem_branch i _).mpr (Or.inl rfl)
    · exact (D.mem_branch i _).mpr (Or.inr ⟨e, hei, hye⟩)

theorem path_between (e : Fin 6) :
    ∃ f ∈ G.edges,
      (G.source f ∈ D.branch (K4Network.source e) ∧
        G.target f ∈ D.branch (K4Network.target e)) ∨
      (G.source f ∈ D.branch (K4Network.target e) ∧
        G.target f ∈ D.branch (K4Network.source e)) := by
  let l := D.vertex (K4Network.source e) :: D.inside e
  have hne : l ≠ [] := by simp [l]
  let x := l.getLast hne
  have hx : x ∈ D.branch (K4Network.source e) := by
    rcases List.mem_cons.mp (List.getLast_mem hne) with hx | hx
    · exact (D.mem_branch _ _).mpr (Or.inl hx)
    · exact (D.mem_branch _ _).mpr (Or.inr ⟨e, rfl, hx⟩)
  have hy : D.vertex (K4Network.target e) ∈ D.branch (K4Network.target e) :=
    (D.mem_branch _ _).mpr (Or.inl rfl)
  have hxy : Adj G x (D.vertex (K4Network.target e)) := by
    exact (D.chain e).rel_getLast_head_of_append hne (by simp)
  obtain ⟨_, f, hf, hor⟩ := hxy
  refine ⟨f, hf, ?_⟩
  rcases hor with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact Or.inl ⟨hs.symm ▸ hx, ht.symm ▸ hy⟩
  · exact Or.inr ⟨hs.symm ▸ hy, ht.symm ▸ hx⟩

include D in
/-- Every topological K4 model has a literal K4 graph minor. -/
theorem hasK4Minor : G.HasK4Minor := by
  let B : K4BranchModel G := K4BranchModel.ofDisjoint D.branch
    (fun i ↦ ⟨D.vertex i, (D.mem_branch i _).mpr (Or.inl rfl)⟩)
    D.branch_disjoint
    (fun i a ha b hb ↦ (D.center_connected i a ha).symm.trans (D.center_connected i b hb))
    (by
      intro i j hij
      obtain ⟨e, he⟩ := K4Network_complete i j hij
      have hh := D.path_between e
      rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · simpa only [hs, ht] using hh
      · obtain ⟨f, hf, hor⟩ := hh
        exact ⟨f, hf, by simpa only [hs, ht, or_comm] using hor⟩)
  exact B.hasK4Minor

end K4Subdivision
end Unimodular.CycleBounds
