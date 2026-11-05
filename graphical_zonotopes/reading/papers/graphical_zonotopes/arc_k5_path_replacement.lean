import Papers.GraphicalZonotopes.ArcK5Definitions
import Schoenflies.Graph.CycleJordan

noncomputable section
open Set Schoenflies
open scoped Graph Classical
namespace Graph

/-- The single edge represented by a possibly subdivided path. -/
def IsApexPair (i j : Fin 5) : Prop := (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3)

@[simp] theorem isApexPair_comm (i j : Fin 5) : IsApexPair i j ↔ IsApexPair j i := by
  simp only [IsApexPair]
  tauto

def apexPathFamily {β : Type*} (drawing : β → ℝ → Plane)
    (e : Fin 5 → Fin 5 → β) (W : List β) (i j : Fin 5) : Set Plane :=
  if IsApexPair i j then edgesCover drawing W else edgeArc drawing (e i j)

/-- A finite drawing with all the edges of K₅ except the last one, together
with a path joining the missing endpoints and avoiding the other three
vertices, gives a genuine ten-arc K₅ configuration. -/
theorem IsDrawing.arcK5_of_apex_path {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} (hd : IsDrawing G drawing)
    (x : Fin 5 → Plane) (hx : Function.Injective x)
    (hvertex : ∀ i,x i ∈ V(G)) (e : Fin 5 → Fin 5 → β)
    (hesymm : ∀ i j,e i j = e j i)
    (helink : ∀ i j,i ≠ j → ¬ IsApexPair i j → G.IsLink (e i j) (x i) (x j))
    (W : List β) (hpath : G.IsPath (x 3) W (x 4))
    (havoid : ∀ i : Fin 3,x ⟨i.1,by omega⟩ ∉ edgesCover drawing W) :
    IsArcK5 x (apexPathFamily drawing e W) := by
  classical
  let A := edgesCover drawing W
  have hA : IsArcBetween A (x 3) (x 4) := by
    apply hd.path_isArcBetween hpath
    intro hnil
    have heq := (hnil ▸ hpath.isWalk).eq_of_nil
    have h34 : (3 : Fin 5) ≠ 4 := by decide
    exact h34 (hx heq)
  have hAV : ∀ k : Fin 5,x k ∈ A → k = 3 ∨ k = 4 := by
    intro k hk
    by_cases hlt : k.1 < 3
    · exact False.elim (havoid ⟨k.1,hlt⟩ hk)
    · have hcases : k.1 = 3 ∨ k.1 = 4 := by omega
      exact hcases.imp Fin.ext Fin.ext
  have htriangleEnd : ∀ i j : Fin 5,i ≠ j → ¬ IsApexPair i j →
      i.1 < 3 ∨ j.1 < 3 := by
    intro i j hij hbad
    by_contra hno
    push_neg at hno
    have hi : i = 3 ∨ i = 4 := by
      have hh : i.1 = 3 ∨ i.1 = 4 := by omega
      exact hh.imp Fin.ext Fin.ext
    have hj : j = 3 ∨ j = 4 := by
      have hh : j.1 = 3 ∨ j.1 = 4 := by omega
      exact hh.imp Fin.ext Fin.ext
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact hij rfl
    · exact hbad (Or.inl ⟨rfl,rfl⟩)
    · exact hbad (Or.inr ⟨rfl,rfl⟩)
    · exact hij rfl
  have hnotW : ∀ i j : Fin 5,∀ hij : i ≠ j,∀ hbad : ¬ IsApexPair i j,e i j ∉ W := by
    intro i j hij hbad heW
    have he := helink i j hij hbad
    have hArc := hd.edge_isArcBetween he
    rcases htriangleEnd i j hij hbad with hi | hj
    · exact havoid ⟨i.1,hi⟩ (mem_edgesCover heW hArc.left_mem)
    · exact havoid ⟨j.1,hj⟩ (mem_edgesCover heW hArc.right_mem)
  have hcross : ∀ i j : Fin 5,i ≠ j → ¬ IsApexPair i j →
      A ∩ edgeArc drawing (e i j) ⊆ ({x 3,x 4} : Set Plane) ∩ {x i,x j} := by
    intro i j hij hbad z hz
    obtain ⟨f,hf,hzf⟩ := mem_edgesCover_iff.mp hz.1
    have he := helink i j hij hbad
    have hef : e i j ≠ f := fun hh => hnotW i j hij hbad (hh.symm ▸ hf)
    obtain ⟨_,hze,_⟩ := hd.edge_inter he.edge_mem (hpath.edge_mem hf) hef hz.2 hzf
    have hends := hze.eq_or_eq_of_isLink he
    refine ⟨?_,hends⟩
    rcases hends with rfl | rfl
    · exact (hAV i hz.1).imp (congrArg x) (congrArg x)
    · exact (hAV j hz.1).imp (congrArg x) (congrArg x)
  have hbadends : ∀ i j,IsApexPair i j → ({x i,x j} : Set Plane) = {x 3,x 4} := by
    intro i j hbad
    rcases hbad with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact Set.pair_comm _ _
  constructor
  · exact hx
  · intro i j hij
    by_cases hbad : IsApexPair i j
    · rw [apexPathFamily,if_pos hbad]
      rcases hbad with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hA
      · exact hA.reverse
    · rw [apexPathFamily,if_neg hbad]
      exact hd.edge_isArcBetween (helink i j hij hbad)
  · intro i j
    simp only [apexPathFamily,isApexPair_comm i j,hesymm i j]
  · intro i j k hij hk
    by_cases hbad : IsApexPair i j
    · rw [apexPathFamily,if_pos hbad] at hk
      have hkv := hAV k hk
      rcases hbad with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hkv
      · exact hkv.symm
    · rw [apexPathFamily,if_neg hbad] at hk
      exact (hd.vertex_mem_edgeArc (helink i j hij hbad) (hvertex k) hk).imp
        (fun hh => hx hh) (fun hh => hx hh)
  · intro i j k l hij hkl hpairs hreverse
    by_cases hbad1 : IsApexPair i j
    · by_cases hbad2 : IsApexPair k l
      · rcases hbad1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
          rcases hbad2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact False.elim (hpairs rfl)
        · exact False.elim (hreverse rfl)
        · exact False.elim (hreverse rfl)
        · exact False.elim (hpairs rfl)
      · rw [apexPathFamily,if_pos hbad1,apexPathFamily,if_neg hbad2,hbadends i j hbad1]
        exact hcross k l hkl hbad2
    · by_cases hbad2 : IsApexPair k l
      · rw [apexPathFamily,if_neg hbad1,apexPathFamily,if_pos hbad2,hbadends k l hbad2]
        intro z hz
        exact (hcross i j hij hbad1 ⟨hz.2,hz.1⟩).symm
      · rw [apexPathFamily,if_neg hbad1,apexPathFamily,if_neg hbad2]
        intro z hz
        have he1 := helink i j hij hbad1
        have he2 := helink k l hkl hbad2
        have hef : e i j ≠ e k l := by
          intro heq
          have he2' : G.IsLink (e i j) (x k) (x l) := heq.symm ▸ he2
          rcases he1.eq_and_eq_or_eq_and_eq he2' with ⟨h1,h2⟩ | ⟨h1,h2⟩
          · exact hpairs (Prod.ext (hx h1) (hx h2))
          · exact hreverse (Prod.ext (hx h1) (hx h2))
        obtain ⟨_,hze,hzf⟩ := hd.edge_inter he1.edge_mem he2.edge_mem hef hz.1 hz.2
        exact ⟨hze.eq_or_eq_of_isLink he1,hzf.eq_or_eq_of_isLink he2⟩

end Graph
