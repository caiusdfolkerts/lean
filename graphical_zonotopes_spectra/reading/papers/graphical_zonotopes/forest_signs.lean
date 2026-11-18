module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ForestSigns
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def IsSign (x : ℝ) : Prop := x=1 ∨ x=-1

theorem IsSign.mul {x y : ℝ} (hx : IsSign x) (hy : IsSign y) : IsSign (x*y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [IsSign]

theorem IsSign.sq {x : ℝ} (hx : IsSign x) : x^2=1 := by
  rcases hx with rfl | rfl <;> norm_num

/-- Every assignment of signs to the edges of a finite forest is realized
as products of vertex signs. The proof deletes one bridge and flips precisely
one of its two components; it includes disconnected and empty forests. -/
theorem exists_vertex_signs (G : SimpleGraph V) (hG : G.IsAcyclic)
    (ρ : V → V → ℝ) (hρ : ∀ u v,G.Adj u v → IsSign (ρ u v))
    (hρsym : ∀ u v,G.Adj u v → ρ u v=ρ v u) :
    ∃ σ : V → ℝ,(∀ v,IsSign (σ v)) ∧ ∀ u v,G.Adj u v → σ u*σ v=ρ u v := by
  classical
  suffices h : ∀ n (H : SimpleGraph V),H.edgeFinset.card=n → H.IsAcyclic →
      (∀ u v,H.Adj u v → IsSign (ρ u v)) →
      (∀ u v,H.Adj u v → ρ u v=ρ v u) →
      ∃ σ : V → ℝ,(∀ v,IsSign (σ v)) ∧ ∀ u v,H.Adj u v → σ u*σ v=ρ u v from
    h _ G rfl hG hρ hρsym
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hcard hH hρ hρsym
    by_cases hbot : H=⊥
    · subst H
      exact ⟨fun _ => 1,fun _ => Or.inl rfl,by simp⟩
    · obtain ⟨e,he⟩ := H.edgeFinset_nonempty.mpr hbot
      obtain ⟨u,v⟩ := e
      have huv : H.Adj u v := (H.mem_edgeFinset.mp he)
      let H' := H.deleteEdges ({s(u,v)} : Finset (Sym2 V))
      have hle : H' ≤ H := H.deleteEdges_le _
      have hlt : H'.edgeFinset.card<n := by
        change (H.deleteEdges ({s(u,v)} : Finset (Sym2 V))).edgeFinset.card<n
        rw [SimpleGraph.edgeFinset_deleteEdges,sdiff_singleton_eq_erase]
        have hh : (H.edgeFinset.erase s(u,v)).card < H.edgeFinset.card :=
          card_erase_lt_of_mem (show s(u,v) ∈ H.edgeFinset from he)
        exact hh.trans_eq (by simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hcard)
      obtain ⟨σ,hσ,hσedge⟩ := ih _ hlt H' (by simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]) (hH.anti hle)
        (fun x y hxy => hρ x y (hle hxy)) (fun x y hxy => hρsym x y (hle hxy))
      have hbridge := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hH) huv
      have hnotuv : ¬H'.Reachable u v := by
        simpa only [H', Finset.coe_singleton] using SimpleGraph.isBridge_iff.mp hbridge
      have hnotvu : ¬H'.Reachable v u := fun h => hnotuv h.symm
      let a : ℝ := ρ u v*σ u*σ v
      have ha : IsSign a := ((hρ u v huv).mul (hσ u)).mul (hσ v)
      let τ : V → ℝ := fun w => if H'.Reachable v w then a*σ w else σ w
      have hτ : ∀ w,IsSign (τ w) := by
        intro w
        dsimp [τ]
        split
        · exact ha.mul (hσ w)
        · exact hσ w
      have huvτ : τ u*τ v=ρ u v := by
        simp only [τ,if_neg hnotvu,SimpleGraph.Reachable.rfl,if_pos]
        dsimp [a]
        calc
          σ u*((ρ u v*σ u*σ v)*σ v)=ρ u v*(σ u)^2*(σ v)^2 := by ring
          _=ρ u v := by rw [(hσ u).sq,(hσ v).sq]; ring
      refine ⟨τ,hτ,?_⟩
      intro x y hxy
      by_cases heq : s(x,y)=s(u,v)
      · rcases Sym2.eq_iff.mp heq with heq | heq
        · obtain ⟨rfl,rfl⟩ := heq
          exact huvτ
        · obtain ⟨rfl,rfl⟩ := heq
          simpa only [mul_comm, hρsym _ _ hxy] using huvτ
      · have hxy' : H'.Adj x y := by
          refine ⟨hxy, ?_⟩
          intro he
          have hm := he.1
          change s(x,y) ∈ ({s(u,v)} : Finset (Sym2 V)) at hm
          exact heq (Finset.mem_singleton.mp hm)
        have hr : H'.Reachable v x ↔ H'.Reachable v y :=
          ⟨fun h => h.trans hxy'.reachable,fun h => h.trans hxy'.symm.reachable⟩
        by_cases hx : H'.Reachable v x
        · have hy := hr.mp hx
          simp only [τ,if_pos hx,if_pos hy]
          calc
            (a*σ x)*(a*σ y)=a^2*(σ x*σ y) := by ring
            _=ρ x y := by rw [ha.sq,hσedge x y hxy',one_mul]
        · have hy : ¬H'.Reachable v y := fun h => hx (hr.mpr h)
          simp only [τ,if_neg hx,if_neg hy]
          exact hσedge x y hxy'

end ForestSigns
end GraphicalZonotopes
