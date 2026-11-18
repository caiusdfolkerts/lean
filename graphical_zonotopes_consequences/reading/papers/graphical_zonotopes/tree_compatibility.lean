module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Card

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
universe u v w

/-- A finite tree of nonempty local state spaces has compatible states if
every state at one end of an edge can be matched at the other end. There
are no compatibility conditions on nonedges and no chosen-root hypothesis.
This is the exact finite constraint-tree gluing step needed for the bit-row
construction, independent of its geometric application. -/
theorem tree_compatible_states {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (State : V → Type v)
    (hne : ∀ v,Nonempty (State v)) (Color : Type w)
    (port : ∀ u v,State u → Color)
    (hextend : ∀ u v,G.Adj u v → ∀ t : State v,
      ∃ s : State u,port u v s=port v u t) :
    ∃ s : ∀ v,State v,∀ u v,G.Adj u v → port u v (s u)=port v u (s v) := by
  classical
  suffices h : ∀ n,∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W),Fintype.card W=n → H.IsTree →
      ∀ (S : W → Type v),(∀ v,Nonempty (S v)) →
      ∀ (p : ∀ u v,S u → Color),
      (∀ u v,H.Adj u v → ∀ t : S v,∃ s : S u,p u v s=p v u t) →
      ∃ s : ∀ v,S v,∀ u v,H.Adj u v → p u v (s u)=p v u (s v) from
    h _ V G rfl hG State hne port hextend
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ H hcard htree S hne p hextend
    by_cases hsub : Subsingleton W
    · letI : Subsingleton W := hsub
      refine ⟨fun v => Classical.choice (hne v),?_⟩
      intro u v huv
      exact False.elim (huv.ne (Subsingleton.elim u v))
    · letI : Nontrivial W := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨r,hdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
      obtain ⟨q,hrq,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
      let W' := {x : W // x≠r}
      let H' : SimpleGraph W' := H.induce {r}ᶜ
      have htree' : H'.IsTree :=
        ⟨htree.connected.induce_compl_singleton_of_degree_eq_one hdeg,
          htree.isAcyclic.induce _⟩
      have hlt : Fintype.card W'<n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x:=r) (by simp)
      obtain ⟨s,hs⟩ := ih (Fintype.card W') hlt W' H' rfl htree'
        (fun v => S v.1) (fun v => hne v.1) (fun u v => p u.1 v.1)
        (fun u v huv t => hextend u.1 v.1 huv t)
      have hqr : q≠r := hrq.ne.symm
      obtain ⟨sr,hsr⟩ := hextend r q hrq (s ⟨q,hqr⟩)
      let t : ∀ x,S x := fun x =>
        if hx : x=r then hx.symm ▸ sr else s ⟨x,hx⟩
      have htroot : t r=sr := by simp only [t,dif_pos rfl]
      have htoff : ∀ x (hx : x≠r),t x=s ⟨x,hx⟩ := by
        intro x hx
        simp only [t,dif_neg hx]
      refine ⟨t,?_⟩
      intro u v huv
      by_cases hur : u=r
      · subst u
        have hvq : v=q := hunique v huv
        subst v
        rw [htroot,htoff q hqr]
        exact hsr
      · by_cases hvr : v=r
        · subst v
          have huq : u=q := hunique u huv.symm
          subst u
          rw [htroot,htoff q hqr]
          exact hsr.symm
        · rw [htoff u hur,htoff v hvr]
          exact hs ⟨u,hur⟩ ⟨v,hvr⟩ huv

end GraphicalZonotopes
