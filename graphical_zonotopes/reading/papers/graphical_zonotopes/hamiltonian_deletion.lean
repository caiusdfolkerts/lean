module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

/-! A Hamiltonian cycle leaves at most |S| components after deletion of a
nonempty vertex set S. The proof counts the components visited by a walk;
it uses the actual graph and its actual induced deletion. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.HamiltonianDeletion
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev deleted (G : SimpleGraph V) (S : Finset V) :=
  G.induce {v | v ∉ S}

def componentLabel (G : SimpleGraph V) (S : Finset V) (v : V) :
    Option (deleted G S).ConnectedComponent :=
  if h : v ∈ S then none else some ((deleted G S).connectedComponentMk ⟨v,h⟩)

def walkComponents (G : SimpleGraph V) (S : Finset V) {a b : V} (p : G.Walk a b) :
    Finset (deleted G S).ConnectedComponent :=
  (p.support.filterMap (componentLabel G S)).toFinset

theorem start_component_mem (G : SimpleGraph V) (S : Finset V) {a b : V}
    (p : G.Walk a b) (ha : a ∉ S) :
    (deleted G S).connectedComponentMk ⟨a,ha⟩ ∈ walkComponents G S p := by
  simp only [walkComponents,List.mem_toFinset,List.mem_filterMap]
  exact ⟨a,p.start_mem_support,by simp [componentLabel,ha]⟩

/-- Every deleted occurrence can start at most one new surviving component.
If the walk starts outside the deleted set, its initial component contributes
the sole extra term. No simplicity assumption on the walk is needed. -/
theorem walk_component_count_le (G : SimpleGraph V) (S : Finset V) {a b : V}
    (p : G.Walk a b) :
    (walkComponents G S p).card ≤ p.support.countP (fun v => v ∈ S)+
      if a ∈ S then 0 else 1 := by
  induction p with
  | @nil v =>
    by_cases hv : v ∈ S <;> simp [walkComponents,componentLabel,hv]
  | @cons a b c hab p ih =>
    by_cases ha : a ∈ S
    · have hw : walkComponents G S (.cons hab p)=walkComponents G S p := by
        simp [walkComponents,componentLabel,ha]
      rw [hw]
      by_cases hb : b ∈ S <;>
        simp [hb] at ih <;> simp [SimpleGraph.Walk.support_cons,ha] <;> omega
    · have hw : walkComponents G S (.cons hab p)=
          insert ((deleted G S).connectedComponentMk ⟨a,ha⟩) (walkComponents G S p) := by
        simp [walkComponents,componentLabel,ha]
      rw [hw]
      by_cases hb : b ∈ S
      · have hc := card_insert_le ((deleted G S).connectedComponentMk ⟨a,ha⟩)
          (walkComponents G S p)
        simp [hb] at ih
        simp [SimpleGraph.Walk.support_cons,ha]
        omega
      · have he : (deleted G S).connectedComponentMk ⟨a,ha⟩=
            (deleted G S).connectedComponentMk ⟨b,hb⟩ :=
          SimpleGraph.ConnectedComponent.sound
            ((show (deleted G S).Adj ⟨a,ha⟩ ⟨b,hb⟩ from hab).reachable)
        have hm := start_component_mem G S p hb
        rw [←he] at hm
        rw [insert_eq_of_mem hm]
        simpa [SimpleGraph.Walk.support_cons,ha,hb] using ih

theorem hamiltonian_walk_components (G : SimpleGraph V) (S : Finset V) {a b : V}
    {p : G.Walk a b} (hp : p.IsHamiltonian) : walkComponents G S p=univ := by
  apply eq_univ_iff_forall.mpr
  intro C
  induction C using SimpleGraph.ConnectedComponent.ind
  rename_i v
  have hv : v.1 ∉ S := v.2
  simp only [walkComponents,List.mem_toFinset,List.mem_filterMap]
  exact ⟨v.1,hp.mem_support v.1,by simp [componentLabel,hv]⟩

theorem hamiltonian_deleted_count (G : SimpleGraph V) (S : Finset V) {a b : V}
    {p : G.Walk a b} (hp : p.IsHamiltonian) :
    p.support.countP (fun v => v ∈ S)=S.card := by
  have h := hp.isPath.support_nodup.card_eq_countP (P := fun v => v ∈ S)
  rw [hp.toFinset_support] at h
  simpa using h.symm

/-- The usual toughness bound for a Hamiltonian graph, derived directly from
a Hamiltonian cycle and valid for every nonempty deletion set. -/
theorem hamiltonian_component_card_delete_le (G : SimpleGraph V)
    (hG : G.IsHamiltonian) (hn : 2 ≤ Fintype.card V)
    (S : Finset V) (hS : S.Nonempty) :
    Nat.card (G.induce ((S : Set V)ᶜ)).ConnectedComponent ≤ S.card := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨a,ha⟩ := hS
  obtain ⟨p,hp⟩ := hG.exists_isHamiltonianCycle a
  have hpath := hp.isHamiltonian_dropLast
  have h := walk_component_count_le G S p.dropLast
  rw [hamiltonian_walk_components G S hpath,
    hamiltonian_deleted_count G S hpath] at h
  change Nat.card (deleted G S).ConnectedComponent ≤ S.card
  simpa only [ha,ite_true,add_zero,card_univ,Nat.card_eq_fintype_card] using h

end GraphicalZonotopes.HamiltonianDeletion
