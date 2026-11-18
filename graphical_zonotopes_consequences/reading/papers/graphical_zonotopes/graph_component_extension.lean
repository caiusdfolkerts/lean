module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Option
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace VertexExtension
variable {V : Type*} {W : Type*}

/-- Add one vertex, with exactly the specified neighbors. The old vertex
type is retained as `some`, and the new vertex is `none`. -/
def graph (G : SimpleGraph V) (N : Set V) : SimpleGraph (Option V) where
  Adj a b := match a,b with
    | none,some v => v∈N
    | some v,none => v∈N
    | some v,some w => G.Adj v w
    | none,none => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp [G.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp [G.irrefl]⟩

def someHom (G : SimpleGraph V) (N : Set V) : G →g graph G N where
  toFun := Option.some
  map_rel' := fun h => h

/-- A label constant on each edge descends to the actual connected-component
quotient. In particular, this does not assert that the labels define a graph
homomorphism, which would fail when an edge is collapsed to one vertex. -/
def componentLift (G : SimpleGraph V) (f : V → W)
    (hf : ∀ u v,G.Adj u v → f u=f v) : G.ConnectedComponent → W :=
  Quot.lift f (by
    intro u v hp
    rw [SimpleGraph.reachable_eq_reflTransGen] at hp
    induction hp with
    | refl => rfl
    | @tail v w hp hvw ih => exact ih.trans (hf v w hvw))

@[simp] theorem componentLift_mk (G : SimpleGraph V) (f : V → W)
    (hf : ∀ u v,G.Adj u v → f u=f v) (u : V) :
    componentLift G f hf (G.connectedComponentMk u)=f u := rfl

def oldLabel (G : SimpleGraph V) (v₀ : V) : Option V → G.ConnectedComponent
  | none => G.connectedComponentMk v₀
  | some v => G.connectedComponentMk v

theorem oldLabel_adj (G : SimpleGraph V) (N : Set V) (v₀ : V)
    (hv₀ : v₀∈N) (hN : G.IsClique N) :
    ∀ a b,(graph G N).Adj a b → oldLabel G v₀ a=oldLabel G v₀ b := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => exact False.elim hab
    | some v =>
      by_cases he : v₀=v
      · simp [oldLabel,he]
      · exact SimpleGraph.ConnectedComponent.sound (hN hv₀ hab he).reachable
  | some u =>
    cases b with
    | none =>
      by_cases he : u=v₀
      · simp [oldLabel,he]
      · exact SimpleGraph.ConnectedComponent.sound (hN hab hv₀ he).reachable
    | some v =>
        change G.Adj u v at hab
        exact SimpleGraph.ConnectedComponent.sound hab.reachable

/-- Attaching a vertex to a nonempty clique preserves all actual connected
components, including any other disconnected components of the old graph. -/
def componentEquiv (G : SimpleGraph V) (N : Set V) (v₀ : V)
    (hv₀ : v₀∈N) (hN : G.IsClique N) :
    (graph G N).ConnectedComponent ≃ G.ConnectedComponent where
  toFun := componentLift (graph G N) (oldLabel G v₀) (oldLabel_adj G N v₀ hv₀ hN)
  invFun := SimpleGraph.ConnectedComponent.map (someHom G N)
  left_inv := by
    intro c
    refine c.ind ?_
    intro v
    cases v with
    | none =>
      exact SimpleGraph.ConnectedComponent.sound
        (show (graph G N).Reachable (some v₀) none from
          (SimpleGraph.Adj.reachable (show (graph G N).Adj (some v₀) none from hv₀)))
    | some v => rfl
  right_inv := by
    intro c
    exact c.ind (fun _ => rfl)

theorem component_card (G : SimpleGraph V) (N : Set V)
    (hne : N.Nonempty) (hN : G.IsClique N) :
    Nat.card (graph G N).ConnectedComponent=Nat.card G.ConnectedComponent := by
  obtain ⟨v₀,hv₀⟩:=hne
  exact Nat.card_congr (componentEquiv G N v₀ hv₀ hN)

def isolatedLabel (G : SimpleGraph V) : Option V → Option G.ConnectedComponent
  | none => none
  | some v => some (G.connectedComponentMk v)

theorem isolatedLabel_adj (G : SimpleGraph V) :
    ∀ a b,(graph G ∅).Adj a b → isolatedLabel G a=isolatedLabel G b := by
  intro a b hab
  cases a <;> cases b
  · exact False.elim hab
  · exact False.elim hab
  · exact False.elim hab
  · rename_i u v
    change G.Adj u v at hab
    exact congrArg Option.some (SimpleGraph.ConnectedComponent.sound hab.reachable)

/-- Adding an isolated vertex adds exactly one new connected component. -/
def isolatedComponentEquiv (G : SimpleGraph V) :
    (graph G ∅).ConnectedComponent ≃ Option G.ConnectedComponent where
  toFun := componentLift (graph G ∅) (isolatedLabel G) (isolatedLabel_adj G)
  invFun := fun c => match c with
    | none => (graph G ∅).connectedComponentMk none
    | some c => c.map (someHom G ∅)
  left_inv := by
    intro c
    refine c.ind ?_
    intro v
    cases v <;> rfl
  right_inv := by
    intro c
    cases c with
    | none => rfl
    | some c => exact c.ind (fun _ => rfl)

theorem isolated_component_card (G : SimpleGraph V) [Finite V] :
    Nat.card (graph G ∅).ConnectedComponent=Nat.card G.ConnectedComponent+1 := by
  classical
  letI : Fintype G.ConnectedComponent:=Fintype.ofFinite _
  rw [Nat.card_congr (isolatedComponentEquiv G),Nat.card_eq_fintype_card,
    Fintype.card_option,Nat.card_eq_fintype_card]

theorem connected (G : SimpleGraph V) (N : Set V)
    (hG : G.Connected) (hne : N.Nonempty) : (graph G N).Connected := by
  obtain ⟨v₀,hv₀⟩:=hne
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none,?_⟩
  intro v
  cases v with
  | none => exact SimpleGraph.Reachable.rfl
  | some v =>
    exact (SimpleGraph.Adj.reachable (show (graph G N).Adj none (some v₀) from hv₀)).trans
      ((hG v₀ v).map (someHom G N))

theorem connected_component_card_one {G : SimpleGraph V} (hG : G.Connected) :
    Nat.card G.ConnectedComponent=1 := by
  letI : Nonempty V:=hG.nonempty
  letI : Subsingleton G.ConnectedComponent:=hG.preconnected.subsingleton_connectedComponent
  exact Nat.card_unique

end VertexExtension
end GraphicalZonotopes
