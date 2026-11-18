module

public import Papers.GraphicalZonotopes.FiniteMonomialCoordinates
public import Papers.GraphicalZonotopes.LocalDeltas
public import Papers.GraphicalZonotopes.GraphModels
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The endpoint-corrected path-join polynomial

The parameter `n` means that the path has `n+2` vertices. Thus every path
length in Appendix B is included. The ambient vertex set has `n+4`
vertices, with hubs 0,1 and path vertices 2,...,n+3.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

abbrev Vertex (n : ℕ) := Fin (n+4)
def hubA (n : ℕ) : Vertex n := ⟨0,by omega⟩
def hubB (n : ℕ) : Vertex n := ⟨1,by omega⟩
def vertex {n : ℕ} (i : Fin (n+2)) : Vertex n := ⟨i.val+2,by omega⟩

@[simp] theorem hubA_ne_hubB (n : ℕ) : hubA n ≠ hubB n := by
  simp [hubA,hubB,Fin.ext_iff]
@[simp] theorem hubB_ne_hubA (n : ℕ) : hubB n ≠ hubA n := Ne.symm (hubA_ne_hubB n)
@[simp] theorem vertex_ne_hubA {n : ℕ} (i : Fin (n+2)) : vertex i ≠ hubA n := by
  intro h
  have hv := congrArg Fin.val h
  change i.val+2=0 at hv
  omega
@[simp] theorem vertex_ne_hubB {n : ℕ} (i : Fin (n+2)) : vertex i ≠ hubB n := by
  simp [vertex,hubB,Fin.ext_iff]
@[simp] theorem hubA_ne_vertex {n : ℕ} (i : Fin (n+2)) : hubA n ≠ vertex i :=
  Ne.symm (vertex_ne_hubA i)
@[simp] theorem hubB_ne_vertex {n : ℕ} (i : Fin (n+2)) : hubB n ≠ vertex i :=
  Ne.symm (vertex_ne_hubB i)
@[simp] theorem vertex_inj {n : ℕ} {i j : Fin (n+2)} : vertex i=vertex j ↔ i=j := by
  simp [vertex,Fin.ext_iff]
@[simp] theorem vertex_left_ne_right {n : ℕ} (i : Fin (n+1)) :
    vertex i.castSucc ≠ vertex i.succ := by simp [vertex,Fin.ext_iff]
@[simp] theorem vertex_right_ne_left {n : ℕ} (i : Fin (n+1)) :
    vertex i.succ ≠ vertex i.castSucc := Ne.symm (vertex_left_ne_right i)

theorem vertex_cases {n : ℕ} (v : Vertex n) :
    v=hubA n ∨ v=hubB n ∨ ∃ i : Fin (n+2),v=vertex i := by
  by_cases ha : v.val=0
  · exact Or.inl (Fin.ext ha)
  by_cases hb : v.val=1
  · exact Or.inr (Or.inl (Fin.ext hb))
  refine Or.inr (Or.inr ⟨⟨v.val-2,by omega⟩,?_⟩)
  apply Fin.ext
  simp only [vertex]
  omega

/-- The literal graph K₂ * P_(n+2), with its labelled hubs and path. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj u v := u≠v ∧ (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1,by tauto⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (n : ℕ) : DecidableRel (graph n).Adj := fun u v =>
  inferInstanceAs (Decidable (u≠v ∧
    (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)))

@[simp] theorem graph_hubA {n : ℕ} {v : Vertex n} :
    (graph n).Adj (hubA n) v ↔ hubA n≠v := by simp [graph,hubA]
@[simp] theorem graph_hubB {n : ℕ} {v : Vertex n} :
    (graph n).Adj (hubB n) v ↔ hubB n≠v := by simp [graph,hubB]
@[simp] theorem graph_vertices {n : ℕ} (i j : Fin (n+2)) :
    (graph n).Adj (vertex i) (vertex j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  change (vertex i≠vertex j ∧
    (i.val+2<2 ∨ j.val+2<2 ∨ i.val+2+1=j.val+2 ∨ j.val+2+1=i.val+2)) ↔ _
  rw [Ne,vertex_inj]
  simp only [Fin.ext_iff]
  omega

/-- Every clique of cardinality at least two has exactly one of these
coordinate shapes: the hub edge, a spoke/hub triangle, or a path edge
with any subset of its two hubs. -/
abbrev Slot (n : ℕ) := Unit ⊕ (Fin 3 × Fin (n+2)) ⊕ (Fin 4 × Fin (n+1))

def clique {n : ℕ} : Slot n → Finset (Vertex n)
  | .inl _ => {hubA n,hubB n}
  | .inr (.inl (r,i)) =>
    if r=0 then {hubA n,vertex i}
    else if r=1 then {hubB n,vertex i}
    else {hubA n,hubB n,vertex i}
  | .inr (.inr (r,i)) =>
    if r=0 then {vertex i.castSucc,vertex i.succ}
    else if r=1 then {hubA n,vertex i.castSucc,vertex i.succ}
    else if r=2 then {hubB n,vertex i.castSucc,vertex i.succ}
    else {hubA n,hubB n,vertex i.castSucc,vertex i.succ}

theorem clique_card_ge_two {n : ℕ} (i : Slot n) : 2≤(clique i).card := by
  rcases i with u | ⟨r,i⟩ | ⟨r,i⟩
  · simp [clique]
  · fin_cases r <;> simp [clique]
  · fin_cases r <;> simp [clique,Finset.card_pair (vertex_left_ne_right i)]

theorem clique_isClique {n : ℕ} (i : Slot n) : (graph n).IsClique (clique i) := by
  have insA {S : Finset (Vertex n)} (h : (graph n).IsClique S) :
      (graph n).IsClique (insert (hubA n) S : Finset (Vertex n)) := by
    simpa only [Finset.coe_insert] using
      h.insert (fun v hv hav => graph_hubA.mpr hav)
  have insB {S : Finset (Vertex n)} (h : (graph n).IsClique S) :
      (graph n).IsClique (insert (hubB n) S : Finset (Vertex n)) := by
    simpa only [Finset.coe_insert] using
      h.insert (fun v hv hbv => graph_hubB.mpr hbv)
  have one (v : Vertex n) : (graph n).IsClique ({v} : Finset (Vertex n)) := by
    simpa only [Finset.coe_singleton] using (graph n).isClique_singleton v
  have pair (j : Fin (n+1)) :
      (graph n).IsClique ({vertex j.castSucc,vertex j.succ} : Finset (Vertex n)) := by
    rw [Finset.coe_pair,SimpleGraph.isClique_pair]
    intro hj
    apply (graph_vertices _ _).mpr
    exact Or.inl rfl
  rcases i with w | ⟨r,i⟩ | ⟨r,i⟩
  · exact insA (one (hubB n))
  · fin_cases r
    · exact insA (one (vertex i))
    · exact insB (one (vertex i))
    · exact insA (insB (one (vertex i)))
  · fin_cases r
    · exact pair i
    · exact insA (pair i)
    · exact insB (pair i)
    · exact insA (insB (pair i))

def coefficient (n : ℕ) : Slot n → ℝ
  | .inl _ => ((n+2)/2 : ℕ)
  | .inr (.inl (r,i)) =>
    if r=0 then 1
    else if r=1 then (if i=0 then 0 else 1)
    else if i=0 then 0 else -1
  | .inr (.inr (r,i)) =>
    if r=0 then 1
    else if r=1 then (if i.val%2=0 then -1 else 0)
    else if r=2 then (if i.val%2=0 then 0 else -1)
    else 1

def setFunction (n : ℕ) : SetFunction (Vertex n) :=
  FiniteMonomial.polynomial clique (coefficient n)

theorem normalized (n : ℕ) : TranslationNormalized (setFunction n) :=
  FiniteMonomial.polynomial_normalized clique clique_card_ge_two _

theorem graphical (n : ℕ) : Graphical (graph n) (setFunction n) :=
  FiniteMonomial.polynomial_graphical clique clique_isClique _

end GraphicalZonotopes.PathJoin
